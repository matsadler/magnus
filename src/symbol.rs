//! Types and traits for working with Ruby symbols.

use std::{borrow::Cow, fmt};

use rb_sys::{VALUE, rb_check_id, rb_intern_str, rb_sym2str, rb_to_symbol, ruby_value_type};

use crate::{
    Ruby,
    encoding::EncodingCapable,
    error::{Error, protect},
    into_value::IntoValue,
    r_string::RString,
    try_convert::TryConvert,
    value::{
        Id, LazyId, NonZeroValue, OpaqueId, ReprValue, StaticSymbol, Value,
        private::{self, ReprValue as _},
    },
};

/// # Symbol
///
/// Functions that can be used to create Ruby `Symbol`s.
///
/// See also the [`Symbol`] type.
impl Ruby {
    /// Create a new `Symbol` from `name`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby, rb_assert};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let sym = ruby.to_symbol("example");
    ///     rb_assert!(ruby, ":example == sym", sym);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn to_symbol<T: AsRef<str>>(&self, name: T) -> Symbol {
        name.as_ref().into_symbol_with(self)
    }
}

/// A type wrapping either a [`StaticSymbol`] or a Value pointer to a RSymbol
/// struct.
///
/// See the [`ReprValue`] trait for additional methods available on this type.
/// See [`Ruby`](Ruby#symbol) for methods to create a `Symbol`.
#[derive(Clone, Copy, Eq, PartialEq)]
#[repr(transparent)]
pub struct Symbol(NonZeroValue);

impl Symbol {
    /// Return `Some(Symbol)` if `val` is a `Symbol`, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Symbol, eval};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(Symbol::from_value(eval(":foo").unwrap()).is_some());
    /// assert!(Symbol::from_value(eval(r#""bar".to_sym"#).unwrap()).is_some());
    /// assert!(Symbol::from_value(eval(r#""baz""#).unwrap()).is_none());
    /// ```
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            if val.is_static_symbol() {
                return Some(Self(NonZeroValue::new_unchecked(val)));
            }
            debug_assert_value!(val);
            (val.rb_type() == ruby_value_type::RUBY_T_SYMBOL)
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        unsafe { Self(NonZeroValue::new_unchecked(Value::new(val))) }
    }

    /// Create a new `Symbol` from `name`.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread. See [`Ruby::to_symbol`] for
    /// the non-panicking version.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(deprecated)]
    /// use magnus::{Symbol, rb_assert};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let sym = Symbol::new("example");
    /// rb_assert!(":example == sym", sym);
    /// ```
    #[deprecated(note = "please use `Ruby::to_symbol` instead")]
    #[cfg(feature = "old-api")]
    #[cfg_attr(docsrs, doc(cfg(feature = "old-api")))]
    #[inline]
    pub fn new<T: AsRef<str>>(name: T) -> Self {
        get_ruby!().to_symbol(name)
    }

    /// Returns whether `self` is static or not.
    ///
    /// Static symbols won't be garbage collected, so should be safe to store
    /// on the heap. See [`StaticSymbol`].
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby, Symbol};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     assert!(ruby.eval::<Symbol>(":foo")?.is_static());
    ///     assert!(!ruby.to_symbol("bar").is_static());
    ///     assert!(!ruby.eval::<Symbol>(r#""baz".to_sym"#)?.is_static());
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn is_static(self) -> bool {
        if self.is_static_symbol() {
            return true;
        }
        let mut p = self.as_rb_value();
        unsafe { rb_check_id(&mut p as *mut _) != 0 }
    }

    /// Return the symbol as a string. If the symbol is static this will be a
    /// `&str`, otherwise an owned `String`.
    ///
    /// May error if the name is not valid utf-8.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let sym = ruby.to_symbol("example");
    ///     assert_eq!(sym.name()?, "example");
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn name(self) -> Result<Cow<'static, str>, Error> {
        if let Some(sym) = self.as_static() {
            return sym.name().map(Cow::from);
        }
        unsafe {
            RString::from_rb_value_unchecked(rb_sym2str(self.as_rb_value()))
                .to_string()
                .map(Cow::from)
        }
    }

    /// If `self` is static, returns `self` as a [`StaticSymbol`], otherwise
    /// returns `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby, Symbol};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     assert!(ruby.eval::<Symbol>(":foo")?.as_static().is_some());
    ///     assert!(ruby.to_symbol("bar").as_static().is_none());
    ///     assert!(
    ///         ruby.eval::<Symbol>(r#""baz".to_sym"#)?
    ///             .as_static()
    ///             .is_none()
    ///     );
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn as_static(self) -> Option<StaticSymbol> {
        self.is_static()
            .then(|| unsafe { StaticSymbol::from_rb_value_unchecked(self.as_rb_value()) })
    }

    /// If `self` is already static simply returns `self` as a
    /// [`StaticSymbol`]. If `self` is not static it will be made so and
    /// returned as a [`StaticSymbol`].
    ///
    /// Be aware that once static a symbol will never be garbage collected.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby, rb_assert};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let sym = ruby.to_symbol("example");
    ///     let static_sym = sym.to_static();
    ///     rb_assert!(ruby, "sym == static_sym", sym, static_sym);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn to_static(self) -> StaticSymbol {
        if let Some(sym) = StaticSymbol::from_value(self.as_value()) {
            return sym;
        }
        unsafe {
            let name = rb_sym2str(self.as_rb_value());
            Id::from_rb_id(rb_intern_str(name)).into()
        }
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl EncodingCapable for Symbol {}

/// Conversions from Rust types into [`Symbol`].
pub trait IntoSymbol: Sized {
    /// Convert `self` into [`Symbol`].
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread. See
    /// [`IntoSymbol::into_symbol_with`] for the non-panicking version.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(deprecated)]
    /// use magnus::{rb_assert, symbol::IntoSymbol};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let sym = "example".into_symbol();
    /// rb_assert!("sym == :example", sym);
    /// ```
    #[deprecated(note = "please use `IntoSymbol::into_symbol_with` instead")]
    #[cfg(feature = "old-api")]
    #[cfg_attr(docsrs, doc(cfg(feature = "old-api")))]
    #[inline]
    fn into_symbol(self) -> Symbol {
        self.into_symbol_with(&get_ruby!())
    }

    /// Convert `self` into [`Symbol`].
    ///
    /// # Safety
    ///
    /// This method should only be called from a Ruby thread.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, symbol::IntoSymbol};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// // only safe when called from a Ruby thread
    /// let sym = unsafe { "example".into_symbol_unchecked() };
    /// rb_assert!("sym == :example", sym);
    /// ```
    unsafe fn into_symbol_unchecked(self) -> Symbol {
        unsafe { self.into_symbol_with(&Ruby::get_unchecked()) }
    }

    /// Convert `self` into [`Symbol`].
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Ruby, rb_assert, symbol::IntoSymbol};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ruby = Ruby::get().unwrap();
    /// let sym = "example".into_symbol_with(&ruby);
    /// rb_assert!(ruby, "sym == :example", sym);
    /// ```
    fn into_symbol_with(self, handle: &Ruby) -> Symbol;
}

impl IntoSymbol for Symbol {
    fn into_symbol_with(self, _: &Ruby) -> Symbol {
        self
    }
}

impl IntoSymbol for Id {
    fn into_symbol_with(self, handle: &Ruby) -> Symbol {
        StaticSymbol::from(self).into_symbol_with(handle)
    }
}

impl From<Id> for Symbol {
    fn from(id: Id) -> Self {
        unsafe { id.into_symbol_with(&Ruby::get_unchecked()) }
    }
}

impl IntoSymbol for &str {
    fn into_symbol_with(self, handle: &Ruby) -> Symbol {
        protect(|| unsafe {
            Symbol::from_rb_value_unchecked(rb_to_symbol(handle.str_new(self).as_rb_value()))
        })
        .unwrap()
    }
}

impl IntoSymbol for String {
    fn into_symbol_with(self, handle: &Ruby) -> Symbol {
        self.as_str().into_symbol_with(handle)
    }
}

impl IntoSymbol for StaticSymbol {
    fn into_symbol_with(self, handle: &Ruby) -> Symbol {
        unsafe { Symbol(NonZeroValue::new_unchecked(self.into_value_with(handle))) }
    }
}

impl From<StaticSymbol> for Symbol {
    fn from(s: StaticSymbol) -> Self {
        s.into_symbol_with(&Ruby::get_with(s))
    }
}

impl IntoValue for Symbol {
    #[inline]
    fn into_value_with(self, _: &Ruby) -> Value {
        self.0.get()
    }
}

impl PartialEq<Id> for Symbol {
    fn eq(&self, other: &Id) -> bool {
        self.as_static().map(|s| s == *other).unwrap_or(false)
    }
}

impl PartialEq<OpaqueId> for Symbol {
    fn eq(&self, other: &OpaqueId) -> bool {
        self.as_static().map(|s| s == *other).unwrap_or(false)
    }
}

impl PartialEq<LazyId> for Symbol {
    /// # Panics
    ///
    /// Panics if the first call is from a non-Ruby thread. The `LazyId` will
    /// then be *poisoned* and all future use of it will panic.
    fn eq(&self, other: &LazyId) -> bool {
        self.as_static().map(|s| s == *other).unwrap_or(false)
    }
}

impl PartialEq<StaticSymbol> for Symbol {
    fn eq(&self, other: &StaticSymbol) -> bool {
        self.as_static().map(|s| s == *other).unwrap_or(false)
    }
}

unsafe impl private::ReprValue for Symbol {}

impl ReprValue for Symbol {}

impl TryConvert for Symbol {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Self::from_value(val).ok_or_else(|| {
            Error::new(
                Ruby::get_with(val).exception_type_error(),
                format!("no implicit conversion of {} into Symbol", unsafe {
                    val.classname()
                },),
            )
        })
    }
}
