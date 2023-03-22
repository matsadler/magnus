//! Types and traits for working with Ruby symbols.

use std::{borrow::Cow, fmt};

use rb_sys::{rb_check_id, rb_intern_str, rb_sym2str, rb_to_symbol, ruby_value_type, VALUE};

use crate::{
    encoding::EncodingCapable,
    error::{protect, Error},
    into_value::IntoValue,
    r_string::RString,
    try_convert::TryConvert,
    value::{
        private::{self, ReprValue as _},
        Id, LazyId, NonZeroValue, OpaqueId, ReprValue, StaticSymbol, Value,
    },
    Ruby,
};

#[allow(missing_docs)]
impl Ruby {
    #[inline]
    pub fn to_symbol<T: AsRef<str>>(&self, name: T) -> Symbol {
        name.as_ref().into_symbol_with(self)
    }
}

/// A type wrapping either a [`StaticSymbol`] or a Value pointer to a RSymbol
/// struct.
///
/// See the [`ReprValue`] trait for additional methods available on this type.
#[derive(Clone, Copy, Eq, PartialEq)]
#[repr(transparent)]
pub struct Symbol(NonZeroValue);

impl Symbol {
    /// Return `Some(Symbol)` if `val` is a `Symbol`, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Symbol};
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
        Self(NonZeroValue::new_unchecked(Value::new(val)))
    }

    /// Create a new `Symbol` from `name`.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Symbol};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let sym = Symbol::new("example");
    /// let result: bool = eval!(":example == sym", sym).unwrap();
    /// assert!(result);
    /// ```
    #[cfg(feature = "friendly-api")]
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
    /// use magnus::{eval, Symbol};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(eval::<Symbol>(":foo").unwrap().is_static());
    /// assert!(!Symbol::new("bar").is_static());
    /// assert!(!eval::<Symbol>(r#""baz".to_sym"#).unwrap().is_static());
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
    /// use magnus::Symbol;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let sym = Symbol::new("example");
    /// assert_eq!(sym.name().unwrap(), "example");
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
    /// use magnus::{eval, Symbol};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(eval::<Symbol>(":foo").unwrap().as_static().is_some());
    /// assert!(Symbol::new("bar").as_static().is_none());
    /// assert!(eval::<Symbol>(r#""baz".to_sym"#).unwrap().as_static().is_none());
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
    /// use magnus::{eval, Symbol};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let sym = Symbol::new("example");
    /// let static_sym = sym.to_static();
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
    /// Panics if called from a non-Ruby thread.
    #[cfg(feature = "friendly-api")]
    #[inline]
    fn into_symbol(self) -> Symbol {
        self.into_symbol_with(&get_ruby!())
    }

    /// Convert `self` into [`Symbol`].
    ///
    /// # Safety
    ///
    /// This method should only be called from a Ruby thread.
    unsafe fn into_symbol_unchecked(self) -> Symbol {
        self.into_symbol_with(&Ruby::get_unchecked())
    }

    /// Convert `self` into [`Symbol`].
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
        unsafe { id.into_symbol_unchecked() }
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
