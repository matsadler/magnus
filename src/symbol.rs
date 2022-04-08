use std::{borrow::Cow, fmt, ops::Deref};

use crate::{
    debug_assert_value,
    error::{protect, Error},
    exception,
    r_string::RString,
    ruby_sys::{
        rb_check_id, rb_id2sym, rb_intern_str, rb_sym2str, rb_to_symbol, ruby_value_type, VALUE,
    },
    try_convert::TryConvert,
    value::{private, Id, NonZeroValue, ReprValue, StaticSymbol, Value},
};

/// A type wrapping either a [`StaticSymbol`] or a Value pointer to a RSymbol
/// struct.
///
/// All [`Value`] methods should be available on this type through [`Deref`],
/// but some may be missed by this documentation.
#[derive(Clone, Copy)]
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
    #[inline]
    pub fn new<T: AsRef<str>>(name: T) -> Self {
        name.as_ref().into()
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
        if let Some(sym) = StaticSymbol::from_value(*self) {
            return sym;
        }
        unsafe {
            let name = rb_sym2str(self.as_rb_value());
            let id = rb_intern_str(name);
            StaticSymbol::from_rb_value_unchecked(rb_id2sym(id))
        }
    }
}

impl Deref for Symbol {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
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

impl From<Id> for Symbol {
    fn from(id: Id) -> Self {
        unsafe { Self::from_rb_value_unchecked(rb_id2sym(id.as_rb_id())) }
    }
}

impl From<&str> for Symbol {
    fn from(s: &str) -> Self {
        unsafe {
            protect(|| Value::new(rb_to_symbol(RString::new(s).as_rb_value())))
                .map(|v| Self::from_rb_value_unchecked(v.as_rb_value()))
                .unwrap()
        }
    }
}

impl From<String> for Symbol {
    fn from(s: String) -> Self {
        s.as_str().into()
    }
}

impl From<StaticSymbol> for Symbol {
    fn from(s: StaticSymbol) -> Self {
        unsafe { Self(NonZeroValue::new_unchecked(s.into())) }
    }
}

impl From<Symbol> for Value {
    fn from(val: Symbol) -> Self {
        *val
    }
}

unsafe impl private::ReprValue for Symbol {
    fn to_value(self) -> Value {
        *self
    }

    unsafe fn from_value_unchecked(val: Value) -> Self {
        Self(NonZeroValue::new_unchecked(val))
    }
}

impl ReprValue for Symbol {}

impl TryConvert for Symbol {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        Self::from_value(*val).ok_or_else(|| {
            Error::new(
                exception::type_error(),
                format!("no implicit conversion of {} into Symbol", unsafe {
                    val.classname()
                },),
            )
        })
    }
}
