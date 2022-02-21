use std::{
    borrow::Cow,
    fmt,
    ops::Deref,
    os::raw::{c_char, c_long},
};

use crate::{
    debug_assert_value,
    error::{protect, Error},
    r_string::RString,
    ruby_sys::{rb_id2sym, rb_intern2, rb_sym2str, rb_to_symbol, ruby_value_type, VALUE},
    try_convert::TryConvert,
    value::{Id, NonZeroValue, StaticSymbol, Value},
};

/// A type wrapping either an immediate symbol value or a Value pointer to a
/// RSymbol struct.
///
/// All [`Value`] methods should be available on this type through [`Deref`],
/// but some may be missed by this documentation.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Symbol(NonZeroValue);

impl Symbol {
    /// Return `Some(RSymbol)` if `val` is a `RSymbol`, `None` otherwise.
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
    #[inline]
    pub fn new<T: AsRef<str>>(name: T) -> Self {
        name.as_ref().into()
    }

    /// Returns whether `self` is static or not.
    ///
    /// Static symbols won't be garbage collected, so should be safe to store
    /// on the heap. See [`StaticSymbol`].
    pub fn is_static(self) -> bool {
        self.is_static_symbol()
    }

    /// Return the symbol as a string. If the symbol is static this will be a
    /// `&str`, otherwise an owned `String`.
    ///
    /// May error if the name is not valid utf-8.
    pub fn name(self) -> Result<Cow<'static, str>, Error> {
        if let Some(sym) = StaticSymbol::from_value(*self) {
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
    pub fn as_static(self) -> Option<StaticSymbol> {
        StaticSymbol::from_value(*self)
    }

    /// If `self` is already static simply returns `self` as a
    /// [`StaticSymbol`]. If `self` is not static it will be made so and
    /// returned as a [`StaticSymbol`].
    ///
    /// Be aware that once static a symbol will never be garbage collected.
    pub fn to_static(self) -> StaticSymbol {
        if let Some(sym) = StaticSymbol::from_value(*self) {
            return sym;
        }
        unsafe {
            let name = RString::from_rb_value_unchecked(rb_sym2str(self.as_rb_value()));
            let slice = name.as_slice();
            let id = rb_intern2(slice.as_ptr() as *const c_char, slice.len() as c_long);
            StaticSymbol::from_value(Value::new(rb_id2sym(id))).unwrap()
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

impl From<Symbol> for Value {
    fn from(val: Symbol) -> Self {
        *val
    }
}

impl TryConvert for Symbol {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        Self::from_value(*val).ok_or_else(|| {
            Error::type_error(format!(
                "no implicit conversion of {} into Symbol",
                unsafe { val.classname() },
            ))
        })
    }
}
