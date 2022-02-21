use std::{fmt, ops::Deref};

use crate::{
    error::Error,
    ruby_sys::ruby_value_type,
    try_convert::TryConvert,
    value::{NonZeroValue, Value},
};

/// A Value pointer to a RComplex struct, Ruby's internal representation of
/// complex numbers.
///
/// All [`Value`] methods should be available on this type through [`Deref`],
/// but some may be missed by this documentation.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RComplex(NonZeroValue);

impl RComplex {
    /// Return `Some(RComplex)` if `val` is a `RComplex`, `None` otherwise.
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            (val.rb_type() == ruby_value_type::RUBY_T_COMPLEX)
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }
}

impl Deref for RComplex {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
    }
}

impl fmt::Display for RComplex {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for RComplex {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl From<RComplex> for Value {
    fn from(val: RComplex) -> Self {
        *val
    }
}

impl TryConvert for RComplex {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        Self::from_value(*val).ok_or_else(|| {
            Error::type_error(format!(
                "no implicit conversion of {} into Complex",
                unsafe { val.classname() },
            ))
        })
    }
}
