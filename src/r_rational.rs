use std::{fmt, ops::Deref};

use crate::{
    error::Error,
    ruby_sys::ruby_value_type,
    try_convert::TryConvert,
    value::{NonZeroValue, Value},
};

/// A Value pointer to a RRational struct, Ruby's internal representation of
/// rational numbers.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RRational(NonZeroValue);

impl RRational {
    /// Return `Some(RRational)` if `val` is a `RRational`, `None` otherwise.
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            (val.rb_type() == ruby_value_type::RUBY_T_RATIONAL)
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }
}

impl Deref for RRational {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
    }
}

impl fmt::Display for RRational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for RRational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl From<RRational> for Value {
    fn from(val: RRational) -> Self {
        *val
    }
}

impl TryConvert for RRational {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        Self::from_value(*val).ok_or_else(|| {
            Error::type_error(format!(
                "no implicit conversion of {} into Rational",
                unsafe { val.classname() },
            ))
        })
    }
}
