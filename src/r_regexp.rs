use std::{fmt, ops::Deref};

use crate::ruby_sys::ruby_value_type;

use crate::{
    encoding::EncodingCapable,
    error::Error,
    exception,
    try_convert::TryConvert,
    value::{private, NonZeroValue, ReprValue, Value},
};

/// A Value pointer to a RRegexp struct, Ruby's internal representation of
/// regular expressions.
///
/// All [`Value`] methods should be available on this type through [`Deref`],
/// but some may be missed by this documentation.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RRegexp(NonZeroValue);

impl RRegexp {
    /// Return `Some(RRegexp)` if `val` is a `RRegexp`, `None` otherwise.
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            (val.rb_type() == ruby_value_type::RUBY_T_REGEXP)
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }
}

impl Deref for RRegexp {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
    }
}

impl fmt::Display for RRegexp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for RRegexp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl EncodingCapable for RRegexp {}

impl From<RRegexp> for Value {
    fn from(val: RRegexp) -> Self {
        *val
    }
}

unsafe impl private::ReprValue for RRegexp {
    fn to_value(self) -> Value {
        *self
    }

    unsafe fn from_value_unchecked(val: Value) -> Self {
        Self(NonZeroValue::new_unchecked(val))
    }
}

impl ReprValue for RRegexp {}

impl TryConvert for RRegexp {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        Self::from_value(*val).ok_or_else(|| {
            Error::new(
                exception::type_error(),
                format!("no implicit conversion of {} into Regexp", unsafe {
                    val.classname()
                },),
            )
        })
    }
}
