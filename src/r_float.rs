use std::{fmt, ops::Deref};

use crate::{
    debug_assert_value,
    error::Error,
    exception,
    float::Float,
    ruby_sys::{rb_float_new, rb_float_value, ruby_value_type, VALUE},
    try_convert::TryConvert,
    value::{private, Flonum, NonZeroValue, ReprValue, Value},
};

/// A Value pointer to a RFloat struct, Ruby's internal representation of
/// high precision floating point numbers.
///
/// All [`Value`] methods should be available on this type through [`Deref`],
/// but some may be missed by this documentation.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RFloat(NonZeroValue);

impl RFloat {
    /// Return `Some(RFloat)` if `val` is a `RFloat`, `None` otherwise.
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            (val.rb_type() == ruby_value_type::RUBY_T_FLOAT)
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        Self(NonZeroValue::new_unchecked(Value::new(val)))
    }

    /// Create a new `RFloat` from an `f64.`
    ///
    /// Returns `Ok(RFloat)` if `n` requires a high precision float, otherwise
    /// returns `Err(Fixnum)`.
    pub fn from_f64(n: f64) -> Result<Self, Flonum> {
        unsafe {
            let val = Value::new(rb_float_new(n));
            Self::from_value(val).ok_or_else(|| Flonum::from_rb_value_unchecked(val.as_rb_value()))
        }
    }

    /// Convert `self` to a `f64`.
    pub fn to_f64(self) -> f64 {
        debug_assert_value!(self);
        unsafe { rb_float_value(self.as_rb_value()) }
    }
}

impl Deref for RFloat {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
    }
}

impl fmt::Display for RFloat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for RFloat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl From<RFloat> for Value {
    fn from(val: RFloat) -> Self {
        *val
    }
}

unsafe impl private::ReprValue for RFloat {
    fn to_value(self) -> Value {
        *self
    }

    unsafe fn from_value_unchecked(val: Value) -> Self {
        Self(NonZeroValue::new_unchecked(val))
    }
}

impl ReprValue for RFloat {}

impl TryConvert for RFloat {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        let float = val.try_convert::<Float>()?;
        if let Some(rfloat) = RFloat::from_value(*float) {
            Ok(rfloat)
        } else {
            Err(Error::new(
                exception::range_error(),
                "float in range for flonum",
            ))
        }
    }
}
