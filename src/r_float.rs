use std::{fmt, ops::Deref};

use crate::{
    debug_assert_value,
    error::Error,
    float::Float,
    ruby_sys::{rb_float_new, rb_float_value, ruby_value_type, VALUE},
    try_convert::TryConvert,
    value::{Flonum, NonZeroValue, Value},
};

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RFloat(NonZeroValue);

impl RFloat {
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

    pub fn from_f64(n: f64) -> Result<Self, Flonum> {
        unsafe {
            let val = Value::new(rb_float_new(n));
            Self::from_value(val).ok_or_else(|| Flonum::from_rb_value_unchecked(val.as_rb_value()))
        }
    }

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

impl TryConvert for RFloat {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        let float = val.try_convert::<Float>()?;
        if let Some(rfloat) = RFloat::from_value(*float) {
            Ok(rfloat)
        } else {
            Err(Error::range_error("float in range for flonum"))
        }
    }
}
