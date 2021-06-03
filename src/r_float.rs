use std::{fmt, ops::Deref};

use crate::{
    debug_assert_value,
    ruby_sys::{rb_float_new, rb_float_value, ruby_value_type},
    value::{Flonum, NonZeroValue, Value},
};

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RFloat(NonZeroValue);

impl RFloat {
    /// # Safety
    ///
    /// val must not have been GC'd, return value must be kept on stack or
    /// otherwise protected from the GC.
    pub unsafe fn from_value(val: Value) -> Option<Self> {
        (val.rb_type() == ruby_value_type::RUBY_T_FLOAT)
            .then(|| Self(NonZeroValue::new_unchecked(val)))
    }

    pub fn from_f64(n: f64) -> Result<Self, Flonum> {
        unsafe {
            let val = Value::new(rb_float_new(n));
            Self::from_value(val).ok_or_else(|| {
                Flonum::from_value(val).expect("f64 should convert to flonum or float")
            })
        }
    }

    /// # Safety
    ///
    /// self must not have been GC'd.
    pub unsafe fn to_f64(self) -> f64 {
        debug_assert_value!(self);
        rb_float_value(self.as_rb_value())
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
        write!(f, "{}", unsafe { self.inspect() })
    }
}

impl From<RFloat> for Value {
    fn from(val: RFloat) -> Self {
        *val
    }
}
