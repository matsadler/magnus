use std::ops::Deref;

use crate::{
    r_basic::RBasic,
    ruby_sys::{rb_float_new, rb_float_value, ruby_value_type, VALUE},
    value::{Flonum, Value},
};

#[repr(transparent)]
pub struct RFloat(pub(crate) VALUE);

impl RFloat {
    /// # Safety
    ///
    /// val must not have been GC'd, return value must be kept on stack or
    /// otherwise protected from the GC.
    pub unsafe fn from_value(val: &Value) -> Option<Self> {
        let r_basic = RBasic::from_value(val)?;
        (r_basic.builtin_type() == ruby_value_type::RUBY_T_FLOAT).then(|| Self(val.into_inner()))
    }

    pub fn from_f64(n: f64) -> Result<Self, Flonum> {
        unsafe {
            let val = Value::new(rb_float_new(n));
            Self::from_value(&val).ok_or_else(|| {
                Flonum::from_value(&val).expect("f64 should convert to flonum or float")
            })
        }
    }

    /// # Safety
    ///
    /// self must not have been GC'd.
    pub unsafe fn to_f64(&self) -> f64 {
        rb_float_value(self.into_inner())
    }
}

impl Deref for RFloat {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        let self_ptr = self as *const Self;
        let value_ptr = self_ptr as *const Self::Target;
        // we just got this pointer from &self, so we know it's valid to deref
        unsafe { &*value_ptr }
    }
}

impl From<RFloat> for Value {
    fn from(val: RFloat) -> Self {
        *val
    }
}
