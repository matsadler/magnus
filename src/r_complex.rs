use std::ops::Deref;

use crate::{
    r_basic::RBasic,
    ruby_sys::{ruby_value_type, VALUE},
    value::Value,
};

#[repr(transparent)]
pub struct RComplex(VALUE);

impl RComplex {
    /// # Safety
    ///
    /// val must not have been GC'd, return value must be kept on stack or
    /// otherwise protected from the GC.
    pub unsafe fn from_value(val: &Value) -> Option<Self> {
        let r_basic = RBasic::from_value(val)?;
        (r_basic.builtin_type() == ruby_value_type::RUBY_T_COMPLEX).then(|| Self(val.into_inner()))
    }
}

impl Deref for RComplex {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        let self_ptr = self as *const Self;
        let value_ptr = self_ptr as *const Self::Target;
        // we just got this pointer from &self, so we know it's valid to deref
        unsafe { &*value_ptr }
    }
}
