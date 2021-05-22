use std::{ops::Deref, ptr::NonNull};

use crate::{
    module::Module,
    object::Object,
    r_basic::RBasic,
    ruby_sys::{self, rb_class_inherited_p, ruby_value_type, VALUE},
    value::Value,
};

#[repr(transparent)]
pub struct RClass(pub(crate) VALUE);

impl RClass {
    /// # Safety
    ///
    /// val must not have been GC'd, return value must be kept on stack or
    /// otherwise protected from the GC.
    pub unsafe fn from_value(val: &Value) -> Option<Self> {
        let r_basic = RBasic::from_value(val)?;
        (r_basic.builtin_type() == ruby_value_type::RUBY_T_CLASS).then(|| Self(val.into_inner()))
    }

    // TODO: use or remove
    #[allow(dead_code)]
    pub(crate) fn as_internal(&self) -> NonNull<ruby_sys::RClass> {
        // safe as to get self we need to have gone through ::from_value()
        // where val is vaild as an RBasic, which rules out NULL
        unsafe { NonNull::new_unchecked(self.0 as *mut _) }
    }

    pub fn is_inherited(&self, other: RClass) -> bool {
        unsafe { Value::new(rb_class_inherited_p(self.into_inner(), other.into_inner())).to_bool() }
    }
}

impl Default for RClass {
    fn default() -> Self {
        unsafe { RClass(ruby_sys::rb_cObject) }
    }
}

impl Deref for RClass {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        let self_ptr = self as *const Self;
        let value_ptr = self_ptr as *const Self::Target;
        // we just got this pointer from &self, so we know it's valid to deref
        unsafe { &*value_ptr }
    }
}

impl Object for RClass {}
impl Module for RClass {}
