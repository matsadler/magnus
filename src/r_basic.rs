use std::{ops::Deref, ptr::NonNull};

use crate::{
    r_class::RClass,
    ruby_sys::{self, ruby_special_consts, ruby_value_type, VALUE},
    value::Value,
};

#[repr(transparent)]
pub struct RBasic(VALUE);

impl RBasic {
    pub(crate) fn from_value(val: &Value) -> Option<Self> {
        let value_p = val.into_inner();
        let immediate_p = value_p & ruby_special_consts::RUBY_IMMEDIATE_MASK as VALUE != 0;
        let test = value_p & !(ruby_special_consts::RUBY_Qnil as VALUE) != 0;
        let special_const_p = immediate_p || !test;
        (!special_const_p).then(|| Self(value_p))
    }

    pub(crate) fn as_internal(&self) -> NonNull<ruby_sys::RBasic> {
        // Ruby uses a VALUE of 0 for `false`. The `test` check in
        // ::from_value() rules out false (and nil), so we know we don't have a
        // 0 (aka NULL as a pointer), so NonNull::new_unchecked is safe
        unsafe { NonNull::new_unchecked(self.0 as *mut _) }
    }

    // derefs a raw pointer that under GC compaction may be outside the
    // process's memory space if the Value has been allowed to get GC'd
    pub(crate) unsafe fn builtin_type(&self) -> ruby_value_type {
        let ret = self.as_internal().as_ref().flags & (ruby_value_type::RUBY_T_MASK as VALUE);
        // this bit is safe, ruby_value_type is #[repr(u32)], the flags value
        // set by Ruby, and Ruby promises that flags masked like this will
        // always be a valid entry in this enum
        std::mem::transmute(ret as u32)
    }

    pub(crate) unsafe fn class(&self) -> RClass {
        RClass(self.as_internal().as_ref().klass)
    }
}

impl Deref for RBasic {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        let self_ptr = self as *const Self;
        let value_ptr = self_ptr as *const Self::Target;
        // we just got this pointer from &self, so we know it's valid to deref
        unsafe { &*value_ptr }
    }
}
