use std::{ffi::CString, mem::transmute, ops::Deref, ptr::NonNull};

use crate::{
    debug_assert_value,
    method::Method,
    r_basic::RBasic,
    ruby_sys::{
        self, rb_define_method, rb_define_private_method, rb_define_protected_method,
        rb_define_singleton_method, ruby_value_type, VALUE,
    },
    value::Value,
};

#[repr(transparent)]
pub struct RClass(VALUE);

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

    pub fn define_method<M>(&self, name: &str, func: M)
    where
        M: Method,
    {
        debug_assert_value!(self);
        let name = CString::new(name).unwrap();
        unsafe {
            rb_define_method(
                self.into_inner(),
                name.as_ptr(),
                transmute(func.as_ptr()),
                M::arity().into(),
            );
        }
    }

    pub fn define_singleton_method<M>(&self, name: &str, func: M)
    where
        M: Method,
    {
        debug_assert_value!(self);
        let name = CString::new(name).unwrap();
        unsafe {
            rb_define_singleton_method(
                self.into_inner(),
                name.as_ptr(),
                transmute(func.as_ptr()),
                M::arity().into(),
            );
        }
    }

    pub fn define_private_method<M>(&self, name: &str, func: M)
    where
        M: Method,
    {
        debug_assert_value!(self);
        let name = CString::new(name).unwrap();
        unsafe {
            rb_define_private_method(
                self.into_inner(),
                name.as_ptr(),
                transmute(func.as_ptr()),
                M::arity().into(),
            );
        }
    }

    pub fn define_protected_method<M>(&self, name: &str, func: M)
    where
        M: Method,
    {
        debug_assert_value!(self);
        let name = CString::new(name).unwrap();
        unsafe {
            rb_define_protected_method(
                self.into_inner(),
                name.as_ptr(),
                transmute(func.as_ptr()),
                M::arity().into(),
            );
        }
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
