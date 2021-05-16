use std::{ffi::CString, mem::transmute, ops::Deref};

use crate::{
    debug_assert_value,
    method::Method,
    r_basic::RBasic,
    ruby_sys::{
        rb_define_method, rb_define_module_function, rb_define_private_method,
        rb_define_protected_method, rb_define_singleton_method, ruby_value_type, VALUE,
    },
    value::Value,
};

#[repr(transparent)]
pub struct RModule(VALUE);

impl RModule {
    /// # Safety
    ///
    /// val must not have been GC'd, return value must be kept on stack or
    /// otherwise protected from the GC.
    pub unsafe fn from_value(val: &Value) -> Option<Self> {
        let r_basic = RBasic::from_value(val)?;
        (r_basic.builtin_type() == ruby_value_type::RUBY_T_MODULE).then(|| Self(val.into_inner()))
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

    pub fn define_module_function<M>(&self, name: &str, func: M)
    where
        M: Method,
    {
        debug_assert_value!(self);
        let name = CString::new(name).unwrap();
        unsafe {
            rb_define_module_function(
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

impl Deref for RModule {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        let self_ptr = self as *const Self;
        let value_ptr = self_ptr as *const Self::Target;
        // we just got this pointer from &self, so we know it's valid to deref
        unsafe { &*value_ptr }
    }
}
