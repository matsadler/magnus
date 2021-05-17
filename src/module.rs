use std::{ffi::CString, mem::transmute, ops::Deref};

use crate::{
    debug_assert_value,
    method::Method,
    object::Object,
    protect,
    r_class::RClass,
    r_module::RModule,
    ruby_sys::{
        rb_const_get, rb_define_class_under, rb_define_method, rb_define_module_under,
        rb_define_private_method, rb_define_protected_method,
    },
    value::{Symbol, Value},
    ProtectState,
};

pub trait Module: Object + Deref<Target = Value> {
    fn define_class(&self, name: &str, superclass: RClass) -> Result<RClass, ProtectState> {
        debug_assert_value!(self);
        debug_assert_value!(superclass);
        let name = CString::new(name).unwrap();
        let superclass = superclass.into_inner();
        unsafe {
            let res = protect(|| {
                Value::new(rb_define_class_under(
                    self.into_inner(),
                    name.as_ptr(),
                    superclass,
                ))
            });
            res.map(|v| RClass::from_value(&v).unwrap())
        }
    }

    fn define_module(&self, name: &str) -> Result<RModule, ProtectState> {
        let name = CString::new(name).unwrap();
        unsafe {
            let res =
                protect(|| Value::new(rb_define_module_under(self.into_inner(), name.as_ptr())));
            res.map(|v| RModule::from_value(&v).unwrap())
        }
    }

    fn const_get<S: Into<Symbol>>(&self, name: S) -> Result<Value, ProtectState> {
        debug_assert_value!(self);
        let id = name.into().to_id();
        unsafe { protect(|| Value::new(rb_const_get(self.into_inner(), id.into_inner()))) }
    }

    fn define_method<M>(&self, name: &str, func: M)
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

    fn define_private_method<M>(&self, name: &str, func: M)
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

    fn define_protected_method<M>(&self, name: &str, func: M)
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
