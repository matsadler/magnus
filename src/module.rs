use std::{ffi::CString, mem::transmute, ops::Deref};

use crate::{
    debug_assert_value,
    error::{protect, Error},
    method::Method,
    object::Object,
    r_class::RClass,
    r_module::RModule,
    ruby_sys::{
        rb_const_get, rb_define_class_id_under, rb_define_method_id, rb_define_module_id_under,
        rb_define_private_method, rb_define_protected_method,
    },
    value::{Id, Value},
};

pub trait Module: Object + Deref<Target = Value> {
    fn define_class<T: Into<Id>>(&self, name: T, superclass: RClass) -> Result<RClass, Error> {
        debug_assert_value!(self);
        debug_assert_value!(superclass);
        let id = name.into();
        let superclass = superclass.into_inner();
        unsafe {
            let res = protect(|| {
                Value::new(rb_define_class_id_under(
                    self.into_inner(),
                    id.into_inner(),
                    superclass,
                ))
            });
            res.map(|v| RClass::from_value(&v).unwrap())
        }
    }

    fn define_module<T: Into<Id>>(&self, name: T) -> Result<RModule, Error> {
        let id = name.into();
        unsafe {
            let res = protect(|| {
                Value::new(rb_define_module_id_under(
                    self.into_inner(),
                    id.into_inner(),
                ))
            });
            res.map(|v| RModule::from_value(&v).unwrap())
        }
    }

    fn const_get<T: Into<Id>>(&self, name: T) -> Result<Value, Error> {
        debug_assert_value!(self);
        let id = name.into();
        unsafe { protect(|| Value::new(rb_const_get(self.into_inner(), id.into_inner()))) }
    }

    fn define_method<T, M>(&self, name: T, func: M)
    where
        T: Into<Id>,
        M: Method,
    {
        debug_assert_value!(self);
        let id = name.into();
        unsafe {
            rb_define_method_id(
                self.into_inner(),
                id.into_inner(),
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
