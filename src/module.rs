use std::{ffi::CString, mem::transmute, ops::Deref};

use crate::{
    debug_assert_value,
    error::{protect, Error},
    method::Method,
    object::Object,
    r_class::RClass,
    r_module::RModule,
    ruby_sys::{
        rb_class_inherited_p, rb_const_get, rb_define_class_id_under, rb_define_method_id,
        rb_define_module_id_under, rb_define_private_method, rb_define_protected_method,
    },
    value::{Id, Value},
};

pub trait Module: Object + Deref<Target = Value> + Copy {
    fn define_class<T: Into<Id>>(self, name: T, superclass: RClass) -> Result<RClass, Error> {
        debug_assert_value!(self);
        debug_assert_value!(superclass);
        let id = name.into();
        let superclass = superclass.as_rb_value();
        unsafe {
            let res = protect(|| {
                Value::new(rb_define_class_id_under(
                    self.as_rb_value(),
                    id.as_rb_id(),
                    superclass,
                ))
            });
            res.map(|v| RClass::from_value(v).unwrap())
        }
    }

    fn define_module<T: Into<Id>>(self, name: T) -> Result<RModule, Error> {
        let id = name.into();
        unsafe {
            let res = protect(|| {
                Value::new(rb_define_module_id_under(self.as_rb_value(), id.as_rb_id()))
            });
            res.map(|v| RModule::from_value(v).unwrap())
        }
    }

    fn const_get<T: Into<Id>>(self, name: T) -> Result<Value, Error> {
        debug_assert_value!(self);
        let id = name.into();
        unsafe { protect(|| Value::new(rb_const_get(self.as_rb_value(), id.as_rb_id()))) }
    }

    fn is_inherited<T>(self, other: T) -> bool
    where
        T: Deref<Target = Value> + Module,
    {
        unsafe {
            Value::new(rb_class_inherited_p(
                self.as_rb_value(),
                other.as_rb_value(),
            ))
            .to_bool()
        }
    }

    fn define_method<T, M>(self, name: T, func: M)
    where
        T: Into<Id>,
        M: Method,
    {
        debug_assert_value!(self);
        let id = name.into();
        unsafe {
            rb_define_method_id(
                self.as_rb_value(),
                id.as_rb_id(),
                transmute(func.as_ptr()),
                M::arity().into(),
            );
        }
    }

    fn define_private_method<M>(self, name: &str, func: M)
    where
        M: Method,
    {
        debug_assert_value!(self);
        let name = CString::new(name).unwrap();
        unsafe {
            rb_define_private_method(
                self.as_rb_value(),
                name.as_ptr(),
                transmute(func.as_ptr()),
                M::arity().into(),
            );
        }
    }

    fn define_protected_method<M>(self, name: &str, func: M)
    where
        M: Method,
    {
        debug_assert_value!(self);
        let name = CString::new(name).unwrap();
        unsafe {
            rb_define_protected_method(
                self.as_rb_value(),
                name.as_ptr(),
                transmute(func.as_ptr()),
                M::arity().into(),
            );
        }
    }
}
