use std::{ffi::CString, mem::transmute, ops::Deref};

use crate::{
    debug_assert_value, method::Method, ruby_sys::rb_define_singleton_method, value::Value,
};

pub trait Object: Deref<Target = Value> + Copy {
    fn define_singleton_method<M>(self, name: &str, func: M)
    where
        M: Method,
    {
        debug_assert_value!(self);
        let name = CString::new(name).unwrap();
        unsafe {
            rb_define_singleton_method(
                self.as_rb_value(),
                name.as_ptr(),
                transmute(func.as_ptr()),
                M::arity().into(),
            );
        }
    }
}
