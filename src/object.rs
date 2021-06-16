use std::{ffi::CString, mem::transmute, ops::Deref};

use crate::{
    debug_assert_value,
    error::{protect, Error},
    method::Method,
    ruby_sys::{rb_define_singleton_method, rb_ivar_get, rb_ivar_set},
    try_convert::TryConvert,
    value::{Id, Value},
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

    fn ivar_get<T, U>(self, name: T) -> Result<U, Error>
    where
        T: Into<Id>,
        U: TryConvert,
    {
        debug_assert_value!(self);
        let id = name.into();
        let res = unsafe { protect(|| Value::new(rb_ivar_get(self.as_rb_value(), id.as_rb_id()))) };
        res.and_then(|v| v.try_convert())
    }

    fn ivar_set<T, U>(self, name: T, value: U) -> Result<(), Error>
    where
        T: Into<Id>,
        U: Into<Value>,
    {
        debug_assert_value!(self);
        let id = name.into();
        let value = value.into();
        unsafe {
            protect(|| {
                Value::new(rb_ivar_set(
                    self.as_rb_value(),
                    id.as_rb_id(),
                    value.as_rb_value(),
                ))
            })
        }?;
        Ok(())
    }
}
