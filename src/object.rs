use std::{ffi::CString, mem::transmute, ops::Deref};

use crate::ruby_sys::{rb_define_singleton_method, rb_ivar_get, rb_ivar_set, rb_singleton_class};

use crate::{
    class::RClass,
    debug_assert_value,
    error::{protect, Error},
    method::Method,
    try_convert::TryConvert,
    value::{Id, Value},
};

/// Functions available all non-immediate values.
pub trait Object: Deref<Target = Value> + Copy {
    /// Define a singleton method in `self`'s scope.
    ///
    /// Singleton methods defined on a class are Ruby's method for implementing
    /// 'class' methods.
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

    /// Get the value for the instance variable `name` within `self`'s scope.
    ///
    /// Note, the `@` is part of the name.
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

    /// Set the value for the instance variable `name` within `self`'s scope.
    ///
    /// Note, the `@` is part of the name.
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

    /// Finds or creates the singleton class of `self`.
    ///
    /// Returns `Err` if `self` can not have a singleton class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Object, RString};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(RString::new("example").singleton_class().is_ok());
    /// ```
    fn singleton_class(self) -> Result<RClass, Error> {
        protect(|| unsafe {
            RClass::from_rb_value_unchecked(rb_singleton_class(self.as_rb_value()))
        })
    }
}
