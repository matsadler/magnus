use std::{ffi::CString, fmt, mem::transmute, ops::Deref};

use crate::{
    debug_assert_value,
    error::Error,
    method::Method,
    module::Module,
    object::Object,
    ruby_sys::{rb_define_module_function, ruby_value_type},
    try_convert::TryConvert,
    value::{NonZeroValue, Value},
};

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RModule(NonZeroValue);

impl RModule {
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            (val.rb_type() == ruby_value_type::RUBY_T_MODULE)
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    pub fn define_module_function<M>(self, name: &str, func: M)
    where
        M: Method,
    {
        debug_assert_value!(self);
        let name = CString::new(name).unwrap();
        unsafe {
            rb_define_module_function(
                self.as_rb_value(),
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
        self.0.get_ref()
    }
}

impl fmt::Display for RModule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for RModule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl From<RModule> for Value {
    fn from(val: RModule) -> Self {
        *val
    }
}

impl Object for RModule {}
impl Module for RModule {}

impl TryConvert for RModule {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        Self::from_value(*val).ok_or_else(|| {
            Error::type_error(format!(
                "no implicit conversion of {} into Module",
                unsafe { val.classname() },
            ))
        })
    }
}
