use std::{fmt, ops::Deref, os::raw::c_int};

use crate::{
    error::{protect, Error},
    module::Module,
    object::Object,
    ruby_sys::{self, rb_class_new_instance, ruby_value_type, VALUE},
    try_convert::{ArgList, TryConvert},
    value::{NonZeroValue, Value},
};

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RClass(NonZeroValue);

impl RClass {
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            (val.rb_type() == ruby_value_type::RUBY_T_CLASS)
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        Self(NonZeroValue::new_unchecked(Value::new(val)))
    }

    pub fn new_instance<T>(self, args: T) -> Result<Value, Error>
    where
        T: ArgList,
    {
        let args = args.into_arg_list();
        let slice = args.as_ref();
        unsafe {
            protect(|| {
                Value::new(rb_class_new_instance(
                    slice.len() as c_int,
                    slice.as_ptr() as *const VALUE,
                    self.as_rb_value(),
                ))
            })
        }
    }
}

impl Default for RClass {
    fn default() -> Self {
        unsafe { RClass::from_rb_value_unchecked(ruby_sys::rb_cObject) }
    }
}

impl Deref for RClass {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
    }
}

impl fmt::Display for RClass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for RClass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl From<RClass> for Value {
    fn from(val: RClass) -> Self {
        *val
    }
}

impl Object for RClass {}
impl Module for RClass {}

impl TryConvert for RClass {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        match Self::from_value(*val) {
            Some(v) => Ok(v),
            None => Err(Error::type_error(format!(
                "no implicit conversion of {} into Class",
                unsafe { val.classname() },
            ))),
        }
    }
}
