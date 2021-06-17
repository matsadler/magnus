use std::{ffi::CString, fmt, ops::Deref, os::raw::c_char, ptr::null};

use crate::{
    error::{protect, Error},
    object::Object,
    r_class::RClass,
    ruby_sys::{rb_struct_define, ruby_value_type},
    value::{NonZeroValue, Value},
};

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RStruct(NonZeroValue);

impl RStruct {
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            (val.rb_type() == ruby_value_type::RUBY_T_STRUCT)
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }
}

impl Deref for RStruct {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
    }
}

impl fmt::Display for RStruct {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for RStruct {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl From<RStruct> for Value {
    fn from(val: RStruct) -> Self {
        *val
    }
}

impl Object for RStruct {}

pub fn define_struct<T>(name: &str, members: T) -> Result<RClass, Error>
where
    T: StructMembers,
{
    members.define(name)
}

mod private {
    use super::*;

    pub trait StructMembers {
        fn define(self, name: &str) -> Result<RClass, Error>;
    }
}
use private::StructMembers;

impl StructMembers for (&str,) {
    fn define(self, name: &str) -> Result<RClass, Error> {
        let name = CString::new(name).unwrap();
        let arg0 = CString::new(self.0).unwrap();
        unsafe {
            protect(|| {
                Value::new(rb_struct_define(
                    name.as_ptr(),
                    arg0.as_ptr(),
                    null::<c_char>(),
                ))
            })
            .map(|v| RClass::from_rb_value_unchecked(v.as_rb_value()))
        }
    }
}

impl StructMembers for (&str, &str) {
    fn define(self, name: &str) -> Result<RClass, Error> {
        let name = CString::new(name).unwrap();
        let arg0 = CString::new(self.0).unwrap();
        let arg1 = CString::new(self.1).unwrap();
        unsafe {
            protect(|| {
                Value::new(rb_struct_define(
                    name.as_ptr(),
                    arg0.as_ptr(),
                    arg1.as_ptr(),
                    null::<c_char>(),
                ))
            })
            .map(|v| RClass::from_rb_value_unchecked(v.as_rb_value()))
        }
    }
}

impl StructMembers for (&str, &str, &str) {
    fn define(self, name: &str) -> Result<RClass, Error> {
        let name = CString::new(name).unwrap();
        let arg0 = CString::new(self.0).unwrap();
        let arg1 = CString::new(self.1).unwrap();
        let arg2 = CString::new(self.2).unwrap();
        unsafe {
            protect(|| {
                Value::new(rb_struct_define(
                    name.as_ptr(),
                    arg0.as_ptr(),
                    arg1.as_ptr(),
                    arg2.as_ptr(),
                    null::<c_char>(),
                ))
            })
            .map(|v| RClass::from_rb_value_unchecked(v.as_rb_value()))
        }
    }
}

impl StructMembers for (&str, &str, &str, &str) {
    fn define(self, name: &str) -> Result<RClass, Error> {
        let name = CString::new(name).unwrap();
        let arg0 = CString::new(self.0).unwrap();
        let arg1 = CString::new(self.1).unwrap();
        let arg2 = CString::new(self.2).unwrap();
        let arg3 = CString::new(self.3).unwrap();
        unsafe {
            protect(|| {
                Value::new(rb_struct_define(
                    name.as_ptr(),
                    arg0.as_ptr(),
                    arg1.as_ptr(),
                    arg2.as_ptr(),
                    arg3.as_ptr(),
                    null::<c_char>(),
                ))
            })
            .map(|v| RClass::from_rb_value_unchecked(v.as_rb_value()))
        }
    }
}

impl StructMembers for (&str, &str, &str, &str, &str) {
    fn define(self, name: &str) -> Result<RClass, Error> {
        let name = CString::new(name).unwrap();
        let arg0 = CString::new(self.0).unwrap();
        let arg1 = CString::new(self.1).unwrap();
        let arg2 = CString::new(self.2).unwrap();
        let arg3 = CString::new(self.3).unwrap();
        let arg4 = CString::new(self.4).unwrap();
        unsafe {
            protect(|| {
                Value::new(rb_struct_define(
                    name.as_ptr(),
                    arg0.as_ptr(),
                    arg1.as_ptr(),
                    arg2.as_ptr(),
                    arg3.as_ptr(),
                    arg4.as_ptr(),
                    null::<c_char>(),
                ))
            })
            .map(|v| RClass::from_rb_value_unchecked(v.as_rb_value()))
        }
    }
}

impl StructMembers for (&str, &str, &str, &str, &str, &str) {
    fn define(self, name: &str) -> Result<RClass, Error> {
        let name = CString::new(name).unwrap();
        let arg0 = CString::new(self.0).unwrap();
        let arg1 = CString::new(self.1).unwrap();
        let arg2 = CString::new(self.2).unwrap();
        let arg3 = CString::new(self.3).unwrap();
        let arg4 = CString::new(self.4).unwrap();
        let arg5 = CString::new(self.5).unwrap();
        unsafe {
            protect(|| {
                Value::new(rb_struct_define(
                    name.as_ptr(),
                    arg0.as_ptr(),
                    arg1.as_ptr(),
                    arg2.as_ptr(),
                    arg3.as_ptr(),
                    arg4.as_ptr(),
                    arg5.as_ptr(),
                    null::<c_char>(),
                ))
            })
            .map(|v| RClass::from_rb_value_unchecked(v.as_rb_value()))
        }
    }
}

impl StructMembers for (&str, &str, &str, &str, &str, &str, &str) {
    fn define(self, name: &str) -> Result<RClass, Error> {
        let name = CString::new(name).unwrap();
        let arg0 = CString::new(self.0).unwrap();
        let arg1 = CString::new(self.1).unwrap();
        let arg2 = CString::new(self.2).unwrap();
        let arg3 = CString::new(self.3).unwrap();
        let arg4 = CString::new(self.4).unwrap();
        let arg5 = CString::new(self.5).unwrap();
        let arg6 = CString::new(self.6).unwrap();
        unsafe {
            protect(|| {
                Value::new(rb_struct_define(
                    name.as_ptr(),
                    arg0.as_ptr(),
                    arg1.as_ptr(),
                    arg2.as_ptr(),
                    arg3.as_ptr(),
                    arg4.as_ptr(),
                    arg5.as_ptr(),
                    arg6.as_ptr(),
                    null::<c_char>(),
                ))
            })
            .map(|v| RClass::from_rb_value_unchecked(v.as_rb_value()))
        }
    }
}

impl StructMembers for (&str, &str, &str, &str, &str, &str, &str, &str) {
    fn define(self, name: &str) -> Result<RClass, Error> {
        let name = CString::new(name).unwrap();
        let arg0 = CString::new(self.0).unwrap();
        let arg1 = CString::new(self.1).unwrap();
        let arg2 = CString::new(self.2).unwrap();
        let arg3 = CString::new(self.3).unwrap();
        let arg4 = CString::new(self.4).unwrap();
        let arg5 = CString::new(self.5).unwrap();
        let arg6 = CString::new(self.6).unwrap();
        let arg7 = CString::new(self.7).unwrap();
        unsafe {
            protect(|| {
                Value::new(rb_struct_define(
                    name.as_ptr(),
                    arg0.as_ptr(),
                    arg1.as_ptr(),
                    arg2.as_ptr(),
                    arg3.as_ptr(),
                    arg4.as_ptr(),
                    arg5.as_ptr(),
                    arg6.as_ptr(),
                    arg7.as_ptr(),
                    null::<c_char>(),
                ))
            })
            .map(|v| RClass::from_rb_value_unchecked(v.as_rb_value()))
        }
    }
}

impl StructMembers for (&str, &str, &str, &str, &str, &str, &str, &str, &str) {
    fn define(self, name: &str) -> Result<RClass, Error> {
        let name = CString::new(name).unwrap();
        let arg0 = CString::new(self.0).unwrap();
        let arg1 = CString::new(self.1).unwrap();
        let arg2 = CString::new(self.2).unwrap();
        let arg3 = CString::new(self.3).unwrap();
        let arg4 = CString::new(self.4).unwrap();
        let arg5 = CString::new(self.5).unwrap();
        let arg6 = CString::new(self.6).unwrap();
        let arg7 = CString::new(self.7).unwrap();
        let arg8 = CString::new(self.8).unwrap();
        unsafe {
            protect(|| {
                Value::new(rb_struct_define(
                    name.as_ptr(),
                    arg0.as_ptr(),
                    arg1.as_ptr(),
                    arg2.as_ptr(),
                    arg3.as_ptr(),
                    arg4.as_ptr(),
                    arg5.as_ptr(),
                    arg6.as_ptr(),
                    arg7.as_ptr(),
                    arg8.as_ptr(),
                    null::<c_char>(),
                ))
            })
            .map(|v| RClass::from_rb_value_unchecked(v.as_rb_value()))
        }
    }
}

impl StructMembers for (&str, &str, &str, &str, &str, &str, &str, &str, &str, &str) {
    fn define(self, name: &str) -> Result<RClass, Error> {
        let name = CString::new(name).unwrap();
        let arg0 = CString::new(self.0).unwrap();
        let arg1 = CString::new(self.1).unwrap();
        let arg2 = CString::new(self.2).unwrap();
        let arg3 = CString::new(self.3).unwrap();
        let arg4 = CString::new(self.4).unwrap();
        let arg5 = CString::new(self.5).unwrap();
        let arg6 = CString::new(self.6).unwrap();
        let arg7 = CString::new(self.7).unwrap();
        let arg8 = CString::new(self.8).unwrap();
        let arg9 = CString::new(self.9).unwrap();
        unsafe {
            protect(|| {
                Value::new(rb_struct_define(
                    name.as_ptr(),
                    arg0.as_ptr(),
                    arg1.as_ptr(),
                    arg2.as_ptr(),
                    arg3.as_ptr(),
                    arg4.as_ptr(),
                    arg5.as_ptr(),
                    arg6.as_ptr(),
                    arg7.as_ptr(),
                    arg8.as_ptr(),
                    arg9.as_ptr(),
                    null::<c_char>(),
                ))
            })
            .map(|v| RClass::from_rb_value_unchecked(v.as_rb_value()))
        }
    }
}

impl StructMembers
    for (
        &str,
        &str,
        &str,
        &str,
        &str,
        &str,
        &str,
        &str,
        &str,
        &str,
        &str,
    )
{
    fn define(self, name: &str) -> Result<RClass, Error> {
        let name = CString::new(name).unwrap();
        let arg0 = CString::new(self.0).unwrap();
        let arg1 = CString::new(self.1).unwrap();
        let arg2 = CString::new(self.2).unwrap();
        let arg3 = CString::new(self.3).unwrap();
        let arg4 = CString::new(self.4).unwrap();
        let arg5 = CString::new(self.5).unwrap();
        let arg6 = CString::new(self.6).unwrap();
        let arg7 = CString::new(self.7).unwrap();
        let arg8 = CString::new(self.8).unwrap();
        let arg9 = CString::new(self.9).unwrap();
        let arg10 = CString::new(self.10).unwrap();
        unsafe {
            protect(|| {
                Value::new(rb_struct_define(
                    name.as_ptr(),
                    arg0.as_ptr(),
                    arg1.as_ptr(),
                    arg2.as_ptr(),
                    arg3.as_ptr(),
                    arg4.as_ptr(),
                    arg5.as_ptr(),
                    arg6.as_ptr(),
                    arg7.as_ptr(),
                    arg8.as_ptr(),
                    arg9.as_ptr(),
                    arg10.as_ptr(),
                    null::<c_char>(),
                ))
            })
            .map(|v| RClass::from_rb_value_unchecked(v.as_rb_value()))
        }
    }
}

impl StructMembers
    for (
        &str,
        &str,
        &str,
        &str,
        &str,
        &str,
        &str,
        &str,
        &str,
        &str,
        &str,
        &str,
    )
{
    fn define(self, name: &str) -> Result<RClass, Error> {
        let name = CString::new(name).unwrap();
        let arg0 = CString::new(self.0).unwrap();
        let arg1 = CString::new(self.1).unwrap();
        let arg2 = CString::new(self.2).unwrap();
        let arg3 = CString::new(self.3).unwrap();
        let arg4 = CString::new(self.4).unwrap();
        let arg5 = CString::new(self.5).unwrap();
        let arg6 = CString::new(self.6).unwrap();
        let arg7 = CString::new(self.7).unwrap();
        let arg8 = CString::new(self.8).unwrap();
        let arg9 = CString::new(self.9).unwrap();
        let arg10 = CString::new(self.10).unwrap();
        let arg11 = CString::new(self.11).unwrap();
        unsafe {
            protect(|| {
                Value::new(rb_struct_define(
                    name.as_ptr(),
                    arg0.as_ptr(),
                    arg1.as_ptr(),
                    arg2.as_ptr(),
                    arg3.as_ptr(),
                    arg4.as_ptr(),
                    arg5.as_ptr(),
                    arg6.as_ptr(),
                    arg7.as_ptr(),
                    arg8.as_ptr(),
                    arg9.as_ptr(),
                    arg10.as_ptr(),
                    arg11.as_ptr(),
                    null::<c_char>(),
                ))
            })
            .map(|v| RClass::from_rb_value_unchecked(v.as_rb_value()))
        }
    }
}
