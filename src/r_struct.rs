//! Types and functions for working with Ruby's Struct class.

use std::{
    borrow::Cow,
    ffi::CString,
    fmt,
    ops::Deref,
    os::raw::c_char,
    ptr::{null, NonNull},
    slice,
};

use crate::{
    class::RClass,
    debug_assert_value,
    error::{protect, Error},
    exception,
    object::Object,
    r_array::RArray,
    ruby_sys::{
        rb_struct_aref, rb_struct_aset, rb_struct_define, rb_struct_getmember, rb_struct_members,
        rb_struct_size, ruby_value_type, VALUE,
    },
    symbol::Symbol,
    try_convert::TryConvert,
    value::{self, Id, NonZeroValue, Value},
};

// Ruby provides some inline functions to get a pointer to the struct's
// contents, but we have to reimplement those for Rust. The for that we need
// the definition of RStruct, but that isn't public, so we have to duplicate it
// here.
mod sys {
    use crate::ruby_sys::{ruby_fl_type, RBasic, VALUE};

    #[cfg(ruby_gte_3_0)]
    use crate::ruby_sys::ruby_fl_ushift::RUBY_FL_USHIFT;

    #[cfg(ruby_lt_3_0)]
    use crate::ruby_sys::ruby_fl_type::RUBY_FL_USHIFT;

    #[cfg(ruby_gte_2_7)]
    pub const EMBED_LEN_MAX: u32 = crate::ruby_sys::ruby_rvalue_flags::RVALUE_EMBED_LEN_MAX as u32;

    #[cfg(ruby_lt_2_7)]
    pub const EMBED_LEN_MAX: u32 = 3;

    pub const EMBED_LEN_MASK: u32 =
        ruby_fl_type::RUBY_FL_USER2 as u32 | ruby_fl_type::RUBY_FL_USER1 as u32;
    pub const EMBED_LEN_SHIFT: u32 = RUBY_FL_USHIFT as u32 + 1;

    #[repr(C)]
    #[derive(Copy, Clone)]
    pub struct RStruct {
        pub basic: RBasic,
        pub as_: As,
    }
    #[repr(C)]
    #[derive(Copy, Clone)]
    pub union As {
        pub heap: Heap,
        pub ary: [VALUE; EMBED_LEN_MAX as usize],
    }
    #[repr(C)]
    #[derive(Debug, Copy, Clone)]
    pub struct Heap {
        pub len: std::os::raw::c_long,
        pub ptr: *const VALUE,
    }
}

/// A Value pointer to a RStruct struct, Ruby’s internal representation of
/// 'Structs'.
///
/// All [`Value`] methods should be available on this type through [`Deref`],
/// but some may be missed by this documentation.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RStruct(NonZeroValue);

impl RStruct {
    /// Return `Some(RStruct)` if `val` is a `RStruct`, `None` otherwise.
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            (val.rb_type() == ruby_value_type::RUBY_T_STRUCT)
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        Self(NonZeroValue::new_unchecked(Value::new(val)))
    }

    fn as_internal(self) -> NonNull<sys::RStruct> {
        // safe as inner value is NonZero
        unsafe { NonNull::new_unchecked(self.0.get().as_rb_value() as *mut _) }
    }

    /// Return the members of the struct as a slice of [`Value`]s. The order
    /// will be the order the of the member names when the struct class was
    /// defined.
    ///
    /// # Safety
    ///
    /// Ruby may modify or free the memory backing the returned slice, the
    /// caller must ensure this does not happen.
    pub unsafe fn as_slice(&self) -> &[Value] {
        self.as_slice_unconstrained()
    }

    pub(crate) unsafe fn as_slice_unconstrained<'a>(self) -> &'a [Value] {
        debug_assert_value!(self);
        let r_basic = self.r_basic_unchecked();
        let flags = r_basic.as_ref().flags;
        if (flags & sys::EMBED_LEN_MASK as VALUE) != 0 {
            let len = (flags & sys::EMBED_LEN_MASK as VALUE) >> sys::EMBED_LEN_SHIFT as VALUE;
            slice::from_raw_parts(
                &self.as_internal().as_ref().as_.ary as *const VALUE as *const Value,
                len as usize,
            )
        } else {
            let h = self.as_internal().as_ref().as_.heap;
            slice::from_raw_parts(h.ptr as *const Value, h.len as usize)
        }
    }

    /// Return the value for the member at `index`, where members are ordered
    /// as per the member names when the struct class was defined.
    pub fn get<T>(self, index: usize) -> Result<T, Error>
    where
        T: TryConvert,
    {
        unsafe {
            let slice = self.as_slice();
            slice
                .get(index)
                .ok_or_else(|| {
                    Error::new(
                        exception::index_error(),
                        format!(
                            "offset {} too large for struct(size:{})",
                            index,
                            slice.len()
                        ),
                    )
                })
                .and_then(|v| v.try_convert())
        }
    }

    /// Return the value for the member at `index`.
    ///
    /// `index` may be an integer, string, or [`Symbol`].
    pub fn aref<T, U>(self, index: T) -> Result<U, Error>
    where
        T: Into<Value>,
        U: TryConvert,
    {
        let index = index.into();
        unsafe {
            protect(|| Value::new(rb_struct_aref(self.as_rb_value(), index.as_rb_value())))
                .and_then(|v| v.try_convert())
        }
    }

    /// Return the value for the member at `index`.
    ///
    /// `index` may be an integer, string, or [`Symbol`].
    pub fn aset<T, U>(self, index: T, val: U) -> Result<(), Error>
    where
        T: Into<Value>,
        U: Into<Value>,
    {
        let index = index.into();
        let val = val.into();
        unsafe {
            protect(|| {
                Value::new(rb_struct_aset(
                    self.as_rb_value(),
                    index.as_rb_value(),
                    val.as_rb_value(),
                ))
            })?;
        }
        Ok(())
    }

    /// Returns the count of members this struct has.
    pub fn size(self) -> usize {
        unsafe {
            Value::new(rb_struct_size(self.as_rb_value()))
                .try_convert()
                .unwrap()
        }
    }

    /// Returns the member names for this struct as [`Symbol`]s.
    pub fn members(self) -> Result<Vec<Cow<'static, str>>, Error> {
        unsafe {
            let array = RArray::from_rb_value_unchecked(rb_struct_members(self.as_rb_value()));
            array
                .as_slice()
                .iter()
                .map(|v| Symbol::from_value(*v).unwrap().name())
                .collect()
        }
    }

    /// Return the value for the member named `id`.
    pub fn getmember<T, U>(self, id: T) -> Result<U, Error>
    where
        T: Into<Id>,
        U: TryConvert,
    {
        let id = id.into();
        unsafe {
            protect(|| Value::new(rb_struct_getmember(self.as_rb_value(), id.as_rb_id())))
                .and_then(|v| v.try_convert())
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

unsafe impl value::private::ReprValue for RStruct {
    fn to_value(self) -> Value {
        *self
    }

    unsafe fn from_value_unchecked(val: Value) -> Self {
        Self(NonZeroValue::new_unchecked(val))
    }
}

impl TryConvert for RStruct {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        Self::from_value(*val).ok_or_else(|| {
            Error::new(
                exception::type_error(),
                format!("no implicit conversion of {} into Struct", unsafe {
                    val.classname()
                },),
            )
        })
    }
}

/// Define a Ruby Struct class.
pub fn define_struct<T>(name: Option<&str>, members: T) -> Result<RClass, Error>
where
    T: StructMembers,
{
    members.define(name)
}

mod private {
    use super::*;

    pub trait StructMembers {
        fn define(self, name: Option<&str>) -> Result<RClass, Error>;
    }
}
use private::StructMembers;

impl StructMembers for (&str,) {
    fn define(self, name: Option<&str>) -> Result<RClass, Error> {
        let name = name.map(|n| CString::new(n).unwrap());
        let arg0 = CString::new(self.0).unwrap();
        unsafe {
            protect(|| {
                Value::new(rb_struct_define(
                    name.as_ref().map(|n| n.as_ptr()).unwrap_or_else(null),
                    arg0.as_ptr(),
                    null::<c_char>(),
                ))
            })
            .map(|v| RClass::from_rb_value_unchecked(v.as_rb_value()))
        }
    }
}

impl StructMembers for (&str, &str) {
    fn define(self, name: Option<&str>) -> Result<RClass, Error> {
        let name = name.map(|n| CString::new(n).unwrap());
        let arg0 = CString::new(self.0).unwrap();
        let arg1 = CString::new(self.1).unwrap();
        unsafe {
            protect(|| {
                Value::new(rb_struct_define(
                    name.as_ref().map(|n| n.as_ptr()).unwrap_or_else(null),
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
    fn define(self, name: Option<&str>) -> Result<RClass, Error> {
        let name = name.map(|n| CString::new(n).unwrap());
        let arg0 = CString::new(self.0).unwrap();
        let arg1 = CString::new(self.1).unwrap();
        let arg2 = CString::new(self.2).unwrap();
        unsafe {
            protect(|| {
                Value::new(rb_struct_define(
                    name.as_ref().map(|n| n.as_ptr()).unwrap_or_else(null),
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
    fn define(self, name: Option<&str>) -> Result<RClass, Error> {
        let name = name.map(|n| CString::new(n).unwrap());
        let arg0 = CString::new(self.0).unwrap();
        let arg1 = CString::new(self.1).unwrap();
        let arg2 = CString::new(self.2).unwrap();
        let arg3 = CString::new(self.3).unwrap();
        unsafe {
            protect(|| {
                Value::new(rb_struct_define(
                    name.as_ref().map(|n| n.as_ptr()).unwrap_or_else(null),
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
    fn define(self, name: Option<&str>) -> Result<RClass, Error> {
        let name = name.map(|n| CString::new(n).unwrap());
        let arg0 = CString::new(self.0).unwrap();
        let arg1 = CString::new(self.1).unwrap();
        let arg2 = CString::new(self.2).unwrap();
        let arg3 = CString::new(self.3).unwrap();
        let arg4 = CString::new(self.4).unwrap();
        unsafe {
            protect(|| {
                Value::new(rb_struct_define(
                    name.as_ref().map(|n| n.as_ptr()).unwrap_or_else(null),
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
    fn define(self, name: Option<&str>) -> Result<RClass, Error> {
        let name = name.map(|n| CString::new(n).unwrap());
        let arg0 = CString::new(self.0).unwrap();
        let arg1 = CString::new(self.1).unwrap();
        let arg2 = CString::new(self.2).unwrap();
        let arg3 = CString::new(self.3).unwrap();
        let arg4 = CString::new(self.4).unwrap();
        let arg5 = CString::new(self.5).unwrap();
        unsafe {
            protect(|| {
                Value::new(rb_struct_define(
                    name.as_ref().map(|n| n.as_ptr()).unwrap_or_else(null),
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
    fn define(self, name: Option<&str>) -> Result<RClass, Error> {
        let name = name.map(|n| CString::new(n).unwrap());
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
                    name.as_ref().map(|n| n.as_ptr()).unwrap_or_else(null),
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
    fn define(self, name: Option<&str>) -> Result<RClass, Error> {
        let name = name.map(|n| CString::new(n).unwrap());
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
                    name.as_ref().map(|n| n.as_ptr()).unwrap_or_else(null),
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
    fn define(self, name: Option<&str>) -> Result<RClass, Error> {
        let name = name.map(|n| CString::new(n).unwrap());
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
                    name.as_ref().map(|n| n.as_ptr()).unwrap_or_else(null),
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
    fn define(self, name: Option<&str>) -> Result<RClass, Error> {
        let name = name.map(|n| CString::new(n).unwrap());
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
                    name.as_ref().map(|n| n.as_ptr()).unwrap_or_else(null),
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
    fn define(self, name: Option<&str>) -> Result<RClass, Error> {
        let name = name.map(|n| CString::new(n).unwrap());
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
                    name.as_ref().map(|n| n.as_ptr()).unwrap_or_else(null),
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
    fn define(self, name: Option<&str>) -> Result<RClass, Error> {
        let name = name.map(|n| CString::new(n).unwrap());
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
                    name.as_ref().map(|n| n.as_ptr()).unwrap_or_else(null),
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
