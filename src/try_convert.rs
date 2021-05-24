use crate::{error::Error, integer::Integer, value::Value};

pub trait TryConvert: Sized {
    /// # Safety
    ///
    /// unsafe as typically val must be dereferenced to perform the conversion
    unsafe fn try_convert(val: Value) -> Result<Self, Error>;
}

/// Only implemented on Rust types. TryConvert may convert from a
/// Value to another Ruby type. Use this when you need a Rust value that's
/// divorced from the Ruby runtime, safe to put on the heap, etc.
pub trait TryConvertToRust: Sized + TryConvert {
    /// # Safety
    ///
    /// unsafe as typically val must be dereferenced to perform the conversion
    unsafe fn try_convert_to_rust(val: Value) -> Result<Self, Error> {
        Self::try_convert(val)
    }
}

impl TryConvert for Value {
    unsafe fn try_convert(val: Value) -> Result<Self, Error> {
        Ok(val)
    }
}

impl<T> TryConvert for Option<T>
where
    T: TryConvert,
{
    unsafe fn try_convert(val: Value) -> Result<Self, Error> {
        val.is_nil()
            .then(|| T::try_convert(val))
            .transpose()
    }
}

impl<T> TryConvertToRust for Option<T>
where
    T: TryConvertToRust,
{
    unsafe fn try_convert_to_rust(val: Value) -> Result<Self, Error> {
        val.is_nil()
            .then(|| T::try_convert_to_rust(val))
            .transpose()
    }
}

impl TryConvert for bool {
    unsafe fn try_convert(val: Value) -> Result<Self, Error> {
        Ok(val.to_bool())
    }
}
impl TryConvertToRust for bool {}

impl TryConvert for i8 {
    unsafe fn try_convert(val: Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_i8()
    }
}
impl TryConvertToRust for i8 {}

impl TryConvert for i16 {
    unsafe fn try_convert(val: Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_i16()
    }
}
impl TryConvertToRust for i16 {}

impl TryConvert for i32 {
    unsafe fn try_convert(val: Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_i32()
    }
}
impl TryConvertToRust for i32 {}

impl TryConvert for i64 {
    unsafe fn try_convert(val: Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_i64()
    }
}
impl TryConvertToRust for i64 {}

impl TryConvert for isize {
    unsafe fn try_convert(val: Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_isize()
    }
}
impl TryConvertToRust for isize {}

impl TryConvert for u8 {
    unsafe fn try_convert(val: Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_u8()
    }
}
impl TryConvertToRust for u8 {}

impl TryConvert for u16 {
    unsafe fn try_convert(val: Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_u16()
    }
}
impl TryConvertToRust for u16 {}

impl TryConvert for u32 {
    unsafe fn try_convert(val: Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_u32()
    }
}
impl TryConvertToRust for u32 {}

impl TryConvert for u64 {
    unsafe fn try_convert(val: Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_u64()
    }
}
impl TryConvertToRust for u64 {}

impl TryConvert for usize {
    unsafe fn try_convert(val: Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_usize()
    }
}
impl TryConvertToRust for usize {}
