use crate::{error::Error, integer::Integer, value::Value};

pub trait ImplicitConvertFrom: Sized {
    /// # Safety
    ///
    /// unsafe as typically val must be dereferenced to perform the conversion
    unsafe fn implicit_convert_from(val: Value) -> Result<Self, Error>;
}

/// Only implemented on Rust types. ImplicitConvertFrom may convert from a
/// Value to another Ruby type. Use this when you need a Rust value that's
/// divorced from the Ruby runtime, safe to put on the heap, etc.
pub trait ImplicitConvertToRustFrom: Sized + ImplicitConvertFrom {
    /// # Safety
    ///
    /// unsafe as typically val must be dereferenced to perform the conversion
    unsafe fn implicit_convert_to_rust_from(val: Value) -> Result<Self, Error> {
        Self::implicit_convert_from(val)
    }
}

impl ImplicitConvertFrom for Value {
    unsafe fn implicit_convert_from(val: Value) -> Result<Self, Error> {
        Ok(val)
    }
}

impl<T> ImplicitConvertFrom for Option<T>
where
    T: ImplicitConvertFrom,
{
    unsafe fn implicit_convert_from(val: Value) -> Result<Self, Error> {
        val.is_nil()
            .then(|| T::implicit_convert_from(val))
            .transpose()
    }
}

impl<T> ImplicitConvertToRustFrom for Option<T>
where
    T: ImplicitConvertToRustFrom,
{
    unsafe fn implicit_convert_to_rust_from(val: Value) -> Result<Self, Error> {
        val.is_nil()
            .then(|| T::implicit_convert_to_rust_from(val))
            .transpose()
    }
}

impl ImplicitConvertFrom for bool {
    unsafe fn implicit_convert_from(val: Value) -> Result<Self, Error> {
        Ok(val.to_bool())
    }
}
impl ImplicitConvertToRustFrom for bool {}

impl ImplicitConvertFrom for i8 {
    unsafe fn implicit_convert_from(val: Value) -> Result<Self, Error> {
        Integer::implicit_convert_from(val)?.to_i8()
    }
}
impl ImplicitConvertToRustFrom for i8 {}

impl ImplicitConvertFrom for i16 {
    unsafe fn implicit_convert_from(val: Value) -> Result<Self, Error> {
        Integer::implicit_convert_from(val)?.to_i16()
    }
}
impl ImplicitConvertToRustFrom for i16 {}

impl ImplicitConvertFrom for i32 {
    unsafe fn implicit_convert_from(val: Value) -> Result<Self, Error> {
        Integer::implicit_convert_from(val)?.to_i32()
    }
}
impl ImplicitConvertToRustFrom for i32 {}

impl ImplicitConvertFrom for i64 {
    unsafe fn implicit_convert_from(val: Value) -> Result<Self, Error> {
        Integer::implicit_convert_from(val)?.to_i64()
    }
}
impl ImplicitConvertToRustFrom for i64 {}

impl ImplicitConvertFrom for isize {
    unsafe fn implicit_convert_from(val: Value) -> Result<Self, Error> {
        Integer::implicit_convert_from(val)?.to_isize()
    }
}
impl ImplicitConvertToRustFrom for isize {}

impl ImplicitConvertFrom for u8 {
    unsafe fn implicit_convert_from(val: Value) -> Result<Self, Error> {
        Integer::implicit_convert_from(val)?.to_u8()
    }
}
impl ImplicitConvertToRustFrom for u8 {}

impl ImplicitConvertFrom for u16 {
    unsafe fn implicit_convert_from(val: Value) -> Result<Self, Error> {
        Integer::implicit_convert_from(val)?.to_u16()
    }
}
impl ImplicitConvertToRustFrom for u16 {}

impl ImplicitConvertFrom for u32 {
    unsafe fn implicit_convert_from(val: Value) -> Result<Self, Error> {
        Integer::implicit_convert_from(val)?.to_u32()
    }
}
impl ImplicitConvertToRustFrom for u32 {}

impl ImplicitConvertFrom for u64 {
    unsafe fn implicit_convert_from(val: Value) -> Result<Self, Error> {
        Integer::implicit_convert_from(val)?.to_u64()
    }
}
impl ImplicitConvertToRustFrom for u64 {}

impl ImplicitConvertFrom for usize {
    unsafe fn implicit_convert_from(val: Value) -> Result<Self, Error> {
        Integer::implicit_convert_from(val)?.to_usize()
    }
}
impl ImplicitConvertToRustFrom for usize {}
