use std::path::PathBuf;

use rb_sys::{rb_get_path, rb_num2dbl};
use seq_macro::seq;

#[cfg(ruby_use_flonum)]
use crate::value::Flonum;
use crate::{
    error::{protect, Error},
    integer::Integer,
    r_array::RArray,
    r_hash::RHash,
    r_string::RString,
    value::{Fixnum, ReprValue, Value},
    Ruby,
};

/// Conversions from [`Value`] to Rust types.
pub trait TryConvert: Sized {
    /// Convert `val` into `Self`.
    fn try_convert(val: Value) -> Result<Self, Error>;
}

/// Only implemented on Rust types. TryConvert may convert from a
/// Value to another Ruby type. Use this when you need a Rust value that's
/// divorced from the Ruby runtime, safe to put on the heap, etc.
pub trait TryConvertOwned: TryConvert {
    /// Convert `val` into `Self`.
    fn try_convert_owned(val: Value) -> Result<Self, Error> {
        Self::try_convert(val)
    }
}

pub trait TryConvertForArg: Sized {
    /// Convert `val` into `Self`.
    fn try_convert_for_arg(val: Value) -> Result<Self, Error>;
}

impl<T> TryConvert for Option<T>
where
    T: TryConvert,
{
    fn try_convert(val: Value) -> Result<Self, Error> {
        (!val.is_nil()).then(|| T::try_convert(val)).transpose()
    }
}

impl<T> TryConvertOwned for Option<T>
where
    T: TryConvertOwned,
{
    fn try_convert_owned(val: Value) -> Result<Self, Error> {
        (!val.is_nil())
            .then(|| T::try_convert_owned(val))
            .transpose()
    }
}

impl TryConvert for bool {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Ok(val.to_bool())
    }
}
impl TryConvertOwned for bool {}

impl TryConvert for i8 {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_i8()
    }
}
impl TryConvertOwned for i8 {}

impl TryConvert for i16 {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_i16()
    }
}
impl TryConvertOwned for i16 {}

impl TryConvert for i32 {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_i32()
    }
}
impl TryConvertOwned for i32 {}

impl TryConvert for i64 {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_i64()
    }
}
impl TryConvertOwned for i64 {}

impl TryConvert for isize {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_isize()
    }
}
impl TryConvertOwned for isize {}

impl TryConvert for u8 {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_u8()
    }
}
impl TryConvertOwned for u8 {}

impl TryConvert for u16 {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_u16()
    }
}
impl TryConvertOwned for u16 {}

impl TryConvert for u32 {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_u32()
    }
}
impl TryConvertOwned for u32 {}

impl TryConvert for u64 {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_u64()
    }
}
impl TryConvertOwned for u64 {}

impl TryConvert for usize {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_usize()
    }
}
impl TryConvertOwned for usize {}

impl TryConvert for f32 {
    fn try_convert(val: Value) -> Result<Self, Error> {
        f64::try_convert(val).map(|f| f as f32)
    }
}
impl TryConvertOwned for f32 {}

impl TryConvert for f64 {
    fn try_convert(val: Value) -> Result<Self, Error> {
        if let Some(fixnum) = Fixnum::from_value(val) {
            return Ok(fixnum.to_isize() as f64);
        }
        #[cfg(ruby_use_flonum)]
        if let Some(flonum) = Flonum::from_value(val) {
            return Ok(flonum.to_f64());
        }
        debug_assert_value!(val);
        let mut res = 0.0;
        protect(|| {
            unsafe { res = rb_num2dbl(val.as_rb_value()) };
            Ruby::get_with(val).qnil()
        })?;
        Ok(res)
    }
}
impl TryConvertOwned for f64 {}

impl TryConvert for String {
    fn try_convert(val: Value) -> Result<Self, Error> {
        debug_assert_value!(val);
        RString::try_convert(val)?.to_string()
    }
}
impl TryConvertOwned for String {}

#[cfg(feature = "bytes-crate")]
impl TryConvert for bytes::Bytes {
    fn try_convert(val: Value) -> Result<bytes::Bytes, Error> {
        debug_assert_value!(val);
        Ok(RString::try_convert(val)?.to_bytes())
    }
}

#[cfg(feature = "bytes-crate")]
impl TryConvertOwned for bytes::Bytes {}

impl TryConvert for char {
    fn try_convert(val: Value) -> Result<Self, Error> {
        debug_assert_value!(val);
        RString::try_convert(val)?.to_char()
    }
}
impl TryConvertOwned for char {}

impl<T> TryConvert for Vec<T>
where
    T: TryConvertOwned,
{
    fn try_convert(val: Value) -> Result<Self, Error> {
        debug_assert_value!(val);
        RArray::try_convert(val)?.to_vec()
    }
}
impl<T> TryConvertOwned for Vec<T> where T: TryConvertOwned {}

impl<T, const N: usize> TryConvert for [T; N]
where
    T: TryConvert,
{
    fn try_convert(val: Value) -> Result<Self, Error> {
        debug_assert_value!(val);
        RArray::try_convert(val)?.to_array()
    }
}
impl<T, const N: usize> TryConvertOwned for [T; N] where T: TryConvert {}

macro_rules! impl_try_convert {
    ($n:literal) => {
        seq!(N in 0..$n {
            impl<#(T~N,)*> TryConvert for (#(T~N,)*)
            where
                #(T~N: TryConvert,)*
            {
                fn try_convert(val: Value) -> Result<Self, Error> {
                    debug_assert_value!(val);
                    let array = RArray::try_convert(val)?;
                    let slice = unsafe { array.as_slice() };
                    if slice.len() != $n {
                        return Err(Error::new(
                            Ruby::get_with(val).exception_type_error(),
                            concat!("expected Array of length ", $n),
                        ));
                    }
                    Ok((
                        #(TryConvert::try_convert(slice[N])?,)*
                    ))
                }
            }
            impl<#(T~N,)*> TryConvertOwned for (#(T~N,)*)
            where
                #(T~N: TryConvert,)*
            {
            }
        });
    }
}

seq!(N in 1..=12 {
    impl_try_convert!(N);
});

impl<K, V> TryConvert for std::collections::HashMap<K, V>
where
    K: TryConvertOwned + Eq + std::hash::Hash,
    V: TryConvertOwned,
{
    fn try_convert(val: Value) -> Result<Self, Error> {
        debug_assert_value!(val);
        RHash::try_convert(val)?.to_hash_map()
    }
}
impl<K, V> TryConvertOwned for std::collections::HashMap<K, V>
where
    K: TryConvertOwned + Eq + std::hash::Hash,
    V: TryConvertOwned,
{
}

#[cfg(unix)]
impl TryConvert for PathBuf {
    fn try_convert(val: Value) -> Result<Self, Error> {
        use std::os::unix::ffi::OsStringExt;

        let bytes = unsafe {
            let r_string =
                protect(|| RString::from_rb_value_unchecked(rb_get_path(val.as_rb_value())))?;
            r_string.as_slice().to_owned()
        };
        Ok(std::ffi::OsString::from_vec(bytes).into())
    }
}

#[cfg(not(unix))]
impl TryConvert for PathBuf {
    fn try_convert(val: Value) -> Result<Self, Error> {
        protect(|| unsafe { RString::from_rb_value_unchecked(rb_get_path(val.as_rb_value())) })?
            .to_string()
            .map(Into::into)
    }
}

impl TryConvertOwned for PathBuf {}
