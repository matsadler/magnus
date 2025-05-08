//! Traits for converting from Ruby [`Value`]s to Rust types.

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

/// Conversions from [`Value`] to Rust types that do not contain [`Value`].
///
/// This trait is used as a bound on some implementations of [`TryConvert`]
/// (for example, for [`Vec`]) to prevent heap allocated data structures
/// containing `Value`, as it is not safe to store a `Value` on the heap.
///
/// # Safety
///
/// This trait must not be implemented for types that contain `Value`.
pub unsafe trait TryConvertOwned: TryConvert {}

impl<T> TryConvert for Option<T>
where
    T: TryConvert,
{
    #[inline]
    fn try_convert(val: Value) -> Result<Self, Error> {
        (!val.is_nil()).then(|| T::try_convert(val)).transpose()
    }
}

unsafe impl<T> TryConvertOwned for Option<T> where T: TryConvertOwned {}

impl TryConvert for bool {
    #[inline]
    fn try_convert(val: Value) -> Result<Self, Error> {
        Ok(val.to_bool())
    }
}
unsafe impl TryConvertOwned for bool {}

impl TryConvert for i8 {
    #[inline]
    fn try_convert(val: Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_i8()
    }
}
unsafe impl TryConvertOwned for i8 {}

impl TryConvert for i16 {
    #[inline]
    fn try_convert(val: Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_i16()
    }
}
unsafe impl TryConvertOwned for i16 {}

impl TryConvert for i32 {
    #[inline]
    fn try_convert(val: Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_i32()
    }
}
unsafe impl TryConvertOwned for i32 {}

impl TryConvert for i64 {
    #[inline]
    fn try_convert(val: Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_i64()
    }
}
unsafe impl TryConvertOwned for i64 {}

impl TryConvert for i128 {
    #[inline]
    fn try_convert(val: Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_i128()
    }
}
unsafe impl TryConvertOwned for i128 {}

impl TryConvert for isize {
    #[inline]
    fn try_convert(val: Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_isize()
    }
}
unsafe impl TryConvertOwned for isize {}

impl TryConvert for u8 {
    #[inline]
    fn try_convert(val: Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_u8()
    }
}
unsafe impl TryConvertOwned for u8 {}

impl TryConvert for u16 {
    #[inline]
    fn try_convert(val: Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_u16()
    }
}
unsafe impl TryConvertOwned for u16 {}

impl TryConvert for u32 {
    #[inline]
    fn try_convert(val: Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_u32()
    }
}
unsafe impl TryConvertOwned for u32 {}

impl TryConvert for u64 {
    #[inline]
    fn try_convert(val: Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_u64()
    }
}
unsafe impl TryConvertOwned for u64 {}

impl TryConvert for u128 {
    #[inline]
    fn try_convert(val: Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_u128()
    }
}
unsafe impl TryConvertOwned for u128 {}

impl TryConvert for usize {
    #[inline]
    fn try_convert(val: Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_usize()
    }
}
unsafe impl TryConvertOwned for usize {}

macro_rules! impl_non_zero_try_convert {
    ($type:ty, $prim:ty) => {
        impl TryConvert for $type {
            #[inline]
            fn try_convert(val: Value) -> Result<Self, Error> {
                <$type>::new(<$prim>::try_convert(val)?).ok_or(Error::new(
                    Ruby::get_with(val).exception_arg_error(),
                    "value must be non-zero",
                ))
            }
        }
        unsafe impl TryConvertOwned for $type {}
    };
}

impl_non_zero_try_convert!(std::num::NonZeroI8, i8);
impl_non_zero_try_convert!(std::num::NonZeroI16, i16);
impl_non_zero_try_convert!(std::num::NonZeroI32, i32);
impl_non_zero_try_convert!(std::num::NonZeroI64, i64);
impl_non_zero_try_convert!(std::num::NonZeroI128, i128);
impl_non_zero_try_convert!(std::num::NonZeroIsize, isize);
impl_non_zero_try_convert!(std::num::NonZeroU8, u8);
impl_non_zero_try_convert!(std::num::NonZeroU16, u16);
impl_non_zero_try_convert!(std::num::NonZeroU32, u32);
impl_non_zero_try_convert!(std::num::NonZeroU64, u64);
impl_non_zero_try_convert!(std::num::NonZeroU128, u128);
impl_non_zero_try_convert!(std::num::NonZeroUsize, usize);

impl TryConvert for f32 {
    #[inline]
    fn try_convert(val: Value) -> Result<Self, Error> {
        f64::try_convert(val).map(|f| f as f32)
    }
}
unsafe impl TryConvertOwned for f32 {}

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
unsafe impl TryConvertOwned for f64 {}

impl TryConvert for String {
    #[inline]
    fn try_convert(val: Value) -> Result<Self, Error> {
        debug_assert_value!(val);
        RString::try_convert(val)?.to_string()
    }
}
unsafe impl TryConvertOwned for String {}

#[cfg(feature = "bytes")]
impl TryConvert for bytes::Bytes {
    #[inline]
    fn try_convert(val: Value) -> Result<bytes::Bytes, Error> {
        debug_assert_value!(val);
        Ok(RString::try_convert(val)?.to_bytes())
    }
}

#[cfg(feature = "bytes")]
unsafe impl TryConvertOwned for bytes::Bytes {}

impl TryConvert for char {
    #[inline]
    fn try_convert(val: Value) -> Result<Self, Error> {
        debug_assert_value!(val);
        RString::try_convert(val)?.to_char()
    }
}
unsafe impl TryConvertOwned for char {}

impl<T> TryConvert for Vec<T>
where
    T: TryConvertOwned,
{
    #[inline]
    fn try_convert(val: Value) -> Result<Self, Error> {
        debug_assert_value!(val);
        RArray::try_convert(val)?.to_vec()
    }
}
unsafe impl<T> TryConvertOwned for Vec<T> where T: TryConvertOwned {}

impl<T, const N: usize> TryConvert for [T; N]
where
    T: TryConvert,
{
    #[inline]
    fn try_convert(val: Value) -> Result<Self, Error> {
        debug_assert_value!(val);
        RArray::try_convert(val)?.to_array()
    }
}
unsafe impl<T, const N: usize> TryConvertOwned for [T; N] where T: TryConvert {}

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
            unsafe impl<#(T~N,)*> TryConvertOwned for (#(T~N,)*)
            where
                #(T~N: TryConvertOwned,)*
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
    #[inline]
    fn try_convert(val: Value) -> Result<Self, Error> {
        debug_assert_value!(val);
        RHash::try_convert(val)?.to_hash_map()
    }
}
unsafe impl<K, V> TryConvertOwned for std::collections::HashMap<K, V>
where
    K: TryConvertOwned + Eq + std::hash::Hash,
    V: TryConvertOwned,
{
}

impl<K, V> TryConvert for std::collections::BTreeMap<K, V>
where
    K: TryConvertOwned + Eq + std::hash::Hash + Ord,
    V: TryConvertOwned,
{
    #[inline]
    fn try_convert(val: Value) -> Result<Self, Error> {
        debug_assert_value!(val);
        RHash::try_convert(val)?.to_btree_map()
    }
}
unsafe impl<K, V> TryConvertOwned for std::collections::BTreeMap<K, V>
where
    K: TryConvertOwned + Eq + std::hash::Hash + Ord,
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

unsafe impl TryConvertOwned for PathBuf {}
