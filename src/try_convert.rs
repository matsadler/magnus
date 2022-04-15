use std::path::PathBuf;

use crate::ruby_sys::{rb_get_path, rb_num2dbl};

use crate::{
    debug_assert_value,
    error::{protect, Error},
    exception,
    integer::Integer,
    r_array::RArray,
    r_hash::RHash,
    r_string::RString,
    value::{Value, QNIL},
};

/// Conversions from [`Value`] to Rust types.
pub trait TryConvert: Sized {
    /// Convert `val` into `Self`.
    fn try_convert(val: &Value) -> Result<Self, Error>;
}

/// Only implemented on Rust types. TryConvert may convert from a
/// Value to another Ruby type. Use this when you need a Rust value that's
/// divorced from the Ruby runtime, safe to put on the heap, etc.
pub trait TryConvertOwned: TryConvert {
    /// Convert `val` into `Self`.
    #[inline]
    fn try_convert_owned(val: Value) -> Result<Self, Error> {
        Self::try_convert(&val)
    }
}

impl<T> TryConvert for Option<T>
where
    T: TryConvert,
{
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        (!val.is_nil()).then(|| T::try_convert(val)).transpose()
    }
}

impl<T> TryConvertOwned for Option<T>
where
    T: TryConvertOwned,
{
    #[inline]
    fn try_convert_owned(val: Value) -> Result<Self, Error> {
        (!val.is_nil())
            .then(|| T::try_convert_owned(val))
            .transpose()
    }
}

impl TryConvert for bool {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        Ok(val.to_bool())
    }
}
impl TryConvertOwned for bool {}

impl TryConvert for i8 {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_i8()
    }
}
impl TryConvertOwned for i8 {}

impl TryConvert for i16 {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_i16()
    }
}
impl TryConvertOwned for i16 {}

impl TryConvert for i32 {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_i32()
    }
}
impl TryConvertOwned for i32 {}

impl TryConvert for i64 {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_i64()
    }
}
impl TryConvertOwned for i64 {}

impl TryConvert for isize {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_isize()
    }
}
impl TryConvertOwned for isize {}

impl TryConvert for u8 {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_u8()
    }
}
impl TryConvertOwned for u8 {}

impl TryConvert for u16 {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_u16()
    }
}
impl TryConvertOwned for u16 {}

impl TryConvert for u32 {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_u32()
    }
}
impl TryConvertOwned for u32 {}

impl TryConvert for u64 {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_u64()
    }
}
impl TryConvertOwned for u64 {}

impl TryConvert for usize {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_usize()
    }
}
impl TryConvertOwned for usize {}

impl TryConvert for f32 {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        f64::try_convert(val).map(|f| f as f32)
    }
}
impl TryConvertOwned for f32 {}

impl TryConvert for f64 {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        debug_assert_value!(val);
        let mut res = 0.0;
        protect(|| {
            res = unsafe { rb_num2dbl(val.as_rb_value()) };
            *QNIL
        })?;
        Ok(res)
    }
}
impl TryConvertOwned for f64 {}

impl TryConvert for String {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        debug_assert_value!(val);
        RString::try_convert(val)?.to_string()
    }
}
impl TryConvertOwned for String {}

impl TryConvert for char {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        debug_assert_value!(val);
        RString::try_convert(val)?.to_char()
    }
}
impl TryConvertOwned for char {}

impl<T> TryConvert for Vec<T>
where
    T: TryConvertOwned,
{
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        debug_assert_value!(val);
        RArray::try_convert(val)?.to_vec()
    }
}
impl<T> TryConvertOwned for Vec<T> where T: TryConvertOwned {}

impl<T, const N: usize> TryConvert for [T; N]
where
    T: TryConvert,
{
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        debug_assert_value!(val);
        RArray::try_convert(val)?.to_array()
    }
}
impl<T, const N: usize> TryConvertOwned for [T; N] where T: TryConvert {}

impl<T0> TryConvert for (T0,)
where
    T0: TryConvert,
{
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        debug_assert_value!(val);
        let array = RArray::try_convert(val)?;
        let slice = unsafe { array.as_slice() };
        if slice.len() != 1 {
            return Err(Error::new(
                exception::type_error(),
                "expected Array of length 1",
            ));
        }
        Ok((slice[0].try_convert()?,))
    }
}
impl<T0> TryConvertOwned for (T0,) where T0: TryConvert {}

impl<T0, T1> TryConvert for (T0, T1)
where
    T0: TryConvert,
    T1: TryConvert,
{
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        debug_assert_value!(val);
        let array = RArray::try_convert(val)?;
        let slice = unsafe { array.as_slice() };
        if slice.len() != 2 {
            return Err(Error::new(
                exception::type_error(),
                "expected Array of length 2",
            ));
        }
        Ok((slice[0].try_convert()?, slice[1].try_convert()?))
    }
}
impl<T0, T1> TryConvertOwned for (T0, T1)
where
    T0: TryConvert,
    T1: TryConvert,
{
}

impl<T0, T1, T2> TryConvert for (T0, T1, T2)
where
    T0: TryConvert,
    T1: TryConvert,
    T2: TryConvert,
{
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        debug_assert_value!(val);
        let array = RArray::try_convert(val)?;
        let slice = unsafe { array.as_slice() };
        if slice.len() != 3 {
            return Err(Error::new(
                exception::type_error(),
                "expected Array of length 3",
            ));
        }
        Ok((
            slice[0].try_convert()?,
            slice[1].try_convert()?,
            slice[2].try_convert()?,
        ))
    }
}
impl<T0, T1, T2> TryConvertOwned for (T0, T1, T2)
where
    T0: TryConvert,
    T1: TryConvert,
    T2: TryConvert,
{
}

impl<T0, T1, T2, T3> TryConvert for (T0, T1, T2, T3)
where
    T0: TryConvert,
    T1: TryConvert,
    T2: TryConvert,
    T3: TryConvert,
{
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        debug_assert_value!(val);
        let array = RArray::try_convert(val)?;
        let slice = unsafe { array.as_slice() };
        if slice.len() != 4 {
            return Err(Error::new(
                exception::type_error(),
                "expected Array of length 4",
            ));
        }
        Ok((
            slice[0].try_convert()?,
            slice[1].try_convert()?,
            slice[2].try_convert()?,
            slice[3].try_convert()?,
        ))
    }
}
impl<T0, T1, T2, T3> TryConvertOwned for (T0, T1, T2, T3)
where
    T0: TryConvert,
    T1: TryConvert,
    T2: TryConvert,
    T3: TryConvert,
{
}

impl<T0, T1, T2, T3, T4> TryConvert for (T0, T1, T2, T3, T4)
where
    T0: TryConvert,
    T1: TryConvert,
    T2: TryConvert,
    T3: TryConvert,
    T4: TryConvert,
{
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        debug_assert_value!(val);
        let array = RArray::try_convert(val)?;
        let slice = unsafe { array.as_slice() };
        if slice.len() != 5 {
            return Err(Error::new(
                exception::type_error(),
                "expected Array of length 5",
            ));
        }
        Ok((
            slice[0].try_convert()?,
            slice[1].try_convert()?,
            slice[2].try_convert()?,
            slice[3].try_convert()?,
            slice[4].try_convert()?,
        ))
    }
}
impl<T0, T1, T2, T3, T4> TryConvertOwned for (T0, T1, T2, T3, T4)
where
    T0: TryConvert,
    T1: TryConvert,
    T2: TryConvert,
    T3: TryConvert,
    T4: TryConvert,
{
}

impl<T0, T1, T2, T3, T4, T5> TryConvert for (T0, T1, T2, T3, T4, T5)
where
    T0: TryConvert,
    T1: TryConvert,
    T2: TryConvert,
    T3: TryConvert,
    T4: TryConvert,
    T5: TryConvert,
{
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        debug_assert_value!(val);
        let array = RArray::try_convert(val)?;
        let slice = unsafe { array.as_slice() };
        if slice.len() != 6 {
            return Err(Error::new(
                exception::type_error(),
                "expected Array of length 6",
            ));
        }
        Ok((
            slice[0].try_convert()?,
            slice[1].try_convert()?,
            slice[2].try_convert()?,
            slice[3].try_convert()?,
            slice[4].try_convert()?,
            slice[5].try_convert()?,
        ))
    }
}
impl<T0, T1, T2, T3, T4, T5> TryConvertOwned for (T0, T1, T2, T3, T4, T5)
where
    T0: TryConvert,
    T1: TryConvert,
    T2: TryConvert,
    T3: TryConvert,
    T4: TryConvert,
    T5: TryConvert,
{
}

impl<T0, T1, T2, T3, T4, T5, T6> TryConvert for (T0, T1, T2, T3, T4, T5, T6)
where
    T0: TryConvert,
    T1: TryConvert,
    T2: TryConvert,
    T3: TryConvert,
    T4: TryConvert,
    T5: TryConvert,
    T6: TryConvert,
{
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        debug_assert_value!(val);
        let array = RArray::try_convert(val)?;
        let slice = unsafe { array.as_slice() };
        if slice.len() != 7 {
            return Err(Error::new(
                exception::type_error(),
                "expected Array of length 7",
            ));
        }
        Ok((
            slice[0].try_convert()?,
            slice[1].try_convert()?,
            slice[2].try_convert()?,
            slice[3].try_convert()?,
            slice[4].try_convert()?,
            slice[5].try_convert()?,
            slice[6].try_convert()?,
        ))
    }
}
impl<T0, T1, T2, T3, T4, T5, T6> TryConvertOwned for (T0, T1, T2, T3, T4, T5, T6)
where
    T0: TryConvert,
    T1: TryConvert,
    T2: TryConvert,
    T3: TryConvert,
    T4: TryConvert,
    T5: TryConvert,
    T6: TryConvert,
{
}

impl<T0, T1, T2, T3, T4, T5, T6, T7> TryConvert for (T0, T1, T2, T3, T4, T5, T6, T7)
where
    T0: TryConvert,
    T1: TryConvert,
    T2: TryConvert,
    T3: TryConvert,
    T4: TryConvert,
    T5: TryConvert,
    T6: TryConvert,
    T7: TryConvert,
{
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        debug_assert_value!(val);
        let array = RArray::try_convert(val)?;
        let slice = unsafe { array.as_slice() };
        if slice.len() != 8 {
            return Err(Error::new(
                exception::type_error(),
                "expected Array of length 8",
            ));
        }
        Ok((
            slice[0].try_convert()?,
            slice[1].try_convert()?,
            slice[2].try_convert()?,
            slice[3].try_convert()?,
            slice[4].try_convert()?,
            slice[5].try_convert()?,
            slice[6].try_convert()?,
            slice[7].try_convert()?,
        ))
    }
}
impl<T0, T1, T2, T3, T4, T5, T6, T7> TryConvertOwned for (T0, T1, T2, T3, T4, T5, T6, T7)
where
    T0: TryConvert,
    T1: TryConvert,
    T2: TryConvert,
    T3: TryConvert,
    T4: TryConvert,
    T5: TryConvert,
    T6: TryConvert,
    T7: TryConvert,
{
}

impl<T0, T1, T2, T3, T4, T5, T6, T7, T8> TryConvert for (T0, T1, T2, T3, T4, T5, T6, T7, T8)
where
    T0: TryConvert,
    T1: TryConvert,
    T2: TryConvert,
    T3: TryConvert,
    T4: TryConvert,
    T5: TryConvert,
    T6: TryConvert,
    T7: TryConvert,
    T8: TryConvert,
{
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        debug_assert_value!(val);
        let array = RArray::try_convert(val)?;
        let slice = unsafe { array.as_slice() };
        if slice.len() != 9 {
            return Err(Error::new(
                exception::type_error(),
                "expected Array of length 9",
            ));
        }
        Ok((
            slice[0].try_convert()?,
            slice[1].try_convert()?,
            slice[2].try_convert()?,
            slice[3].try_convert()?,
            slice[4].try_convert()?,
            slice[5].try_convert()?,
            slice[6].try_convert()?,
            slice[7].try_convert()?,
            slice[8].try_convert()?,
        ))
    }
}
impl<T0, T1, T2, T3, T4, T5, T6, T7, T8> TryConvertOwned for (T0, T1, T2, T3, T4, T5, T6, T7, T8)
where
    T0: TryConvert,
    T1: TryConvert,
    T2: TryConvert,
    T3: TryConvert,
    T4: TryConvert,
    T5: TryConvert,
    T6: TryConvert,
    T7: TryConvert,
    T8: TryConvert,
{
}

impl<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> TryConvert for (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9)
where
    T0: TryConvert,
    T1: TryConvert,
    T2: TryConvert,
    T3: TryConvert,
    T4: TryConvert,
    T5: TryConvert,
    T6: TryConvert,
    T7: TryConvert,
    T8: TryConvert,
    T9: TryConvert,
{
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        debug_assert_value!(val);
        let array = RArray::try_convert(val)?;
        let slice = unsafe { array.as_slice() };
        if slice.len() != 10 {
            return Err(Error::new(
                exception::type_error(),
                "expected Array of length 10",
            ));
        }
        Ok((
            slice[0].try_convert()?,
            slice[1].try_convert()?,
            slice[2].try_convert()?,
            slice[3].try_convert()?,
            slice[4].try_convert()?,
            slice[5].try_convert()?,
            slice[6].try_convert()?,
            slice[7].try_convert()?,
            slice[8].try_convert()?,
            slice[9].try_convert()?,
        ))
    }
}
impl<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> TryConvertOwned
    for (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9)
where
    T0: TryConvert,
    T1: TryConvert,
    T2: TryConvert,
    T3: TryConvert,
    T4: TryConvert,
    T5: TryConvert,
    T6: TryConvert,
    T7: TryConvert,
    T8: TryConvert,
    T9: TryConvert,
{
}

impl<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> TryConvert
    for (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10)
where
    T0: TryConvert,
    T1: TryConvert,
    T2: TryConvert,
    T3: TryConvert,
    T4: TryConvert,
    T5: TryConvert,
    T6: TryConvert,
    T7: TryConvert,
    T8: TryConvert,
    T9: TryConvert,
    T10: TryConvert,
{
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        debug_assert_value!(val);
        let array = RArray::try_convert(val)?;
        let slice = unsafe { array.as_slice() };
        if slice.len() != 11 {
            return Err(Error::new(
                exception::type_error(),
                "expected Array of length 11",
            ));
        }
        Ok((
            slice[0].try_convert()?,
            slice[1].try_convert()?,
            slice[2].try_convert()?,
            slice[3].try_convert()?,
            slice[4].try_convert()?,
            slice[5].try_convert()?,
            slice[6].try_convert()?,
            slice[7].try_convert()?,
            slice[8].try_convert()?,
            slice[9].try_convert()?,
            slice[10].try_convert()?,
        ))
    }
}
impl<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> TryConvertOwned
    for (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10)
where
    T0: TryConvert,
    T1: TryConvert,
    T2: TryConvert,
    T3: TryConvert,
    T4: TryConvert,
    T5: TryConvert,
    T6: TryConvert,
    T7: TryConvert,
    T8: TryConvert,
    T9: TryConvert,
    T10: TryConvert,
{
}

impl<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> TryConvert
    for (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11)
where
    T0: TryConvert,
    T1: TryConvert,
    T2: TryConvert,
    T3: TryConvert,
    T4: TryConvert,
    T5: TryConvert,
    T6: TryConvert,
    T7: TryConvert,
    T8: TryConvert,
    T9: TryConvert,
    T10: TryConvert,
    T11: TryConvert,
{
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        debug_assert_value!(val);
        let array = RArray::try_convert(val)?;
        let slice = unsafe { array.as_slice() };
        if slice.len() != 12 {
            return Err(Error::new(
                exception::type_error(),
                "expected Array of length 12",
            ));
        }
        Ok((
            slice[0].try_convert()?,
            slice[1].try_convert()?,
            slice[2].try_convert()?,
            slice[3].try_convert()?,
            slice[4].try_convert()?,
            slice[5].try_convert()?,
            slice[6].try_convert()?,
            slice[7].try_convert()?,
            slice[8].try_convert()?,
            slice[9].try_convert()?,
            slice[10].try_convert()?,
            slice[11].try_convert()?,
        ))
    }
}
impl<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> TryConvertOwned
    for (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11)
where
    T0: TryConvert,
    T1: TryConvert,
    T2: TryConvert,
    T3: TryConvert,
    T4: TryConvert,
    T5: TryConvert,
    T6: TryConvert,
    T7: TryConvert,
    T8: TryConvert,
    T9: TryConvert,
    T10: TryConvert,
    T11: TryConvert,
{
}

impl<K, V> TryConvert for std::collections::HashMap<K, V>
where
    K: TryConvertOwned + Eq + std::hash::Hash,
    V: TryConvertOwned,
{
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
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
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        use std::os::unix::ffi::OsStringExt;

        let bytes = unsafe {
            let val = protect(|| Value::new(rb_get_path(val.as_rb_value())))?;
            let r_string = RString::from_rb_value_unchecked(val.as_rb_value());
            r_string.as_slice().to_owned()
        };
        Ok(std::ffi::OsString::from_vec(bytes).into())
    }
}

#[cfg(not(unix))]
impl TryConvert for PathBuf {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        unsafe {
            let val = protect(|| Value::new(rb_get_path(val.as_rb_value())))?;
            RString::from_rb_value_unchecked(val.as_rb_value())
                .to_string()
                .map(Into::into)
        }
    }
}

impl TryConvertOwned for PathBuf {}

/// Trait for types that can be used as an arguments list when calling Ruby
/// methods.
pub trait ArgList {
    /// The type of the arguments list. Must convert to `&[Value]` with
    /// [`AsRef`].
    type Output: AsRef<[Value]>;

    /// Convert `self` into a type that can be used as a Ruby argument list.
    fn into_arg_list(self) -> Self::Output;
}

impl<'a> ArgList for &'a [Value] {
    type Output = &'a [Value];

    fn into_arg_list(self) -> Self::Output {
        self
    }
}

impl ArgList for () {
    type Output = [Value; 0];

    fn into_arg_list(self) -> Self::Output {
        []
    }
}

impl<A> ArgList for (A,)
where
    A: Into<Value>,
{
    type Output = [Value; 1];

    fn into_arg_list(self) -> Self::Output {
        [self.0.into()]
    }
}

impl<A, B> ArgList for (A, B)
where
    A: Into<Value>,
    B: Into<Value>,
{
    type Output = [Value; 2];

    fn into_arg_list(self) -> Self::Output {
        [self.0.into(), self.1.into()]
    }
}

impl<A, B, C> ArgList for (A, B, C)
where
    A: Into<Value>,
    B: Into<Value>,
    C: Into<Value>,
{
    type Output = [Value; 3];

    fn into_arg_list(self) -> Self::Output {
        [self.0.into(), self.1.into(), self.2.into()]
    }
}

impl<A, B, C, D> ArgList for (A, B, C, D)
where
    A: Into<Value>,
    B: Into<Value>,
    C: Into<Value>,
    D: Into<Value>,
{
    type Output = [Value; 4];

    fn into_arg_list(self) -> Self::Output {
        [self.0.into(), self.1.into(), self.2.into(), self.3.into()]
    }
}

impl<A, B, C, D, E> ArgList for (A, B, C, D, E)
where
    A: Into<Value>,
    B: Into<Value>,
    C: Into<Value>,
    D: Into<Value>,
    E: Into<Value>,
{
    type Output = [Value; 5];

    fn into_arg_list(self) -> Self::Output {
        [
            self.0.into(),
            self.1.into(),
            self.2.into(),
            self.3.into(),
            self.4.into(),
        ]
    }
}

impl<A, B, C, D, E, F> ArgList for (A, B, C, D, E, F)
where
    A: Into<Value>,
    B: Into<Value>,
    C: Into<Value>,
    D: Into<Value>,
    E: Into<Value>,
    F: Into<Value>,
{
    type Output = [Value; 6];

    fn into_arg_list(self) -> Self::Output {
        [
            self.0.into(),
            self.1.into(),
            self.2.into(),
            self.3.into(),
            self.4.into(),
            self.5.into(),
        ]
    }
}

impl<A, B, C, D, E, F, G> ArgList for (A, B, C, D, E, F, G)
where
    A: Into<Value>,
    B: Into<Value>,
    C: Into<Value>,
    D: Into<Value>,
    E: Into<Value>,
    F: Into<Value>,
    G: Into<Value>,
{
    type Output = [Value; 7];

    fn into_arg_list(self) -> Self::Output {
        [
            self.0.into(),
            self.1.into(),
            self.2.into(),
            self.3.into(),
            self.4.into(),
            self.5.into(),
            self.6.into(),
        ]
    }
}

impl<A, B, C, D, E, F, G, H> ArgList for (A, B, C, D, E, F, G, H)
where
    A: Into<Value>,
    B: Into<Value>,
    C: Into<Value>,
    D: Into<Value>,
    E: Into<Value>,
    F: Into<Value>,
    G: Into<Value>,
    H: Into<Value>,
{
    type Output = [Value; 8];

    fn into_arg_list(self) -> Self::Output {
        [
            self.0.into(),
            self.1.into(),
            self.2.into(),
            self.3.into(),
            self.4.into(),
            self.5.into(),
            self.6.into(),
            self.7.into(),
        ]
    }
}

impl<A, B, C, D, E, F, G, H, I> ArgList for (A, B, C, D, E, F, G, H, I)
where
    A: Into<Value>,
    B: Into<Value>,
    C: Into<Value>,
    D: Into<Value>,
    E: Into<Value>,
    F: Into<Value>,
    G: Into<Value>,
    H: Into<Value>,
    I: Into<Value>,
{
    type Output = [Value; 9];

    fn into_arg_list(self) -> Self::Output {
        [
            self.0.into(),
            self.1.into(),
            self.2.into(),
            self.3.into(),
            self.4.into(),
            self.5.into(),
            self.6.into(),
            self.7.into(),
            self.8.into(),
        ]
    }
}

impl<A, B, C, D, E, F, G, H, I, J> ArgList for (A, B, C, D, E, F, G, H, I, J)
where
    A: Into<Value>,
    B: Into<Value>,
    C: Into<Value>,
    D: Into<Value>,
    E: Into<Value>,
    F: Into<Value>,
    G: Into<Value>,
    H: Into<Value>,
    I: Into<Value>,
    J: Into<Value>,
{
    type Output = [Value; 10];

    fn into_arg_list(self) -> Self::Output {
        [
            self.0.into(),
            self.1.into(),
            self.2.into(),
            self.3.into(),
            self.4.into(),
            self.5.into(),
            self.6.into(),
            self.7.into(),
            self.8.into(),
            self.9.into(),
        ]
    }
}

impl<A, B, C, D, E, F, G, H, I, J, K> ArgList for (A, B, C, D, E, F, G, H, I, J, K)
where
    A: Into<Value>,
    B: Into<Value>,
    C: Into<Value>,
    D: Into<Value>,
    E: Into<Value>,
    F: Into<Value>,
    G: Into<Value>,
    H: Into<Value>,
    I: Into<Value>,
    J: Into<Value>,
    K: Into<Value>,
{
    type Output = [Value; 11];

    fn into_arg_list(self) -> Self::Output {
        [
            self.0.into(),
            self.1.into(),
            self.2.into(),
            self.3.into(),
            self.4.into(),
            self.5.into(),
            self.6.into(),
            self.7.into(),
            self.8.into(),
            self.9.into(),
            self.10.into(),
        ]
    }
}

impl<A, B, C, D, E, F, G, H, I, J, K, L> ArgList for (A, B, C, D, E, F, G, H, I, J, K, L)
where
    A: Into<Value>,
    B: Into<Value>,
    C: Into<Value>,
    D: Into<Value>,
    E: Into<Value>,
    F: Into<Value>,
    G: Into<Value>,
    H: Into<Value>,
    I: Into<Value>,
    J: Into<Value>,
    K: Into<Value>,
    L: Into<Value>,
{
    type Output = [Value; 12];

    fn into_arg_list(self) -> Self::Output {
        [
            self.0.into(),
            self.1.into(),
            self.2.into(),
            self.3.into(),
            self.4.into(),
            self.5.into(),
            self.6.into(),
            self.7.into(),
            self.8.into(),
            self.9.into(),
            self.10.into(),
            self.11.into(),
        ]
    }
}

impl<const N: usize> ArgList for [Value; N] {
    type Output = [Value; N];

    fn into_arg_list(self) -> Self::Output {
        self
    }
}

pub trait RArrayArgList {
    fn into_array_arg_list(self) -> RArray;
}

impl RArrayArgList for RArray {
    fn into_array_arg_list(self) -> RArray {
        self
    }
}

impl<T> RArrayArgList for T
where
    T: ArgList,
{
    fn into_array_arg_list(self) -> RArray {
        RArray::from_slice(self.into_arg_list().as_ref())
    }
}
