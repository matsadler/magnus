use crate::{
    debug_assert_value,
    error::{protect, Error},
    integer::Integer,
    r_string::RString,
    ruby_sys::rb_num2dbl,
    value::{Qnil, Value},
};

pub trait TryConvert: Sized {
    /// # Safety
    ///
    /// unsafe as typically val must be dereferenced to perform the conversion
    unsafe fn try_convert(val: &Value) -> Result<Self, Error>;
}

/// Only implemented on Rust types. TryConvert may convert from a
/// Value to another Ruby type. Use this when you need a Rust value that's
/// divorced from the Ruby runtime, safe to put on the heap, etc.
pub trait TryConvertToRust: TryConvert {
    /// # Safety
    ///
    /// unsafe as typically val must be dereferenced to perform the conversion
    #[inline]
    unsafe fn try_convert_to_rust(val: &Value) -> Result<Self, Error> {
        Self::try_convert(val)
    }
}

impl TryConvert for Value {
    #[inline]
    unsafe fn try_convert(val: &Value) -> Result<Self, Error> {
        Ok(*val)
    }
}

impl<T> TryConvert for Option<T>
where
    T: TryConvert,
{
    #[inline]
    unsafe fn try_convert(val: &Value) -> Result<Self, Error> {
        (!val.is_nil()).then(|| T::try_convert(val)).transpose()
    }
}

impl<T> TryConvertToRust for Option<T>
where
    T: TryConvertToRust,
{
    #[inline]
    unsafe fn try_convert_to_rust(val: &Value) -> Result<Self, Error> {
        (!val.is_nil())
            .then(|| T::try_convert_to_rust(val))
            .transpose()
    }
}

impl TryConvert for bool {
    #[inline]
    unsafe fn try_convert(val: &Value) -> Result<Self, Error> {
        Ok(val.to_bool())
    }
}
impl TryConvertToRust for bool {}

impl TryConvert for i8 {
    #[inline]
    unsafe fn try_convert(val: &Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_i8()
    }
}
impl TryConvertToRust for i8 {}

impl TryConvert for i16 {
    #[inline]
    unsafe fn try_convert(val: &Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_i16()
    }
}
impl TryConvertToRust for i16 {}

impl TryConvert for i32 {
    #[inline]
    unsafe fn try_convert(val: &Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_i32()
    }
}
impl TryConvertToRust for i32 {}

impl TryConvert for i64 {
    #[inline]
    unsafe fn try_convert(val: &Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_i64()
    }
}
impl TryConvertToRust for i64 {}

impl TryConvert for isize {
    #[inline]
    unsafe fn try_convert(val: &Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_isize()
    }
}
impl TryConvertToRust for isize {}

impl TryConvert for u8 {
    #[inline]
    unsafe fn try_convert(val: &Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_u8()
    }
}
impl TryConvertToRust for u8 {}

impl TryConvert for u16 {
    #[inline]
    unsafe fn try_convert(val: &Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_u16()
    }
}
impl TryConvertToRust for u16 {}

impl TryConvert for u32 {
    #[inline]
    unsafe fn try_convert(val: &Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_u32()
    }
}
impl TryConvertToRust for u32 {}

impl TryConvert for u64 {
    #[inline]
    unsafe fn try_convert(val: &Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_u64()
    }
}
impl TryConvertToRust for u64 {}

impl TryConvert for usize {
    #[inline]
    unsafe fn try_convert(val: &Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_usize()
    }
}
impl TryConvertToRust for usize {}

impl TryConvert for f32 {
    #[inline]
    unsafe fn try_convert(val: &Value) -> Result<Self, Error> {
        f64::try_convert(val).map(|f| f as f32)
    }
}
impl TryConvertToRust for f32 {}

impl TryConvert for f64 {
    #[inline]
    unsafe fn try_convert(val: &Value) -> Result<Self, Error> {
        debug_assert_value!(val);
        let mut res = 0.0;
        protect(|| {
            res = rb_num2dbl(val.as_rb_value());
            *Qnil::new()
        })?;
        Ok(res)
    }
}
impl TryConvertToRust for f64 {}

impl TryConvert for String {
    #[inline]
    unsafe fn try_convert(val: &Value) -> Result<Self, Error> {
        debug_assert_value!(val);
        RString::try_convert(val)?.to_string()
    }
}
impl TryConvertToRust for String {}

impl TryConvert for &str {
    #[inline]
    unsafe fn try_convert(val: &Value) -> Result<Self, Error> {
        debug_assert_value!(val);
        RString::from_value(*val)
            .ok_or_else(|| Error::type_error(format!("expected String, got {}", val.classname())))?
            .as_str_unconstrained()
    }
}

pub trait ArgList {
    type Output: AsRef<[Value]>;

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
