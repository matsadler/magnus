use crate::{
    debug_assert_value,
    error::{protect, Error},
    integer::Integer,
    r_string::RString,
    ruby_sys::rb_num2dbl,
    value::{Qnil, Value},
};

pub trait TryConvert<'a>: Sized {
    /// # Safety
    ///
    /// unsafe as typically val must be dereferenced to perform the conversion
    unsafe fn try_convert(val: &'a Value) -> Result<Self, Error>;
}

impl Value {
    /// # Safety
    ///
    /// self must not have been GC'd.
    pub unsafe fn try_convert<'a, T>(&'a self) -> Result<T, Error>
    where
        T: TryConvert<'a>,
    {
        T::try_convert(self)
    }
}

/// Only implemented on Rust types. TryConvert may convert from a
/// Value to another Ruby type. Use this when you need a Rust value that's
/// divorced from the Ruby runtime, safe to put on the heap, etc.
pub trait TryConvertToRust<'a>: Sized + TryConvert<'a> {
    /// # Safety
    ///
    /// unsafe as typically val must be dereferenced to perform the conversion
    unsafe fn try_convert_to_rust(val: &'a Value) -> Result<Self, Error> {
        Self::try_convert(val)
    }
}

impl TryConvert<'_> for Value {
    unsafe fn try_convert(val: &Value) -> Result<Self, Error> {
        Ok(*val)
    }
}

impl<'a, T> TryConvert<'a> for Option<T>
where
    T: TryConvert<'a> + 'a,
{
    unsafe fn try_convert(val: &'a Value) -> Result<Self, Error> {
        val.is_nil().then(|| T::try_convert(val)).transpose()
    }
}

impl<'a, T> TryConvertToRust<'a> for Option<T>
where
    T: TryConvertToRust<'a> + 'a,
{
    unsafe fn try_convert_to_rust(val: &'a Value) -> Result<Self, Error> {
        val.is_nil()
            .then(|| T::try_convert_to_rust(val))
            .transpose()
    }
}

impl TryConvert<'_> for bool {
    unsafe fn try_convert(val: &Value) -> Result<Self, Error> {
        Ok(val.to_bool())
    }
}
impl TryConvertToRust<'_> for bool {}

impl TryConvert<'_> for i8 {
    unsafe fn try_convert(val: &Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_i8()
    }
}
impl TryConvertToRust<'_> for i8 {}

impl TryConvert<'_> for i16 {
    unsafe fn try_convert(val: &Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_i16()
    }
}
impl TryConvertToRust<'_> for i16 {}

impl TryConvert<'_> for i32 {
    unsafe fn try_convert(val: &Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_i32()
    }
}
impl TryConvertToRust<'_> for i32 {}

impl TryConvert<'_> for i64 {
    unsafe fn try_convert(val: &Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_i64()
    }
}
impl TryConvertToRust<'_> for i64 {}

impl TryConvert<'_> for isize {
    unsafe fn try_convert(val: &Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_isize()
    }
}
impl TryConvertToRust<'_> for isize {}

impl TryConvert<'_> for u8 {
    unsafe fn try_convert(val: &Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_u8()
    }
}
impl TryConvertToRust<'_> for u8 {}

impl TryConvert<'_> for u16 {
    unsafe fn try_convert(val: &Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_u16()
    }
}
impl TryConvertToRust<'_> for u16 {}

impl TryConvert<'_> for u32 {
    unsafe fn try_convert(val: &Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_u32()
    }
}
impl TryConvertToRust<'_> for u32 {}

impl TryConvert<'_> for u64 {
    unsafe fn try_convert(val: &Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_u64()
    }
}
impl TryConvertToRust<'_> for u64 {}

impl TryConvert<'_> for usize {
    unsafe fn try_convert(val: &Value) -> Result<Self, Error> {
        Integer::try_convert(val)?.to_usize()
    }
}
impl TryConvertToRust<'_> for usize {}

impl TryConvert<'_> for f32 {
    unsafe fn try_convert(val: &Value) -> Result<Self, Error> {
        f64::try_convert(val).map(|f| f as f32)
    }
}
impl TryConvertToRust<'_> for f32 {}

impl TryConvert<'_> for f64 {
    unsafe fn try_convert(val: &Value) -> Result<Self, Error> {
        debug_assert_value!(val);
        let mut res = 0.0;
        protect(|| {
            res = rb_num2dbl(val.into_inner());
            *Qnil::new()
        })?;
        Ok(res)
    }
}
impl TryConvertToRust<'_> for f64 {}

impl TryConvert<'_> for String {
    unsafe fn try_convert(val: &Value) -> Result<Self, Error> {
        debug_assert_value!(val);
        RString::try_convert(val)?.to_string()
    }
}
impl TryConvertToRust<'_> for String {}

impl<'a> TryConvert<'a> for &'a str {
    unsafe fn try_convert(val: &'a Value) -> Result<Self, Error> {
        debug_assert_value!(val);
        RString::ref_from_value(val)
            .ok_or_else(|| Error::type_error(format!("expected String, got {}", val.classname())))?
            .as_str()
    }
}

pub trait ValueArray {
    type Output: AsRef<[Value]>;

    fn into(self) -> Self::Output;
}

impl ValueArray for () {
    type Output = [Value; 0];

    fn into(self) -> Self::Output {
        []
    }
}

impl<A> ValueArray for (A,)
where
    A: Into<Value>,
{
    type Output = [Value; 1];

    fn into(self) -> Self::Output {
        [self.0.into()]
    }
}

impl<A, B> ValueArray for (A, B)
where
    A: Into<Value>,
    B: Into<Value>,
{
    type Output = [Value; 2];

    fn into(self) -> Self::Output {
        [self.0.into(), self.1.into()]
    }
}

impl<A, B, C> ValueArray for (A, B, C)
where
    A: Into<Value>,
    B: Into<Value>,
    C: Into<Value>,
{
    type Output = [Value; 3];

    fn into(self) -> Self::Output {
        [self.0.into(), self.1.into(), self.2.into()]
    }
}

impl<A, B, C, D> ValueArray for (A, B, C, D)
where
    A: Into<Value>,
    B: Into<Value>,
    C: Into<Value>,
    D: Into<Value>,
{
    type Output = [Value; 4];

    fn into(self) -> Self::Output {
        [self.0.into(), self.1.into(), self.2.into(), self.3.into()]
    }
}

impl<A, B, C, D, E> ValueArray for (A, B, C, D, E)
where
    A: Into<Value>,
    B: Into<Value>,
    C: Into<Value>,
    D: Into<Value>,
    E: Into<Value>,
{
    type Output = [Value; 5];

    fn into(self) -> Self::Output {
        [
            self.0.into(),
            self.1.into(),
            self.2.into(),
            self.3.into(),
            self.4.into(),
        ]
    }
}

impl<A, B, C, D, E, F> ValueArray for (A, B, C, D, E, F)
where
    A: Into<Value>,
    B: Into<Value>,
    C: Into<Value>,
    D: Into<Value>,
    E: Into<Value>,
    F: Into<Value>,
{
    type Output = [Value; 6];

    fn into(self) -> Self::Output {
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

impl<A, B, C, D, E, F, G> ValueArray for (A, B, C, D, E, F, G)
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

    fn into(self) -> Self::Output {
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

impl<A, B, C, D, E, F, G, H> ValueArray for (A, B, C, D, E, F, G, H)
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

    fn into(self) -> Self::Output {
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

impl<A, B, C, D, E, F, G, H, I> ValueArray for (A, B, C, D, E, F, G, H, I)
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

    fn into(self) -> Self::Output {
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

impl<A, B, C, D, E, F, G, H, I, J> ValueArray for (A, B, C, D, E, F, G, H, I, J)
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

    fn into(self) -> Self::Output {
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

impl<A, B, C, D, E, F, G, H, I, J, K> ValueArray for (A, B, C, D, E, F, G, H, I, J, K)
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

    fn into(self) -> Self::Output {
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

impl<A, B, C, D, E, F, G, H, I, J, K, L> ValueArray for (A, B, C, D, E, F, G, H, I, J, K, L)
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

    fn into(self) -> Self::Output {
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

impl<const N: usize> ValueArray for [Value; N] {
    type Output = [Value; N];

    fn into(self) -> Self::Output {
        self
    }
}
