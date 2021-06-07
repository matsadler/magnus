use std::{
    convert::TryInto, fmt, iter::FromIterator, ops::Deref, os::raw::c_long, ptr::NonNull, slice,
};

use crate::{
    debug_assert_value,
    enumerator::Enumerator,
    error::{protect, Error},
    object::Object,
    ruby_sys::{
        self, rb_ary_cat, rb_ary_entry, rb_ary_new, rb_ary_new_capa, rb_ary_pop, rb_ary_push,
        rb_ary_shift, rb_ary_store, rb_ary_to_ary, rb_ary_unshift, ruby_rarray_consts,
        ruby_rarray_flags, ruby_value_type, VALUE,
    },
    try_convert::{TryConvert, TryConvertOwned},
    value::{NonZeroValue, Value},
};

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RArray(NonZeroValue);

impl RArray {
    /// # Safety
    ///
    /// val must not have been GC'd, return value must be kept on stack or
    /// otherwise protected from the GC.
    #[inline]
    pub unsafe fn from_value(val: Value) -> Option<Self> {
        (val.rb_type() == ruby_value_type::RUBY_T_ARRAY)
            .then(|| Self(NonZeroValue::new_unchecked(val)))
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        Self(NonZeroValue::new_unchecked(Value::new(val)))
    }

    fn as_internal(self) -> NonNull<ruby_sys::RArray> {
        // safe as inner value is NonZero
        unsafe { NonNull::new_unchecked(self.0.get().as_rb_value() as *mut _) }
    }

    pub fn new() -> Self {
        unsafe { Self::from_rb_value_unchecked(rb_ary_new()) }
    }

    pub fn with_capacity(n: usize) -> Self {
        unsafe { Self::from_rb_value_unchecked(rb_ary_new_capa(n as c_long)) }
    }

    pub fn cat(self, s: &[Value]) {
        let ptr = s.as_ptr() as *const VALUE;
        unsafe { rb_ary_cat(self.as_rb_value(), ptr, s.len() as c_long) };
    }

    pub fn from_slice(slice: &[Value]) -> Self {
        let ary = Self::with_capacity(slice.len());
        ary.cat(slice);
        ary
    }

    pub fn push<T>(self, item: T)
    where
        T: Into<Value>,
    {
        unsafe { rb_ary_push(self.as_rb_value(), item.into().as_rb_value()) };
    }

    pub fn pop<T>(self) -> Result<T, Error>
    where
        T: TryConvert,
    {
        unsafe { Value::new(rb_ary_pop(self.as_rb_value())).try_convert() }
    }

    pub fn unshift<T>(self, item: T)
    where
        T: Into<Value>,
    {
        unsafe { rb_ary_unshift(self.as_rb_value(), item.into().as_rb_value()) };
    }

    pub fn shift<T>(self) -> Result<T, Error>
    where
        T: TryConvert,
    {
        unsafe { Value::new(rb_ary_shift(self.as_rb_value())).try_convert() }
    }

    pub fn from_vec<T>(vec: Vec<T>) -> Self
    where
        T: Into<Value>,
    {
        let ary = Self::with_capacity(vec.len());
        for v in vec {
            ary.push(v);
        }
        ary
    }

    pub fn as_slice(&self) -> &[Value] {
        unsafe { self.as_slice_unconstrained() }
    }

    pub(crate) unsafe fn as_slice_unconstrained<'a>(self) -> &'a [Value] {
        debug_assert_value!(self);
        let r_basic = self.r_basic_unchecked();
        let flags = r_basic.as_ref().flags;
        if (flags & ruby_rarray_flags::RARRAY_EMBED_FLAG as VALUE) != 0 {
            let len = (flags >> ruby_rarray_consts::RARRAY_EMBED_LEN_SHIFT as VALUE)
                & (ruby_rarray_flags::RARRAY_EMBED_LEN_MASK as VALUE
                    >> ruby_rarray_consts::RARRAY_EMBED_LEN_SHIFT as VALUE);
            slice::from_raw_parts(
                &self.as_internal().as_ref().as_.ary as *const VALUE as *const Value,
                len as usize,
            )
        } else {
            let h = self.as_internal().as_ref().as_.heap;
            slice::from_raw_parts(h.ptr as *const Value, h.len as usize)
        }
    }

    pub fn to_vec<T>(self) -> Result<Vec<T>, Error>
    where
        T: TryConvertOwned,
    {
        unsafe {
            self.as_slice()
                .iter()
                .map(|v| T::try_convert_owned(*v))
                .collect()
        }
    }

    pub fn to_array<T, const N: usize>(self) -> Result<[T; N], Error>
    where
        T: TryConvert,
    {
        let slice = self.as_slice();
        if slice.len() != N {
            return Err(Error::type_error(format!("expected Array of length {}", N)));
        }
        unsafe {
            // one day might be able to collect direct into an array, but for
            // now need to go via Vec
            slice
                .iter()
                .map(|v| v.try_convert())
                .collect::<Result<Vec<T>, Error>>()
                .map(|v| v.try_into().ok().unwrap())
        }
    }

    pub fn entry<T>(self, offset: isize) -> Result<T, Error>
    where
        T: TryConvert,
    {
        unsafe { Value::new(rb_ary_entry(self.as_rb_value(), offset as c_long)).try_convert() }
    }

    pub fn store<T>(self, offset: isize, val: T)
    where
        T: Into<Value>,
    {
        unsafe {
            rb_ary_store(
                self.as_rb_value(),
                offset as c_long,
                val.into().as_rb_value(),
            );
        }
    }

    pub unsafe fn each(self) -> Enumerator {
        // TODO why doesn't rb_ary_each work?
        self.enumeratorize("each", ())
    }
}

impl Deref for RArray {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
    }
}

impl fmt::Display for RArray {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for RArray {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.inspect() })
    }
}

impl From<RArray> for Value {
    fn from(val: RArray) -> Self {
        *val
    }
}

impl<T0> From<(T0,)> for Value
where
    T0: Into<Value>,
{
    fn from(val: (T0,)) -> Self {
        let ary = [val.0.into()];
        RArray::from_slice(&ary).into()
    }
}

impl<T0, T1> From<(T0, T1)> for Value
where
    T0: Into<Value>,
    T1: Into<Value>,
{
    fn from(val: (T0, T1)) -> Self {
        let ary = [val.0.into(), val.1.into()];
        RArray::from_slice(&ary).into()
    }
}

impl<T0, T1, T2> From<(T0, T1, T2)> for Value
where
    T0: Into<Value>,
    T1: Into<Value>,
    T2: Into<Value>,
{
    fn from(val: (T0, T1, T2)) -> Self {
        let ary = [val.0.into(), val.1.into(), val.2.into()];
        RArray::from_slice(&ary).into()
    }
}

impl<T0, T1, T2, T3> From<(T0, T1, T2, T3)> for Value
where
    T0: Into<Value>,
    T1: Into<Value>,
    T2: Into<Value>,
    T3: Into<Value>,
{
    fn from(val: (T0, T1, T2, T3)) -> Self {
        let ary = [val.0.into(), val.1.into(), val.2.into(), val.3.into()];
        RArray::from_slice(&ary).into()
    }
}

impl<T0, T1, T2, T3, T4> From<(T0, T1, T2, T3, T4)> for Value
where
    T0: Into<Value>,
    T1: Into<Value>,
    T2: Into<Value>,
    T3: Into<Value>,
    T4: Into<Value>,
{
    fn from(val: (T0, T1, T2, T3, T4)) -> Self {
        let ary = [
            val.0.into(),
            val.1.into(),
            val.2.into(),
            val.3.into(),
            val.4.into(),
        ];
        RArray::from_slice(&ary).into()
    }
}

impl<T0, T1, T2, T3, T4, T5> From<(T0, T1, T2, T3, T4, T5)> for Value
where
    T0: Into<Value>,
    T1: Into<Value>,
    T2: Into<Value>,
    T3: Into<Value>,
    T4: Into<Value>,
    T5: Into<Value>,
{
    fn from(val: (T0, T1, T2, T3, T4, T5)) -> Self {
        let ary = [
            val.0.into(),
            val.1.into(),
            val.2.into(),
            val.3.into(),
            val.4.into(),
            val.5.into(),
        ];
        RArray::from_slice(&ary).into()
    }
}

impl<T0, T1, T2, T3, T4, T5, T6> From<(T0, T1, T2, T3, T4, T5, T6)> for Value
where
    T0: Into<Value>,
    T1: Into<Value>,
    T2: Into<Value>,
    T3: Into<Value>,
    T4: Into<Value>,
    T5: Into<Value>,
    T6: Into<Value>,
{
    fn from(val: (T0, T1, T2, T3, T4, T5, T6)) -> Self {
        let ary = [
            val.0.into(),
            val.1.into(),
            val.2.into(),
            val.3.into(),
            val.4.into(),
            val.5.into(),
            val.6.into(),
        ];
        RArray::from_slice(&ary).into()
    }
}

impl<T0, T1, T2, T3, T4, T5, T6, T7> From<(T0, T1, T2, T3, T4, T5, T6, T7)> for Value
where
    T0: Into<Value>,
    T1: Into<Value>,
    T2: Into<Value>,
    T3: Into<Value>,
    T4: Into<Value>,
    T5: Into<Value>,
    T6: Into<Value>,
    T7: Into<Value>,
{
    fn from(val: (T0, T1, T2, T3, T4, T5, T6, T7)) -> Self {
        let ary = [
            val.0.into(),
            val.1.into(),
            val.2.into(),
            val.3.into(),
            val.4.into(),
            val.5.into(),
            val.6.into(),
            val.7.into(),
        ];
        RArray::from_slice(&ary).into()
    }
}

impl<T0, T1, T2, T3, T4, T5, T6, T7, T8> From<(T0, T1, T2, T3, T4, T5, T6, T7, T8)> for Value
where
    T0: Into<Value>,
    T1: Into<Value>,
    T2: Into<Value>,
    T3: Into<Value>,
    T4: Into<Value>,
    T5: Into<Value>,
    T6: Into<Value>,
    T7: Into<Value>,
    T8: Into<Value>,
{
    fn from(val: (T0, T1, T2, T3, T4, T5, T6, T7, T8)) -> Self {
        let ary = [
            val.0.into(),
            val.1.into(),
            val.2.into(),
            val.3.into(),
            val.4.into(),
            val.5.into(),
            val.6.into(),
            val.7.into(),
            val.8.into(),
        ];
        RArray::from_slice(&ary).into()
    }
}

impl<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> From<(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9)>
    for Value
where
    T0: Into<Value>,
    T1: Into<Value>,
    T2: Into<Value>,
    T3: Into<Value>,
    T4: Into<Value>,
    T5: Into<Value>,
    T6: Into<Value>,
    T7: Into<Value>,
    T8: Into<Value>,
    T9: Into<Value>,
{
    fn from(val: (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9)) -> Self {
        let ary = [
            val.0.into(),
            val.1.into(),
            val.2.into(),
            val.3.into(),
            val.4.into(),
            val.5.into(),
            val.6.into(),
            val.7.into(),
            val.8.into(),
            val.9.into(),
        ];
        RArray::from_slice(&ary).into()
    }
}

impl<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>
    From<(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10)> for Value
where
    T0: Into<Value>,
    T1: Into<Value>,
    T2: Into<Value>,
    T3: Into<Value>,
    T4: Into<Value>,
    T5: Into<Value>,
    T6: Into<Value>,
    T7: Into<Value>,
    T8: Into<Value>,
    T9: Into<Value>,
    T10: Into<Value>,
{
    fn from(val: (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10)) -> Self {
        let ary = [
            val.0.into(),
            val.1.into(),
            val.2.into(),
            val.3.into(),
            val.4.into(),
            val.5.into(),
            val.6.into(),
            val.7.into(),
            val.8.into(),
            val.9.into(),
            val.10.into(),
        ];
        RArray::from_slice(&ary).into()
    }
}

impl<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>
    From<(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11)> for Value
where
    T0: Into<Value>,
    T1: Into<Value>,
    T2: Into<Value>,
    T3: Into<Value>,
    T4: Into<Value>,
    T5: Into<Value>,
    T6: Into<Value>,
    T7: Into<Value>,
    T8: Into<Value>,
    T9: Into<Value>,
    T10: Into<Value>,
    T11: Into<Value>,
{
    fn from(val: (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11)) -> Self {
        let ary = [
            val.0.into(),
            val.1.into(),
            val.2.into(),
            val.3.into(),
            val.4.into(),
            val.5.into(),
            val.6.into(),
            val.7.into(),
            val.8.into(),
            val.9.into(),
            val.10.into(),
            val.11.into(),
        ];
        RArray::from_slice(&ary).into()
    }
}

impl<T> From<Vec<T>> for Value
where
    T: Into<Value>,
{
    fn from(val: Vec<T>) -> Self {
        RArray::from_vec(val).into()
    }
}

impl<T> FromIterator<T> for RArray
where
    T: Into<Value>,
{
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        let iter = iter.into_iter();
        let (lower, _) = iter.size_hint();
        let array = if lower > 0 {
            RArray::with_capacity(lower)
        } else {
            RArray::new()
        };
        for i in iter {
            array.push(i);
        }
        array
    }
}

impl Object for RArray {}

impl TryConvert for RArray {
    #[inline]
    unsafe fn try_convert(val: &Value) -> Result<Self, Error> {
        match Self::from_value(*val) {
            Some(i) => Ok(i),
            None => protect(|| {
                debug_assert_value!(val);
                Value::new(rb_ary_to_ary(val.as_rb_value()))
            })
            .map(|res| Self::from_rb_value_unchecked(res.as_rb_value())),
        }
    }
}
