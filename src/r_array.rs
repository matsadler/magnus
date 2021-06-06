use std::{fmt, ops::Deref, os::raw::c_long};

use crate::{
    debug_assert_value,
    enumerator::Enumerator,
    error::{protect, Error},
    object::Object,
    ruby_sys::{
        rb_ary_cat, rb_ary_new, rb_ary_new_capa, rb_ary_push, rb_ary_to_ary, ruby_value_type, VALUE,
    },
    try_convert::TryConvert,
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

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        Self(NonZeroValue::new_unchecked(Value::new(val)))
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
