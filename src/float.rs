use std::ops::Deref;

use crate::{
    debug_assert_value,
    error::Error,
    protect,
    r_basic::RBasic,
    ruby_sys::{
        rb_float_new, rb_float_value, rb_to_float, ruby_special_consts, ruby_value_type, VALUE,
    },
    try_convert::TryConvert,
    value::Value,
};

#[repr(transparent)]
pub struct Float(VALUE);

impl Float {
    /// # Safety
    ///
    /// val must not have been GC'd, return value must be kept on stack or
    /// otherwise protected from the GC.
    pub unsafe fn from_value(val: &Value) -> Option<Self> {
        if val.into_inner() & ruby_special_consts::RUBY_FLONUM_MASK as VALUE
            == ruby_special_consts::RUBY_FLONUM_FLAG as VALUE
        {
            return Some(Self(val.into_inner()));
        }
        debug_assert_value!(val);
        let r_basic = RBasic::from_value(val)?;
        (r_basic.builtin_type() == ruby_value_type::RUBY_T_FLOAT).then(|| Self(val.into_inner()))
    }

    pub fn from_f64(n: f64) -> Self {
        unsafe { Float(rb_float_new(n)) }
    }

    /// # Safety
    ///
    /// self must not have been GC'd.
    pub unsafe fn to_f64(&self) -> f64 {
        rb_float_value(self.into_inner())
    }
}

impl Deref for Float {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        let self_ptr = self as *const Self;
        let value_ptr = self_ptr as *const Self::Target;
        // we just got this pointer from &self, so we know it's valid to deref
        unsafe { &*value_ptr }
    }
}

impl From<Float> for Value {
    fn from(val: Float) -> Self {
        *val
    }
}

impl TryConvert<'_> for Float {
    unsafe fn try_convert(val: &Value) -> Result<Self, Error> {
        match Self::from_value(&val) {
            Some(i) => Ok(i),
            None => protect(|| {
                debug_assert_value!(val);
                Value::new(rb_to_float(val.into_inner()))
            })
            .map(|res| Self(res.into_inner())),
        }
    }
}
