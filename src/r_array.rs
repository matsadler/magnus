use std::{fmt, ops::Deref};

use crate::{
    debug_assert_value,
    enumerator::Enumerator,
    error::{protect, Error},
    object::Object,
    ruby_sys::{rb_ary_to_ary, ruby_value_type, VALUE},
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
    pub unsafe fn from_value(val: Value) -> Option<Self> {
        (val.rb_type() == ruby_value_type::RUBY_T_ARRAY)
            .then(|| Self(NonZeroValue::new_unchecked(val)))
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

impl Object for RArray {}

impl TryConvert for RArray {
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
