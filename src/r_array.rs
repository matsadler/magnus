use std::{fmt, ops::Deref, ptr::NonNull};

use crate::{
    debug_assert_value,
    enumerator::Enumerator,
    error::{protect, Error},
    object::Object,
    r_basic::RBasic,
    ruby_sys::{self, rb_ary_to_ary, ruby_value_type, VALUE},
    try_convert::TryConvert,
    value::Value,
};

#[repr(transparent)]
pub struct RArray(VALUE);

impl RArray {
    /// # Safety
    ///
    /// val must not have been GC'd, return value must be kept on stack or
    /// otherwise protected from the GC.
    pub unsafe fn from_value(val: &Value) -> Option<Self> {
        let r_basic = RBasic::from_value(val)?;
        (r_basic.builtin_type() == ruby_value_type::RUBY_T_ARRAY).then(|| Self(val.into_inner()))
    }

    // TODO: use or remove
    #[allow(dead_code)]
    pub(crate) fn as_internal(&self) -> NonNull<ruby_sys::RArray> {
        // safe as to get self we need to have gone through ::from_value()
        // where val is vaild as an RBasic, which rules out NULL
        unsafe { NonNull::new_unchecked(self.0 as *mut _) }
    }

    pub unsafe fn each(&self) -> Enumerator {
        // TODO why doesn't rb_ary_each work?
        self.enumeratorize("each", ())
    }
}

impl Deref for RArray {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        let self_ptr = self as *const Self;
        let value_ptr = self_ptr as *const Self::Target;
        // we just got this pointer from &self, so we know it's valid to deref
        unsafe { &*value_ptr }
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

impl TryConvert<'_> for RArray {
    unsafe fn try_convert(val: &Value) -> Result<Self, Error> {
        match Self::from_value(&val) {
            Some(i) => Ok(i),
            None => protect(|| {
                debug_assert_value!(val);
                Value::new(rb_ary_to_ary(val.into_inner()))
            })
            .map(|res| Self(res.into_inner())),
        }
    }
}
