use std::{fmt, ops::Deref};

use crate::{
    error::Error,
    object::Object,
    ruby_sys::ruby_value_type,
    try_convert::TryConvert,
    value::{NonZeroValue, Value},
};

/// A Value pointer to a RObject struct, Ruby's internal representation of
/// generic objects, not covered by the other R* types.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RObject(NonZeroValue);

impl RObject {
    /// Return `Some(RObject)` if `val` is a `RObject`, `None` otherwise.
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            (val.rb_type() == ruby_value_type::RUBY_T_OBJECT)
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }
}

impl Deref for RObject {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
    }
}

impl fmt::Display for RObject {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for RObject {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl From<RObject> for Value {
    fn from(val: RObject) -> Self {
        *val
    }
}

impl Object for RObject {}

impl TryConvert for RObject {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        Self::from_value(*val).ok_or_else(|| {
            Error::type_error(format!(
                "no implicit conversion of {} into Object",
                unsafe { val.classname() },
            ))
        })
    }
}
