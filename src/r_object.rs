use std::fmt;

use rb_sys::ruby_value_type;

use crate::{
    error::Error,
    exception,
    into_value::IntoValue,
    object::Object,
    ruby_handle::RubyHandle,
    try_convert::TryConvert,
    value::{
        private::{self, ReprValue as _},
        NonZeroValue, ReprValue, Value,
    },
};

/// A Value pointer to a RObject struct, Ruby's internal representation of
/// generic objects, not covered by the other R* types.
///
/// See the [`ReprValue`] and [`Object`] traits for additional methods
/// available on this type.
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

impl IntoValue for RObject {
    fn into_value_with(self, _: &RubyHandle) -> Value {
        self.0.get()
    }
}

impl Object for RObject {}

unsafe impl private::ReprValue for RObject {}

impl ReprValue for RObject {}

impl TryConvert for RObject {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Self::from_value(val).ok_or_else(|| {
            Error::new(
                exception::type_error(),
                format!("no implicit conversion of {} into Object", unsafe {
                    val.classname()
                },),
            )
        })
    }
}
