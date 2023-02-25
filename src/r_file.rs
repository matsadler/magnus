use std::fmt;

use rb_sys::ruby_value_type;

use crate::{
    error::Error,
    exception,
    into_value::IntoValue,
    object::Object,
    try_convert::TryConvert,
    value::{
        private::{self, ReprValue as _},
        NonZeroValue, ReprValue, Value,
    },
    Ruby,
};

/// A Value pointer to a RFile struct, Ruby's internal representation of files.
///
/// See the [`ReprValue`] and [`Object`] traits for additional methods
/// available on this type.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RFile(NonZeroValue);

impl RFile {
    /// Return `Some(RFile)` if `val` is a `RFile`, `None` otherwise.
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            (val.rb_type() == ruby_value_type::RUBY_T_FILE)
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }
}

impl fmt::Display for RFile {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for RFile {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl IntoValue for RFile {
    fn into_value_with(self, _: &Ruby) -> Value {
        self.0.get()
    }
}

impl Object for RFile {}

unsafe impl private::ReprValue for RFile {}

impl ReprValue for RFile {}

impl TryConvert for RFile {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Self::from_value(val).ok_or_else(|| {
            Error::new(
                exception::type_error(),
                format!("no implicit conversion of {} into File", unsafe {
                    val.classname()
                },),
            )
        })
    }
}
