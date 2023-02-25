use std::fmt;

use rb_sys::VALUE;

use crate::{
    class,
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

/// Wrapper type for a Value known to be an instance of Ruby's Enumerator class.
///
/// See the [`ReprValue`] and [`Object`] traits for additional methods
/// available on this type.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Enumerator(NonZeroValue);

impl Enumerator {
    /// Return `Some(Enumerator)` if `val` is an `Enumerator`, `None` otherwise.
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            val.is_kind_of(class::enumerator())
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        Self(NonZeroValue::new_unchecked(Value::new(val)))
    }
}

impl Iterator for Enumerator {
    type Item = Result<Value, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.funcall("next", ()) {
            Ok(v) => Some(Ok(v)),
            Err(e) if e.is_kind_of(exception::stop_iteration()) => None,
            Err(e) => Some(Err(e)),
        }
    }
}

impl fmt::Display for Enumerator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for Enumerator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", ReprValue::inspect(*self))
    }
}

impl IntoValue for Enumerator {
    fn into_value_with(self, _: &Ruby) -> Value {
        self.0.get()
    }
}

impl Object for Enumerator {}

unsafe impl private::ReprValue for Enumerator {}

impl ReprValue for Enumerator {}

impl TryConvert for Enumerator {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Self::from_value(val).ok_or_else(|| {
            Error::new(
                exception::type_error(),
                format!("no implicit conversion of {} into Enumerator", unsafe {
                    val.classname()
                },),
            )
        })
    }
}
