use std::{fmt, ops::Deref};

use crate::ruby_sys::VALUE;

use crate::{
    class,
    error::Error,
    exception,
    object::Object,
    try_convert::TryConvert,
    value::{private, NonZeroValue, ReprValue, Value},
};

/// Wrapper type for a Value known to be an instance of Ruby's Enumerator class.
///
/// All [`Value`] methods should be available on this type through [`Deref`],
/// but some may be missed by this documentation.
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

impl Deref for Enumerator {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
    }
}

impl fmt::Display for Enumerator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for Enumerator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.deref().inspect())
    }
}

impl From<Enumerator> for Value {
    fn from(val: Enumerator) -> Self {
        *val
    }
}

impl Object for Enumerator {}

unsafe impl private::ReprValue for Enumerator {
    fn to_value(self) -> Value {
        *self
    }

    unsafe fn from_value_unchecked(val: Value) -> Self {
        Self(NonZeroValue::new_unchecked(val))
    }
}

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
