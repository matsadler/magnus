use std::{fmt, ops::Deref};

use crate::{
    error::Error,
    object::Object,
    r_class::RClass,
    ruby_sys::{rb_cEnumerator, rb_eStopIteration, VALUE},
    try_convert::TryConvert,
    value::{NonZeroValue, Value},
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
            val.is_kind_of(RClass::from_rb_value_unchecked(rb_cEnumerator))
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
        unsafe {
            match self.funcall("next", ()) {
                Ok(v) => Some(Ok(v)),
                Err(e) if e.is_kind_of(RClass::from_rb_value_unchecked(rb_eStopIteration)) => None,
                Err(e) => Some(Err(e)),
            }
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

impl TryConvert for Enumerator {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        Self::from_value(*val).ok_or_else(|| {
            Error::type_error(format!(
                "no implicit conversion of {} into Enumerator",
                unsafe { val.classname() },
            ))
        })
    }
}
