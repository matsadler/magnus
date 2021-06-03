use std::{fmt, ops::Deref};

use crate::{
    error::Error,
    object::Object,
    r_class::RClass,
    ruby_sys::{rb_cEnumerator, rb_eStopIteration, VALUE},
    value::{NonZeroValue, Value},
};

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Enumerator(NonZeroValue);

impl Enumerator {
    /// # Safety
    ///
    /// val must not have been GC'd, return value must be kept on stack or
    /// otherwise protected from the GC.
    pub unsafe fn from_value(val: Value) -> Option<Self> {
        val.is_kind_of(RClass::from_rb_value_unchecked(rb_cEnumerator))
            .then(|| Self(NonZeroValue::new_unchecked(val)))
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
        write!(f, "{}", unsafe { self.deref().inspect() })
    }
}

impl From<Enumerator> for Value {
    fn from(val: Enumerator) -> Self {
        *val
    }
}

impl Object for Enumerator {}
