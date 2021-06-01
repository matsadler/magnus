use std::{fmt, ops::Deref};

use crate::{
    error::Error,
    object::Object,
    r_class::RClass,
    ruby_sys::{rb_cEnumerator, rb_eStopIteration, VALUE},
    value::Value,
};

#[repr(transparent)]
pub struct Enumerator(pub(crate) VALUE);

impl Enumerator {
    /// # Safety
    ///
    /// val must not have been GC'd, return value must be kept on stack or
    /// otherwise protected from the GC.
    pub unsafe fn from_value(val: &Value) -> Option<Self> {
        val.is_kind_of(RClass(rb_cEnumerator))
            .then(|| Self(val.into_inner()))
    }
}

impl Iterator for Enumerator {
    type Item = Result<Value, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            match self.funcall("next", ()) {
                Ok(v) => Some(Ok(v)),
                // TODO check this matching actually works
                Err(e) if e.is_kind_of(RClass(rb_eStopIteration)) => None,
                Err(e) => Some(Err(e)),
            }
        }
    }
}

impl Deref for Enumerator {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        let self_ptr = self as *const Self;
        let value_ptr = self_ptr as *const Self::Target;
        // we just got this pointer from &self, so we know it's valid to deref
        unsafe { &*value_ptr }
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
