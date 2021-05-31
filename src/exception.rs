use std::{fmt, ops::Deref};

use crate::{
    debug_assert_value,
    r_basic::RBasic,
    r_class::RClass,
    ruby_sys::{rb_eException, rb_eRuntimeError, ruby_value_type, VALUE},
    value::Value,
};

#[repr(transparent)]
pub struct Exception(pub(crate) VALUE);

impl Exception {
    /// # Safety
    ///
    /// val must not have been GC'd, return value must be kept on stack or
    /// otherwise protected from the GC.
    pub unsafe fn from_value(val: &Value) -> Option<Self> {
        debug_assert_value!(val);
        let r_basic = RBasic::from_value(val)?;
        (r_basic.builtin_type() == ruby_value_type::RUBY_T_OBJECT
            && r_basic.class().is_inherited(RClass(rb_eException)))
        .then(|| Self(val.into_inner()))
    }
}

impl Deref for Exception {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        let self_ptr = self as *const Self;
        let value_ptr = self_ptr as *const Self::Target;
        // we just got this pointer from &self, so we know it's valid to deref
        unsafe { &*value_ptr }
    }
}

impl fmt::Display for Exception {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for Exception {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            // TODO format with backtrace
            write!(f, "{}", unsafe { self.inspect() })
        } else {
            write!(f, "{}", unsafe { self.inspect() })
        }
    }
}

impl From<Exception> for Value {
    fn from(val: Exception) -> Self {
        *val
    }
}

#[repr(transparent)]
pub struct ExceptionClass(pub(crate) VALUE);

impl ExceptionClass {
    /// # Safety
    ///
    /// val must not have been GC'd, return value must be kept on stack or
    /// otherwise protected from the GC.
    pub unsafe fn from_value(val: &Value) -> Option<Self> {
        debug_assert_value!(val);
        RClass::from_value(val).and_then(|class| {
            class
                .is_inherited(RClass(rb_eException))
                .then(|| Self(class.into_inner()))
        })
    }
}

impl Deref for ExceptionClass {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        let self_ptr = self as *const Self;
        let value_ptr = self_ptr as *const Self::Target;
        // we just got this pointer from &self, so we know it's valid to deref
        unsafe { &*value_ptr }
    }
}

impl Default for ExceptionClass {
    fn default() -> Self {
        unsafe { Self(rb_eRuntimeError) }
    }
}

impl fmt::Display for ExceptionClass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for ExceptionClass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.inspect() })
    }
}

impl From<ExceptionClass> for Value {
    fn from(val: ExceptionClass) -> Self {
        *val
    }
}
