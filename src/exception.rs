use std::{fmt, ops::Deref};

use crate::{
    debug_assert_value,
    error::Error,
    module::Module,
    object::Object,
    r_array::RArray,
    r_class::RClass,
    ruby_sys::{rb_eException, rb_eRuntimeError, VALUE},
    value::{NonZeroValue, Value},
};

/// Wrapper type for a Value known to be an instance of Ruby's Exception class.
///
/// All [`Value`] methods should be available on this type through [`Deref`],
/// but some may be missed by this documentation.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Exception(NonZeroValue);

impl Exception {
    /// Return `Some(Exception)` if `val` is an `Exception`, `None` otherwise.
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        debug_assert_value!(val);
        unsafe {
            val.class()
                .is_inherited(RClass::from_rb_value_unchecked(rb_eException))
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        Self(NonZeroValue::new_unchecked(Value::new(val)))
    }

    /// Return the Ruby backtrace for the exception, as a [`RArray`] of
    /// [`RString`](`crate::r_string::RString`)s.
    pub fn backtrace(&self) -> Result<Option<RArray>, Error> {
        self.funcall("backtrace", ())
    }
}

impl Deref for Exception {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
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
            unsafe {
                writeln!(f, "{}: {}", self.classname(), self)?;
                if let Ok(Some(backtrace)) = self.backtrace() {
                    for line in backtrace.each() {
                        if let Ok(line) = line {
                            writeln!(f, "{}", line)?;
                        } else {
                            break;
                        }
                    }
                }
            }
            Ok(())
        } else {
            write!(f, "{}", self.inspect())
        }
    }
}

impl From<Exception> for Value {
    fn from(val: Exception) -> Self {
        *val
    }
}

/// A Value known to be an instance of Class and subclass of Exception.
///
/// All [`Value`] methods should be available on this type through [`Deref`],
/// but some may be missed by this documentation.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct ExceptionClass(NonZeroValue);

impl ExceptionClass {
    /// Return `Some(ExceptionClass)` if `val` is an `ExceptionClass`, `None`
    /// otherwise.
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        debug_assert_value!(val);
        unsafe {
            RClass::from_value(val).and_then(|class| {
                class
                    .is_inherited(RClass::from_rb_value_unchecked(rb_eException))
                    .then(|| Self(NonZeroValue::new_unchecked(val)))
            })
        }
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        Self(NonZeroValue::new_unchecked(Value::new(val)))
    }
}

impl Deref for ExceptionClass {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
    }
}

impl Default for ExceptionClass {
    fn default() -> Self {
        unsafe { Self::from_rb_value_unchecked(rb_eRuntimeError) }
    }
}

impl fmt::Display for ExceptionClass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for ExceptionClass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl From<ExceptionClass> for Value {
    fn from(val: ExceptionClass) -> Self {
        *val
    }
}

impl Object for ExceptionClass {}
impl Module for ExceptionClass {}
