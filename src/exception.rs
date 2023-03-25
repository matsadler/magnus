//! Types and functions for working with Ruby exceptions.

use std::fmt;

#[cfg(ruby_gte_2_7)]
use rb_sys::rb_eNoMatchingPatternError;
#[cfg(ruby_gte_3_1)]
use rb_sys::rb_eNoMatchingPatternKeyError;
use rb_sys::{
    rb_eArgError, rb_eEOFError, rb_eEncCompatError, rb_eEncodingError, rb_eException, rb_eFatal,
    rb_eFloatDomainError, rb_eFrozenError, rb_eIOError, rb_eIndexError, rb_eInterrupt,
    rb_eKeyError, rb_eLoadError, rb_eLocalJumpError, rb_eMathDomainError, rb_eNameError,
    rb_eNoMemError, rb_eNoMethodError, rb_eNotImpError, rb_eRangeError, rb_eRegexpError,
    rb_eRuntimeError, rb_eScriptError, rb_eSecurityError, rb_eSignal, rb_eStandardError,
    rb_eStopIteration, rb_eSyntaxError, rb_eSysStackError, rb_eSystemCallError, rb_eSystemExit,
    rb_eThreadError, rb_eTypeError, rb_eZeroDivError, VALUE,
};

use crate::{
    class::{Class, RClass},
    error::Error,
    into_value::{ArgList, IntoValue},
    module::Module,
    object::Object,
    r_array::RArray,
    try_convert::TryConvert,
    value::{
        private::{self, ReprValue as _},
        NonZeroValue, ReprValue, Value,
    },
    Ruby,
};

/// Wrapper type for a Value known to be an instance of Ruby's Exception class.
///
/// See the [`ReprValue`] and [`Object`] traits for additional methods
/// available on this type.
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

    /// Returns the class that `self` is an instance of, as an
    /// [`ExceptionClass`].
    ///
    /// See also [`ReprValue::class`].
    pub fn exception_class(self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(self.class().as_rb_value()) }
    }

    /// Return the Ruby backtrace for the exception, as a [`RArray`] of
    /// [`RString`](`crate::r_string::RString`)s.
    pub fn backtrace(self) -> Result<Option<RArray>, Error> {
        self.funcall("backtrace", ())
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

impl IntoValue for Exception {
    fn into_value_with(self, _: &Ruby) -> Value {
        self.0.get()
    }
}

unsafe impl private::ReprValue for Exception {}

impl ReprValue for Exception {}

impl TryConvert for Exception {
    fn try_convert(val: Value) -> Result<Self, Error> {
        if let Some(e) = Self::from_value(val) {
            return Ok(e);
        }
        if let Some(Ok(val)) = val.check_funcall::<_, _, Value>("exception", ()) {
            if let Some(e) = Self::from_value(val) {
                return Ok(e);
            }
        }
        Err(Error::new(
            Ruby::get_with(val).exception_type_error(),
            format!("no implicit conversion of {} into Exception", unsafe {
                val.classname()
            },),
        ))
    }
}

/// A Value known to be an instance of Class and subclass of Exception.
///
/// See the [`ReprValue`] and [`Object`] traits for additional methods
/// available on this type.
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

impl IntoValue for ExceptionClass {
    fn into_value_with(self, _: &Ruby) -> Value {
        self.0.get()
    }
}

impl Object for ExceptionClass {}
impl Module for ExceptionClass {}

impl Class for ExceptionClass {
    type Instance = Exception;

    fn new(superclass: Self) -> Result<Self, Error> {
        RClass::new(superclass.as_r_class())
            .map(|class| unsafe { ExceptionClass::from_value_unchecked(class.as_value()) })
    }

    fn new_instance<T>(self, args: T) -> Result<Self::Instance, Error>
    where
        T: ArgList,
    {
        self.as_r_class()
            .new_instance(args)
            .map(|ins| unsafe { Exception::from_value_unchecked(ins) })
    }

    fn obj_alloc(self) -> Result<Self::Instance, Error> {
        self.as_r_class()
            .obj_alloc()
            .map(|ins| unsafe { Exception::from_value_unchecked(ins) })
    }

    fn as_r_class(self) -> RClass {
        unsafe { RClass::from_value_unchecked(self.as_value()) }
    }
}

unsafe impl private::ReprValue for ExceptionClass {}

impl ReprValue for ExceptionClass {}

impl TryConvert for ExceptionClass {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Self::from_value(val).ok_or_else(|| {
            Error::new(
                Ruby::get_with(val).exception_type_error(),
                format!(
                    "no implicit conversion of {} into Class inheriting Exception",
                    unsafe { val.classname() },
                ),
            )
        })
    }
}

#[allow(missing_docs)]
impl Ruby {
    #[inline]
    pub fn exception_arg_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eArgError) }
    }

    #[inline]
    pub fn exception_eof_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eEOFError) }
    }

    #[inline]
    pub fn exception_enc_compat_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eEncCompatError) }
    }

    #[inline]
    pub fn exception_encoding_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eEncodingError) }
    }

    #[inline]
    pub fn exception_exception(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eException) }
    }

    #[inline]
    pub fn exception_fatal(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eFatal) }
    }

    #[inline]
    pub fn exception_float_domain_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eFloatDomainError) }
    }

    #[inline]
    pub fn exception_frozen_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eFrozenError) }
    }

    #[inline]
    pub fn exception_io_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eIOError) }
    }

    #[inline]
    pub fn exception_index_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eIndexError) }
    }

    #[inline]
    pub fn exception_interrupt(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eInterrupt) }
    }

    #[inline]
    pub fn exception_key_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eKeyError) }
    }

    #[inline]
    pub fn exception_load_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eLoadError) }
    }

    #[inline]
    pub fn exception_local_jump_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eLocalJumpError) }
    }

    #[inline]
    pub fn exception_math_domain_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eMathDomainError) }
    }

    #[inline]
    pub fn exception_name_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eNameError) }
    }

    #[cfg(any(ruby_gte_2_7, docsrs))]
    #[cfg_attr(docsrs, doc(cfg(ruby_gte_2_7)))]
    #[inline]
    pub fn exception_no_matching_pattern_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eNoMatchingPatternError) }
    }

    #[cfg(any(ruby_gte_3_1, docsrs))]
    #[cfg_attr(docsrs, doc(cfg(ruby_gte_3_1)))]
    #[inline]
    pub fn exception_no_matching_pattern_key_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eNoMatchingPatternKeyError) }
    }

    #[inline]
    pub fn exception_no_mem_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eNoMemError) }
    }

    #[inline]
    pub fn exception_no_method_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eNoMethodError) }
    }

    #[inline]
    pub fn exception_not_imp_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eNotImpError) }
    }

    #[inline]
    pub fn exception_range_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eRangeError) }
    }

    #[inline]
    pub fn exception_regexp_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eRegexpError) }
    }

    #[inline]
    pub fn exception_runtime_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eRuntimeError) }
    }

    #[inline]
    pub fn exception_script_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eScriptError) }
    }

    #[inline]
    pub fn exception_security_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eSecurityError) }
    }

    #[inline]
    pub fn exception_signal(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eSignal) }
    }

    #[inline]
    pub fn exception_standard_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eStandardError) }
    }

    #[inline]
    pub fn exception_stop_iteration(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eStopIteration) }
    }

    #[inline]
    pub fn exception_syntax_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eSyntaxError) }
    }

    #[inline]
    pub fn exception_sys_stack_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eSysStackError) }
    }

    #[inline]
    pub fn exception_system_call_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eSystemCallError) }
    }

    #[inline]
    pub fn exception_system_exit(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eSystemExit) }
    }

    #[inline]
    pub fn exception_thread_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eThreadError) }
    }

    #[inline]
    pub fn exception_type_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eTypeError) }
    }

    #[inline]
    pub fn exception_zero_div_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eZeroDivError) }
    }
}

/// Return Ruby's `ArgumentError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn arg_error() -> ExceptionClass {
    get_ruby!().exception_arg_error()
}

/// Return Ruby's `EOFError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn eof_error() -> ExceptionClass {
    get_ruby!().exception_eof_error()
}

/// Return Ruby's `Encoding::CompatibilityError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn enc_compat_error() -> ExceptionClass {
    get_ruby!().exception_enc_compat_error()
}

/// Return Ruby's `EncodingError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn encoding_error() -> ExceptionClass {
    get_ruby!().exception_encoding_error()
}

/// Return Ruby's `Exception` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn exception() -> ExceptionClass {
    get_ruby!().exception_exception()
}

/// Return Ruby's `fatal` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn fatal() -> ExceptionClass {
    get_ruby!().exception_fatal()
}

/// Return Ruby's `FloatDomainError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn float_domain_error() -> ExceptionClass {
    get_ruby!().exception_float_domain_error()
}

/// Return Ruby's `FrozenError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn frozen_error() -> ExceptionClass {
    get_ruby!().exception_frozen_error()
}

/// Return Ruby's `IOError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn io_error() -> ExceptionClass {
    get_ruby!().exception_io_error()
}

/// Return Ruby's `IndexError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn index_error() -> ExceptionClass {
    get_ruby!().exception_index_error()
}

/// Return Ruby's `Interrupt` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn interrupt() -> ExceptionClass {
    get_ruby!().exception_interrupt()
}

/// Return Ruby's `KeyError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn key_error() -> ExceptionClass {
    get_ruby!().exception_key_error()
}

/// Return Ruby's `LoadError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn load_error() -> ExceptionClass {
    get_ruby!().exception_load_error()
}

/// Return Ruby's `LocalJumpError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn local_jump_error() -> ExceptionClass {
    get_ruby!().exception_local_jump_error()
}

/// Return Ruby's `Math::DomainError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn math_domain_error() -> ExceptionClass {
    get_ruby!().exception_math_domain_error()
}

/// Return Ruby's `NameError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn name_error() -> ExceptionClass {
    get_ruby!().exception_name_error()
}

/// Return Ruby's `NoMatchingPatternError` class.
#[cfg(any(ruby_gte_2_7, docsrs))]
#[cfg_attr(docsrs, doc(cfg(ruby_gte_2_7)))]
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn no_matching_pattern_error() -> ExceptionClass {
    get_ruby!().exception_no_matching_pattern_error()
}

/// Return Ruby's `NoMatchingPatternKeyError` class.
#[cfg(any(ruby_gte_3_1, docsrs))]
#[cfg_attr(docsrs, doc(cfg(ruby_gte_3_1)))]
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn no_matching_pattern_key_error() -> ExceptionClass {
    get_ruby!().exception_no_matching_pattern_key_error()
}

/// Return Ruby's `NoMemoryError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn no_mem_error() -> ExceptionClass {
    get_ruby!().exception_no_mem_error()
}

/// Return Ruby's `NoMethodError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn no_method_error() -> ExceptionClass {
    get_ruby!().exception_no_method_error()
}

/// Return Ruby's `NotImpError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn not_imp_error() -> ExceptionClass {
    get_ruby!().exception_not_imp_error()
}

/// Return Ruby's `RangeError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn range_error() -> ExceptionClass {
    get_ruby!().exception_range_error()
}

/// Return Ruby's `RegexpError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn regexp_error() -> ExceptionClass {
    get_ruby!().exception_regexp_error()
}

/// Return Ruby's `RuntimeError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn runtime_error() -> ExceptionClass {
    get_ruby!().exception_runtime_error()
}

/// Return Ruby's `ScriptError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn script_error() -> ExceptionClass {
    get_ruby!().exception_script_error()
}

/// Return Ruby's `SecurityError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn security_error() -> ExceptionClass {
    get_ruby!().exception_security_error()
}

/// Return Ruby's `SignalException` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn signal() -> ExceptionClass {
    get_ruby!().exception_signal()
}

/// Return Ruby's `StandardError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn standard_error() -> ExceptionClass {
    get_ruby!().exception_standard_error()
}

/// Return Ruby's `StopIteration` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn stop_iteration() -> ExceptionClass {
    get_ruby!().exception_stop_iteration()
}

/// Return Ruby's `SyntaxError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn syntax_error() -> ExceptionClass {
    get_ruby!().exception_syntax_error()
}

/// Return Ruby's `SystemStackError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn sys_stack_error() -> ExceptionClass {
    get_ruby!().exception_sys_stack_error()
}

/// Return Ruby's `SystemCallError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn system_call_error() -> ExceptionClass {
    get_ruby!().exception_system_call_error()
}

/// Return Ruby's `SystemExit` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn system_exit() -> ExceptionClass {
    get_ruby!().exception_system_exit()
}

/// Return Ruby's `ThreadError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn thread_error() -> ExceptionClass {
    get_ruby!().exception_thread_error()
}

/// Return Ruby's `TypeError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn type_error() -> ExceptionClass {
    get_ruby!().exception_type_error()
}

/// Return Ruby's `ZeroDivisionError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn zero_div_error() -> ExceptionClass {
    get_ruby!().exception_zero_div_error()
}
