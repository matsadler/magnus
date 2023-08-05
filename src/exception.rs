//! Types and functions for working with Ruby exceptions.
//!
//! See also [`Ruby`](Ruby#core-exceptions) for more exception related methods.

use std::fmt;

#[cfg(ruby_gte_3_1)]
use rb_sys::rb_eNoMatchingPatternKeyError;
use rb_sys::{
    rb_eArgError, rb_eEOFError, rb_eEncCompatError, rb_eEncodingError, rb_eException, rb_eFatal,
    rb_eFloatDomainError, rb_eFrozenError, rb_eIOError, rb_eIndexError, rb_eInterrupt,
    rb_eKeyError, rb_eLoadError, rb_eLocalJumpError, rb_eMathDomainError, rb_eNameError,
    rb_eNoMatchingPatternError, rb_eNoMemError, rb_eNoMethodError, rb_eNotImpError, rb_eRangeError,
    rb_eRegexpError, rb_eRuntimeError, rb_eScriptError, rb_eSecurityError, rb_eSignal,
    rb_eStandardError, rb_eStopIteration, rb_eSyntaxError, rb_eSysStackError, rb_eSystemCallError,
    rb_eSystemExit, rb_eThreadError, rb_eTypeError, rb_eZeroDivError, VALUE,
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
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Exception};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(Exception::from_value(eval(r#"StandardError.new("example")"#).unwrap()).is_some());
    /// assert!(Exception::from_value(eval("Object.new").unwrap()).is_none());
    /// ```
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
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, prelude::*, Exception};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let e: Exception = eval(r#"StandardError.new("example")"#).unwrap();
    /// let ec = e.exception_class();
    /// // safe as we immediately create an owned String and drop the reference
    /// assert_eq!(unsafe { ec.name().to_owned() }, "StandardError");
    /// ```
    pub fn exception_class(self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(self.class().as_rb_value()) }
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
                if let Ok(Some(backtrace)) = self.funcall::<_, _, Option<RArray>>("backtrace", ()) {
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
    #[inline]
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
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, ExceptionClass};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(ExceptionClass::from_value(eval("StandardError").unwrap()).is_some());
    /// assert!(ExceptionClass::from_value(eval(r#"StandardError.new("example")"#).unwrap()).is_none());
    /// assert!(ExceptionClass::from_value(eval("Object").unwrap()).is_none());
    /// ```
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
    #[inline]
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

/// # Core Exceptions
///
/// Functions to access Ruby's built-in exception classes.
///
/// See also the [`exception`](self) module.
impl Ruby {
    /// Return Ruby's `ArgumentError` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "klass == ArgumentError",
    ///         klass = ruby.exception_arg_error()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn exception_arg_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eArgError) }
    }

    /// Return Ruby's `EOFError` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "klass == EOFError",
    ///         klass = ruby.exception_eof_error()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn exception_eof_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eEOFError) }
    }

    /// Return Ruby's `Encoding::CompatibilityError` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "klass == Encoding::CompatibilityError",
    ///         klass = ruby.exception_enc_compat_error()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn exception_enc_compat_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eEncCompatError) }
    }

    /// Return Ruby's `EncodingError` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "klass == EncodingError",
    ///         klass = ruby.exception_encoding_error()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn exception_encoding_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eEncodingError) }
    }

    /// Return Ruby's `Exception` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "klass == Exception",
    ///         klass = ruby.exception_exception()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn exception_exception(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eException) }
    }

    /// Return Ruby's `fatal` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         r#"klass.name == "fatal""#,
    ///         klass = ruby.exception_fatal()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn exception_fatal(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eFatal) }
    }

    /// Return Ruby's `FloatDomainError` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "klass == FloatDomainError",
    ///         klass = ruby.exception_float_domain_error()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn exception_float_domain_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eFloatDomainError) }
    }

    /// Return Ruby's `FrozenError` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "klass == FrozenError",
    ///         klass = ruby.exception_frozen_error()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn exception_frozen_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eFrozenError) }
    }

    /// Return Ruby's `IOError` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "klass == IOError", klass = ruby.exception_io_error());
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn exception_io_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eIOError) }
    }

    /// Return Ruby's `IndexError` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "klass == IndexError",
    ///         klass = ruby.exception_index_error()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn exception_index_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eIndexError) }
    }

    /// Return Ruby's `Interrupt` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "klass == Interrupt",
    ///         klass = ruby.exception_interrupt()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn exception_interrupt(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eInterrupt) }
    }

    /// Return Ruby's `KeyError` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "klass == KeyError",
    ///         klass = ruby.exception_key_error()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn exception_key_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eKeyError) }
    }

    /// Return Ruby's `LoadError` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "klass == LoadError",
    ///         klass = ruby.exception_load_error()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn exception_load_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eLoadError) }
    }

    /// Return Ruby's `LocalJumpError` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "klass == LocalJumpError",
    ///         klass = ruby.exception_local_jump_error()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn exception_local_jump_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eLocalJumpError) }
    }

    /// Return Ruby's `Math::DomainError` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "klass == Math::DomainError",
    ///         klass = ruby.exception_math_domain_error()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn exception_math_domain_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eMathDomainError) }
    }

    /// Return Ruby's `NameError` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "klass == NameError",
    ///         klass = ruby.exception_name_error()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn exception_name_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eNameError) }
    }

    /// Return Ruby's `NoMatchingPatternError` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "klass == NoMatchingPatternError",
    ///         klass = ruby.exception_no_matching_pattern_error()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn exception_no_matching_pattern_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eNoMatchingPatternError) }
    }

    /// Return Ruby's `NoMatchingPatternKeyError` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "klass == NoMatchingPatternKeyError",
    ///         klass = ruby.exception_no_matching_pattern_key_error()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[cfg(any(ruby_gte_3_1, docsrs))]
    #[cfg_attr(docsrs, doc(cfg(ruby_gte_3_1)))]
    #[inline]
    pub fn exception_no_matching_pattern_key_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eNoMatchingPatternKeyError) }
    }

    /// Return Ruby's `NoMemoryError` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "klass == NoMemoryError",
    ///         klass = ruby.exception_no_mem_error()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn exception_no_mem_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eNoMemError) }
    }

    /// Return Ruby's `NoMethodError` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "klass == NoMethodError",
    ///         klass = ruby.exception_no_method_error()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn exception_no_method_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eNoMethodError) }
    }

    /// Return Ruby's `NotImplementedError` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "klass == NotImplementedError",
    ///         klass = ruby.exception_not_imp_error()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn exception_not_imp_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eNotImpError) }
    }

    /// Return Ruby's `RangeError` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "klass == RangeError",
    ///         klass = ruby.exception_range_error()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn exception_range_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eRangeError) }
    }

    /// Return Ruby's `RegexpError` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "klass == RegexpError",
    ///         klass = ruby.exception_regexp_error()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn exception_regexp_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eRegexpError) }
    }

    /// Return Ruby's `RuntimeError` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "klass == RuntimeError",
    ///         klass = ruby.exception_runtime_error()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn exception_runtime_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eRuntimeError) }
    }

    /// Return Ruby's `ScriptError` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "klass == ScriptError",
    ///         klass = ruby.exception_script_error()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn exception_script_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eScriptError) }
    }

    /// Return Ruby's `SecurityError` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "klass == SecurityError",
    ///         klass = ruby.exception_security_error()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn exception_security_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eSecurityError) }
    }

    /// Return Ruby's `SignalException` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "klass == SignalException",
    ///         klass = ruby.exception_signal()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn exception_signal(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eSignal) }
    }

    /// Return Ruby's `StandardError` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "klass == StandardError",
    ///         klass = ruby.exception_standard_error()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn exception_standard_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eStandardError) }
    }

    /// Return Ruby's `StopIteration` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "klass == StopIteration",
    ///         klass = ruby.exception_stop_iteration()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn exception_stop_iteration(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eStopIteration) }
    }

    /// Return Ruby's `SyntaxError` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "klass == SyntaxError",
    ///         klass = ruby.exception_syntax_error()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn exception_syntax_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eSyntaxError) }
    }

    /// Return Ruby's `SystemStackError` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "klass == SystemStackError",
    ///         klass = ruby.exception_sys_stack_error()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn exception_sys_stack_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eSysStackError) }
    }

    /// Return Ruby's `SystemCallError` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "klass == SystemCallError",
    ///         klass = ruby.exception_system_call_error()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn exception_system_call_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eSystemCallError) }
    }

    /// Return Ruby's `SystemExit` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "klass == SystemExit",
    ///         klass = ruby.exception_system_exit()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn exception_system_exit(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eSystemExit) }
    }

    /// Return Ruby's `ThreadError` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "klass == ThreadError",
    ///         klass = ruby.exception_thread_error()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn exception_thread_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eThreadError) }
    }

    /// Return Ruby's `TypeError` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "klass == TypeError",
    ///         klass = ruby.exception_type_error()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn exception_type_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eTypeError) }
    }

    /// Return Ruby's `ZeroDivisionError` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "klass == ZeroDivisionError",
    ///         klass = ruby.exception_zero_div_error()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn exception_zero_div_error(&self) -> ExceptionClass {
        unsafe { ExceptionClass::from_rb_value_unchecked(rb_eZeroDivError) }
    }
}

/// Return Ruby's `ArgumentError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::exception_arg_error`]
/// for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::exception_arg_error` instead")
)]
#[inline]
pub fn arg_error() -> ExceptionClass {
    get_ruby!().exception_arg_error()
}

/// Return Ruby's `EOFError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::exception_eof_error`]
/// for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::exception_eof_error` instead")
)]
#[inline]
pub fn eof_error() -> ExceptionClass {
    get_ruby!().exception_eof_error()
}

/// Return Ruby's `Encoding::CompatibilityError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See
/// [`Ruby::exception_enc_compat_error`] for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::exception_enc_compat_error` instead")
)]
#[inline]
pub fn enc_compat_error() -> ExceptionClass {
    get_ruby!().exception_enc_compat_error()
}

/// Return Ruby's `EncodingError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See
/// [`Ruby::exception_encoding_error`] for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::exception_encoding_error` instead")
)]
#[inline]
pub fn encoding_error() -> ExceptionClass {
    get_ruby!().exception_encoding_error()
}

/// Return Ruby's `Exception` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::exception_exception`]
/// for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::exception_exception` instead")
)]
#[inline]
pub fn exception() -> ExceptionClass {
    get_ruby!().exception_exception()
}

/// Return Ruby's `fatal` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::exception_fatal`] for
/// the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::exception_fatal` instead")
)]
#[inline]
pub fn fatal() -> ExceptionClass {
    get_ruby!().exception_fatal()
}

/// Return Ruby's `FloatDomainError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See
/// [`Ruby::exception_float_domain_error`] for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::exception_float_domain_error` instead")
)]
#[inline]
pub fn float_domain_error() -> ExceptionClass {
    get_ruby!().exception_float_domain_error()
}

/// Return Ruby's `FrozenError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See
/// [`Ruby::exception_frozen_error`] for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::exception_frozen_error` instead")
)]
#[inline]
pub fn frozen_error() -> ExceptionClass {
    get_ruby!().exception_frozen_error()
}

/// Return Ruby's `IOError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::exception_io_error`]
/// for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::exception_io_error` instead")
)]
#[inline]
pub fn io_error() -> ExceptionClass {
    get_ruby!().exception_io_error()
}

/// Return Ruby's `IndexError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See
/// [`Ruby::exception_index_error`] for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::exception_index_error` instead")
)]
#[inline]
pub fn index_error() -> ExceptionClass {
    get_ruby!().exception_index_error()
}

/// Return Ruby's `Interrupt` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::exception_interrupt`]
/// for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::exception_interrupt` instead")
)]
#[inline]
pub fn interrupt() -> ExceptionClass {
    get_ruby!().exception_interrupt()
}

/// Return Ruby's `KeyError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::exception_key_error`]
/// for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::exception_key_error` instead")
)]
#[inline]
pub fn key_error() -> ExceptionClass {
    get_ruby!().exception_key_error()
}

/// Return Ruby's `LoadError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::exception_load_error`]
/// for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::exception_load_error` instead")
)]
#[inline]
pub fn load_error() -> ExceptionClass {
    get_ruby!().exception_load_error()
}

/// Return Ruby's `LocalJumpError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See
/// [`Ruby::exception_local_jump_error`] for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::exception_local_jump_error` instead")
)]
#[inline]
pub fn local_jump_error() -> ExceptionClass {
    get_ruby!().exception_local_jump_error()
}

/// Return Ruby's `Math::DomainError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See
/// [`Ruby::exception_math_domain_error`] for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::exception_math_domain_error` instead")
)]
#[inline]
pub fn math_domain_error() -> ExceptionClass {
    get_ruby!().exception_math_domain_error()
}

/// Return Ruby's `NameError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See
/// [`Ruby::exception_name_error`] for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::exception_name_error` instead")
)]
#[inline]
pub fn name_error() -> ExceptionClass {
    get_ruby!().exception_name_error()
}

/// Return Ruby's `NoMatchingPatternError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See
/// [`Ruby::exception_no_matching_pattern_error`] for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::exception_no_matching_pattern_error` instead")
)]
#[inline]
pub fn no_matching_pattern_error() -> ExceptionClass {
    get_ruby!().exception_no_matching_pattern_error()
}

/// Return Ruby's `NoMatchingPatternKeyError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See
/// [`Ruby::exception_no_matching_pattern_key_error`] for the non-panicking
/// version.
#[cfg(any(ruby_gte_3_1, docsrs))]
#[cfg_attr(docsrs, doc(cfg(ruby_gte_3_1)))]
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::exception_no_matching_pattern_key_error` instead")
)]
#[inline]
pub fn no_matching_pattern_key_error() -> ExceptionClass {
    get_ruby!().exception_no_matching_pattern_key_error()
}

/// Return Ruby's `NoMemoryError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See
/// [`Ruby::exception_no_mem_error`] for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::exception_no_mem_error` instead")
)]
#[inline]
pub fn no_mem_error() -> ExceptionClass {
    get_ruby!().exception_no_mem_error()
}

/// Return Ruby's `NoMethodError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See
/// [`Ruby::exception_no_method_error`] for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::exception_no_method_error` instead")
)]
#[inline]
pub fn no_method_error() -> ExceptionClass {
    get_ruby!().exception_no_method_error()
}

/// Return Ruby's `NotImplementedError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See
/// [`Ruby::exception_not_imp_error`] for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::exception_not_imp_error` instead")
)]
#[inline]
pub fn not_imp_error() -> ExceptionClass {
    get_ruby!().exception_not_imp_error()
}

/// Return Ruby's `RangeError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See
/// [`Ruby::exception_range_error`] for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::exception_range_error` instead")
)]
#[inline]
pub fn range_error() -> ExceptionClass {
    get_ruby!().exception_range_error()
}

/// Return Ruby's `RegexpError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See
/// [`Ruby::exception_regexp_error`] for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::exception_regexp_error` instead")
)]
#[inline]
pub fn regexp_error() -> ExceptionClass {
    get_ruby!().exception_regexp_error()
}

/// Return Ruby's `RuntimeError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See
/// [`Ruby::exception_runtime_error`] for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::exception_runtime_error` instead")
)]
#[inline]
pub fn runtime_error() -> ExceptionClass {
    get_ruby!().exception_runtime_error()
}

/// Return Ruby's `ScriptError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See
/// [`Ruby::exception_script_error`] for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::exception_script_error` instead")
)]
#[inline]
pub fn script_error() -> ExceptionClass {
    get_ruby!().exception_script_error()
}

/// Return Ruby's `SecurityError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See
/// [`Ruby::exception_security_error`] for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::exception_security_error` instead")
)]
#[inline]
pub fn security_error() -> ExceptionClass {
    get_ruby!().exception_security_error()
}

/// Return Ruby's `SignalException` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See
/// [`Ruby::exception_signal`] for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::exception_signal` instead")
)]
#[inline]
pub fn signal() -> ExceptionClass {
    get_ruby!().exception_signal()
}

/// Return Ruby's `StandardError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See
/// [`Ruby::exception_standard_error`] for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::exception_standard_error` instead")
)]
#[inline]
pub fn standard_error() -> ExceptionClass {
    get_ruby!().exception_standard_error()
}

/// Return Ruby's `StopIteration` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See
/// [`Ruby::exception_stop_iteration`] for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::exception_stop_iteration` instead")
)]
#[inline]
pub fn stop_iteration() -> ExceptionClass {
    get_ruby!().exception_stop_iteration()
}

/// Return Ruby's `SyntaxError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See
/// [`Ruby::exception_syntax_error`] for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::exception_syntax_error` instead")
)]
#[inline]
pub fn syntax_error() -> ExceptionClass {
    get_ruby!().exception_syntax_error()
}

/// Return Ruby's `SystemStackError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See
/// [`Ruby::exception_sys_stack_error`] for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::exception_sys_stack_error` instead")
)]
#[inline]
pub fn sys_stack_error() -> ExceptionClass {
    get_ruby!().exception_sys_stack_error()
}

/// Return Ruby's `SystemCallError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See
/// [`Ruby::exception_system_call_error`] for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::exception_system_call_error` instead")
)]
#[inline]
pub fn system_call_error() -> ExceptionClass {
    get_ruby!().exception_system_call_error()
}

/// Return Ruby's `SystemExit` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See
/// [`Ruby::exception_system_exit`] for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::exception_system_exit` instead")
)]
#[inline]
pub fn system_exit() -> ExceptionClass {
    get_ruby!().exception_system_exit()
}

/// Return Ruby's `ThreadError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See
/// [`Ruby::exception_thread_error`] for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::exception_thread_error` instead")
)]
#[inline]
pub fn thread_error() -> ExceptionClass {
    get_ruby!().exception_thread_error()
}

/// Return Ruby's `TypeError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::exception_type_error`]
/// for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::exception_type_error` instead")
)]
#[inline]
pub fn type_error() -> ExceptionClass {
    get_ruby!().exception_type_error()
}

/// Return Ruby's `ZeroDivisionError` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See
/// [`Ruby::exception_zero_div_error`] for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::exception_zero_div_error` instead")
)]
#[inline]
pub fn zero_div_error() -> ExceptionClass {
    get_ruby!().exception_zero_div_error()
}
