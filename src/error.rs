//! Rust types for working with Ruby Exceptions and other interrupts.
//!
//! See also [`Ruby`](Ruby#errors) for more error related methods.

use std::{any::Any, borrow::Cow, ffi::CString, fmt, mem::transmute, os::raw::c_int};

use rb_sys::{
    rb_bug, rb_ensure, rb_errinfo, rb_exc_raise, rb_iter_break, rb_iter_break_value, rb_jump_tag,
    rb_protect, rb_set_errinfo, rb_warning, ruby_special_consts, VALUE,
};

use crate::{
    class::Class,
    exception::Exception,
    into_value::IntoValue,
    module::Module,
    value::{private::ReprValue as _, ReprValue, Value},
    ExceptionClass, Ruby,
};

/// An error returned to indicate an attempt to interact with the Ruby API from
/// a non-Ruby thread or without aquiring the GVL.
#[derive(Debug)]
pub enum RubyUnavailableError {
    /// GVL is not locked.
    GvlUnlocked,
    /// Current thread is not a Ruby thread.
    NonRubyThread,
}

impl fmt::Display for RubyUnavailableError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NonRubyThread => write!(f, "Current thread is not a Ruby thread."),
            Self::GvlUnlocked => write!(f, "GVL is not locked."),
        }
    }
}

impl std::error::Error for RubyUnavailableError {}

/// # `break`
///
/// See also [`Error::iter_break`].
#[allow(missing_docs)]
impl Ruby {
    pub fn iter_break_value<T>(&self, val: Option<T>) -> Error
    where
        T: IntoValue,
    {
        match val {
            Some(val) => {
                let val = self.into_value(val);
                protect(|| {
                    unsafe { rb_iter_break_value(val.as_rb_value()) };
                    self.qnil()
                })
                .unwrap_err()
            }
            None => protect(|| {
                unsafe { rb_iter_break() };
                self.qnil()
            })
            .unwrap_err(),
        }
    }
}

/// Shorthand for `std::result::Result<T, Error>`.
pub type Result<T> = std::result::Result<T, Error>;

/// The possible types of [`Error`].
#[derive(Debug)]
pub enum ErrorType {
    /// An interrupt, such as `break` or `throw`.
    Jump(Tag),
    /// An error generated in Rust code that will raise an exception when
    /// returned to Ruby.
    Error(ExceptionClass, Cow<'static, str>),
    /// A Ruby `Exception` captured from Ruby as an Error.
    Exception(Exception),
}

/// A Rust representation of a Ruby `Exception` or other interrupt.
#[derive(Debug)]
pub struct Error(ErrorType);

impl Error {
    /// Create a new `Error` that can be raised as a Ruby `Exception` with `msg`.
    pub fn new<T>(class: ExceptionClass, msg: T) -> Self
    where
        T: Into<Cow<'static, str>>,
    {
        Self(ErrorType::Error(class, msg.into()))
    }

    pub(crate) fn from_tag(tag: Tag) -> Self {
        Self(ErrorType::Jump(tag))
    }

    /// Create a new `RuntimeError` with `msg`.
    #[deprecated(
        since = "0.5.0",
        note = "Please use `Error::new(exception::runtime_error(), msg)` instead"
    )]
    #[cfg(feature = "friendly-api")]
    pub fn runtime_error<T>(msg: T) -> Self
    where
        T: Into<Cow<'static, str>>,
    {
        Self(ErrorType::Error(
            get_ruby!().exception_runtime_error(),
            msg.into(),
        ))
    }

    /// Create a new error that will break from a loop when returned to Ruby.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread. See [`Ruby::iter_break_value`]
    /// for the non-panicking version.
    #[cfg(feature = "friendly-api")]
    #[inline]
    pub fn iter_break<T>(val: Option<T>) -> Self
    where
        T: IntoValue,
    {
        get_ruby!().iter_break_value(val)
    }

    /// Matches the internal `Exception` against `class` with same semantics as
    /// Ruby's `rescue`.
    pub fn is_kind_of<T>(&self, class: T) -> bool
    where
        T: ReprValue + Module,
    {
        match self.0 {
            ErrorType::Jump(_) => false,
            ErrorType::Error(c, _) => c.is_inherited(class),
            ErrorType::Exception(e) => e.is_kind_of(class),
        }
    }

    /// Consumes `self`, returning an `Exception`.
    ///
    /// # Panics
    ///
    /// Panics if called on an `Error::Jump`.
    fn exception(self) -> Exception {
        let handle = unsafe { Ruby::get_unchecked() };
        match self.0 {
            ErrorType::Jump(_) => panic!("Error::exception() called on {}", self),
            ErrorType::Error(class, msg) => {
                match class.new_instance((handle.str_new(msg.as_ref()),)) {
                    Ok(e) | Err(Error(ErrorType::Exception(e))) => e,
                    Err(err) => unreachable!("*very* unexpected error: {}", err),
                }
            }
            ErrorType::Exception(e) => e,
        }
    }

    /// Returns the [`ErrorType`] for self.
    pub fn error_type(&self) -> &ErrorType {
        &self.0
    }

    /// Returns the inner [`Value`] of `self`, if there is one.
    ///
    /// The returned `Value` may be a subclass or an instance of `Exception`.
    ///
    /// This function is provided for rare cases where the `Error` needs to be
    /// stored on the heap and the inner value needs to be
    /// [marked](`crate::gc::mark`) to avoid being garbage collected.
    pub fn value(&self) -> Option<Value> {
        match self.0 {
            ErrorType::Jump(_) => None,
            ErrorType::Error(c, _) => Some(c.as_value()),
            ErrorType::Exception(e) => Some(e.as_value()),
        }
    }

    /// Create an `Error` from the error value of [`std::panic::catch_unwind`].
    ///
    /// The Ruby Exception will be `fatal`, terminating the Ruby process, but
    /// allowing cleanup code to run.
    pub(crate) fn from_panic(e: Box<dyn Any + Send + 'static>) -> Self {
        let msg = if let Some(&m) = e.downcast_ref::<&'static str>() {
            m.into()
        } else if let Some(m) = e.downcast_ref::<String>() {
            m.clone().into()
        } else {
            "panic".into()
        };
        Self(ErrorType::Error(
            unsafe { Ruby::get_unchecked().exception_fatal() },
            msg,
        ))
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            ErrorType::Jump(s) => s.fmt(f),
            ErrorType::Error(e, m) => write!(f, "{}: {}", e, m),
            ErrorType::Exception(e) => e.fmt(f),
        }
    }
}

impl From<Exception> for Error {
    fn from(val: Exception) -> Self {
        Self(ErrorType::Exception(val))
    }
}

/// A wrapper to make a [`Error`] [`Send`] + [`Sync`].
///
/// [`Error`] is not [`Send`] or [`Sync`] as it provides a way to call some of
/// Ruby's APIs, which are not safe to call from a non-Ruby thread.
///
/// [`Error`] is safe to send between Ruby threads, but Rust's trait system
/// currently can not model this detail.
///
/// To resolve this, the `OpaqueError` type makes an [`Error`] [`Send`] +
/// [`Sync`] by removing the ability use it with any Ruby APIs.
///
/// [`OpaqueError::into_error_with`] provides a way to safely get an [`Error`]
/// from a `OpaqueError`].
pub struct OpaqueError(ErrorType);

unsafe impl Send for OpaqueError {}
unsafe impl Sync for OpaqueError {}

impl OpaqueError {
    /// Convert an `OpaqueError` into an [`Error`].
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{error::OpaqueError, Error, Ruby};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ruby = Ruby::get().unwrap(); // errors on non-Ruby thread
    /// let opaque_err = OpaqueError::from(Error::new(ruby.exception_runtime_error(), "test"));
    ///
    /// // send to another Ruby thread
    ///
    /// let ruby = Ruby::get().unwrap(); // errors on non-Ruby thread
    /// let err = OpaqueError::into_error_with(opaque_err, &ruby);
    /// assert!(err.is_kind_of(ruby.exception_runtime_error()));
    /// ```
    #[allow(unused_variables)]
    pub fn into_error_with(this: Self, handle: &Ruby) -> Error {
        Error(this.0)
    }
}

impl From<Error> for OpaqueError {
    fn from(err: Error) -> Self {
        Self(err.0)
    }
}

/// The state of a call to Ruby exiting early, interrupting the normal flow
/// of code.
#[derive(Debug)]
#[repr(i32)]
pub enum Tag {
    // None = 0,
    /// Early return from a block.
    Return = 1,
    /// Break from a block.
    Break = 2,
    /// Early return from a block, continuing to next block call.
    Next = 3,
    /// Break from a block after an error, block will be subsequently re-run.
    Retry = 4,
    /// Break from a block that will be subsequently re-run.
    Redo = 5,
    /// Ruby stack unwound with an error.
    Raise = 6,
    /// Ruby stack unwound as flow control.
    Throw = 7,
    /// Block or method exiting early due to unrecoverable error.
    Fatal = 8,
}

impl Tag {
    fn resume(self) -> ! {
        unsafe { rb_jump_tag(self as c_int) };
        unreachable!()
    }
}

impl fmt::Display for Tag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            // Self::None => write!(f, "None"),
            Self::Return => write!(f, "Return"),
            Self::Break => write!(f, "Break"),
            Self::Next => write!(f, "Next"),
            Self::Retry => write!(f, "Retry"),
            Self::Redo => write!(f, "Redo"),
            Self::Raise => write!(f, "Raise"),
            Self::Throw => write!(f, "Throw"),
            Self::Fatal => write!(f, "Fatal"),
        }
    }
}

/// Calls the given closure, rescuing Ruby Exceptions and returning them as
/// an [`Error`].
///
/// All functions exposed by magnus that call Ruby in a way that may raise
/// already use this internally, but this is provided for anyone calling
/// the Ruby C API directly.
pub(crate) fn protect<F, T>(func: F) -> Result<T>
where
    F: FnOnce() -> T,
    T: ReprValue,
{
    // nested function as this is totally unsafe to call out of this context
    // arg should not be a VALUE, but a mutable pointer to F, cast to VALUE
    unsafe extern "C" fn call<F, T>(arg: VALUE) -> VALUE
    where
        F: FnOnce() -> T,
        T: ReprValue,
    {
        let closure = (*(arg as *mut Option<F>)).take().unwrap();
        (closure)().as_rb_value()
    }

    // Tag::None
    let mut state = 0;
    // rb_protect takes:
    // arg1: function pointer that returns a VALUE
    // arg2: a VALUE
    // arg3: a pointer to an int.
    // rb_protect then calls arg1 with arg2 and returns the VALUE that arg1
    // returns. If a Ruby exception is raised (or other interrupt) the VALUE
    // returned is instead Qnil, and arg3 is set to non-zero.
    // As arg2 is only ever passed to arg1 and otherwise not touched we can
    // pack in whatever data we want that will fit into a VALUE. This is part
    // of the api and safe to do.
    // In this case we use arg2 to pass a pointer the Rust closure we actually
    // want to call, and arg1 is just a simple adapter to call arg2.
    let result = unsafe {
        let mut some_func = Some(func);
        let closure = &mut some_func as *mut Option<F> as VALUE;
        rb_protect(Some(call::<F, T>), closure, &mut state as *mut c_int)
    };

    match state {
        // Tag::None
        0 => unsafe { Ok(T::from_value_unchecked(Value::new(result))) },
        // Tag::Raise
        6 => unsafe {
            let ex = Exception::from_rb_value_unchecked(rb_errinfo());
            rb_set_errinfo(Ruby::get_unchecked().qnil().as_rb_value());
            Err(ex.into())
        },
        other => Err(Error::from_tag(unsafe { transmute(other) })),
    }
}

pub(crate) fn ensure<F1, F2, T>(func: F1, ensure: F2) -> T
where
    F1: FnOnce() -> T,
    F2: FnOnce(),
    T: ReprValue,
{
    unsafe extern "C" fn call_func<F1, T>(arg: VALUE) -> VALUE
    where
        F1: FnOnce() -> T,
        T: ReprValue,
    {
        let closure = (*(arg as *mut Option<F1>)).take().unwrap();
        (closure)().as_rb_value()
    }

    unsafe extern "C" fn call_ensure<F2>(arg: VALUE) -> VALUE
    where
        F2: FnOnce(),
    {
        let closure = (*(arg as *mut Option<F2>)).take().unwrap();
        (closure)();
        ruby_special_consts::RUBY_Qnil as VALUE
    }

    let result = unsafe {
        let call_func_ptr = call_func::<F1, T> as unsafe extern "C" fn(VALUE) -> VALUE;
        #[cfg(ruby_lt_2_7)]
        let call_func_ptr: unsafe extern "C" fn() -> VALUE = std::mem::transmute(call_func_ptr);
        let mut some_func = Some(func);
        let func_closure = &mut some_func as *mut Option<F1> as VALUE;
        let call_ensure_ptr = call_ensure::<F2> as unsafe extern "C" fn(VALUE) -> VALUE;
        #[cfg(ruby_lt_2_7)]
        let call_ensure_ptr: unsafe extern "C" fn() -> VALUE = std::mem::transmute(call_ensure_ptr);
        let mut some_ensure = Some(ensure);
        let ensure_closure = &mut some_ensure as *mut Option<F2> as VALUE;
        rb_ensure(
            Some(call_func_ptr),
            func_closure,
            Some(call_ensure_ptr),
            ensure_closure,
        )
    };

    unsafe { T::from_value_unchecked(Value::new(result)) }
}

pub(crate) fn raise(e: Error) -> ! {
    match e.0 {
        ErrorType::Jump(tag) => tag.resume(),
        _ => {
            unsafe { rb_exc_raise(e.exception().as_rb_value()) }
            // friendly reminder: we really never get here, and as such won't
            // drop any values still in scope, make sure everything has been
            // consumed/dropped
            unreachable!()
        }
    };
}

pub(crate) fn bug_from_panic(e: Box<dyn Any + Send + 'static>, or: &str) -> ! {
    let msg: Cow<'_, str> = if let Some(&m) = e.downcast_ref::<&'static str>() {
        m.into()
    } else if let Some(m) = e.downcast_ref::<String>() {
        m.clone().into()
    } else {
        or.into()
    };
    bug(&msg)
}

/// Immediately terminate the process, printing Ruby internal state for
/// debugging.
pub fn bug(s: &str) -> ! {
    let s = CString::new(s).unwrap_or_else(|_| CString::new("panic").unwrap());
    unsafe { rb_bug(s.as_ptr()) };
    // as we never get here `s` isn't dropped, technically this is a memory
    // leak, in practice we don't care because we just hard crashed
    unreachable!()
}

/// # Errors
///
/// See also the [`error`](self) module.
#[allow(missing_docs)]
impl Ruby {
    pub fn warning(&self, s: &str) {
        let s = CString::new(s).unwrap();
        unsafe { rb_warning(s.as_ptr()) };
    }
}

/// Outputs `s` to Ruby's stderr if Ruby is configured to output warnings.
///
/// Otherwise does nothing.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::warning`] for the
/// non-panicking version.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn warning(s: &str) {
    get_ruby!().warning(s)
}
