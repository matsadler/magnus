//! Rust types for working with Ruby Exceptions and other interrupts.

use std::{any::Any, borrow::Cow, ffi::CString, fmt, mem::transmute, os::raw::c_int};

use rb_sys::{
    rb_bug, rb_ensure, rb_errinfo, rb_exc_raise, rb_iter_break, rb_iter_break_value, rb_jump_tag,
    rb_protect, rb_set_errinfo, rb_warning, ruby_special_consts, VALUE,
};

use crate::{
    class::Class,
    exception::{self, Exception, ExceptionClass},
    into_value::IntoValue,
    module::Module,
    r_string::RString,
    ruby_handle::RubyHandle,
    value::{private::ReprValue as _, ReprValue, Value, QNIL},
};

impl RubyHandle {
    pub fn iter_break_value<T>(&self, val: Option<T>) -> Error
    where
        T: IntoValue,
    {
        match val {
            Some(val) => {
                let val = self.into_value(val);
                protect(|| {
                    unsafe { rb_iter_break_value(val.as_rb_value()) };
                    QNIL
                })
                .unwrap_err()
            }
            None => protect(|| {
                unsafe { rb_iter_break() };
                QNIL
            })
            .unwrap_err(),
        }
    }
}

/// Shorthand for `std::result::Result<T, Error>`.
pub type Result<T> = std::result::Result<T, Error>;

/// A Rust representation of a Ruby `Exception` or other interrupt.
#[derive(Debug)]
pub enum Error {
    /// An interrupt, such as `break` or `throw`.
    Jump(Tag),
    /// An error generated in Rust code that will raise an exception when
    /// returned to Ruby.
    Error(ExceptionClass, Cow<'static, str>),
    /// A Ruby `Exception` captured from Ruby as an Error.
    Exception(Exception),
}

impl Error {
    /// Create a new `Error` that can be raised as a Ruby `Exception` with `msg`.
    pub fn new<T>(class: ExceptionClass, msg: T) -> Self
    where
        T: Into<Cow<'static, str>>,
    {
        Self::Error(class, msg.into())
    }

    /// Create a new `RuntimeError` with `msg`.
    #[deprecated(
        since = "0.5.0",
        note = "Please use `Error::new(exception::runtime_error(), msg)` instead"
    )]
    pub fn runtime_error<T>(msg: T) -> Self
    where
        T: Into<Cow<'static, str>>,
    {
        Self::Error(exception::runtime_error(), msg.into())
    }

    /// Create a new error that will break from a loop when returned to Ruby.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread.
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
        match self {
            Error::Jump(_) => false,
            Error::Error(c, _) => c.is_inherited(class),
            Error::Exception(e) => e.is_kind_of(class),
        }
    }

    /// Consumes `self`, returning an `Exception`.
    ///
    /// # Panics
    ///
    /// Panics if called on an `Error::Jump`.
    fn exception(self) -> Exception {
        match self {
            Error::Jump(_) => panic!("Error::exception() called on {}", self),
            Error::Error(class, msg) => match class.new_instance((RString::new(msg.as_ref()),)) {
                Ok(e) | Err(Error::Exception(e)) => e,
                Err(err) => unreachable!("*very* unexpected error: {}", err),
            },
            Error::Exception(e) => e,
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
        Self::Error(exception::fatal(), msg)
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Jump(s) => s.fmt(f),
            Error::Error(e, m) => write!(f, "{}: {}", e, m),
            Error::Exception(e) => e.fmt(f),
        }
    }
}

impl From<Tag> for Error {
    fn from(val: Tag) -> Self {
        Self::Jump(val)
    }
}

impl From<Exception> for Error {
    fn from(val: Exception) -> Self {
        Self::Exception(val)
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
            rb_set_errinfo(QNIL.as_rb_value());
            Err(Error::Exception(ex))
        },
        other => Err(Error::Jump(unsafe { transmute(other) })),
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
    match e {
        Error::Jump(tag) => tag.resume(),
        err => {
            unsafe { rb_exc_raise(err.exception().as_rb_value()) }
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

impl RubyHandle {
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
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn warning(s: &str) {
    get_ruby!().warning(s)
}
