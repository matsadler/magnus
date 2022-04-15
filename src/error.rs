//! Rust types for working with Ruby Exceptions and other interrupts.

use std::{any::Any, borrow::Cow, ffi::CString, fmt, mem::transmute, ops::Deref, os::raw::c_int};

use crate::ruby_sys::{
    rb_ensure, rb_errinfo, rb_exc_raise, rb_jump_tag, rb_protect, rb_raise, rb_set_errinfo,
    ruby_special_consts, VALUE,
};

use crate::{
    debug_assert_value,
    exception::{self, Exception, ExceptionClass},
    module::Module,
    value::{Value, QNIL},
};

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
    pub fn runtime_error<T>(msg: T) -> Self
    where
        T: Into<Cow<'static, str>>,
    {
        Self::Error(Default::default(), msg.into())
    }

    /// Create a new `ArgumentError` with `msg`.
    #[deprecated(
        since = "0.2.0",
        note = "please use `Error::new(exception::arg_error(), msg)` instead"
    )]
    pub fn argument_error<T>(msg: T) -> Self
    where
        T: Into<Cow<'static, str>>,
    {
        Self::Error(exception::arg_error(), msg.into())
    }

    /// Create a new `RangeError` with `msg`.
    #[deprecated(
        since = "0.2.0",
        note = "please use `Error::new(exception::range_error(), msg)` instead"
    )]
    pub fn range_error<T>(msg: T) -> Self
    where
        T: Into<Cow<'static, str>>,
    {
        Self::Error(exception::range_error(), msg.into())
    }

    /// Create a new `TypeError` with `msg`.
    #[deprecated(
        since = "0.2.0",
        note = "please use `Error::new(exception::type_error(), msg)` instead"
    )]
    pub fn type_error<T>(msg: T) -> Self
    where
        T: Into<Cow<'static, str>>,
    {
        Self::Error(exception::type_error(), msg.into())
    }

    /// Create a new `EncodingError` with `msg`.
    #[deprecated(
        since = "0.2.0",
        note = "please use `Error::new(exception::encoding_error(), msg)` instead"
    )]
    pub fn encoding_error<T>(msg: T) -> Self
    where
        T: Into<Cow<'static, str>>,
    {
        Self::Error(exception::encoding_error(), msg.into())
    }

    /// Create a new `IndexError` with `msg`.
    #[deprecated(
        since = "0.2.0",
        note = "please use `Error::new(exception::index_error(), msg)` instead"
    )]
    pub fn index_error<T>(msg: T) -> Self
    where
        T: Into<Cow<'static, str>>,
    {
        Self::Error(exception::index_error(), msg.into())
    }

    /// Create a new `FrozenError` with `msg`.
    #[deprecated(
        since = "0.2.0",
        note = "please use `Error::new(exception::frozen_error(), msg)` instead"
    )]
    pub fn frozen_error<T>(msg: T) -> Self
    where
        T: Into<Cow<'static, str>>,
    {
        Self::Error(exception::frozen_error(), msg.into())
    }

    /// Create a new `StopIteration` with `msg`.
    #[deprecated(
        since = "0.2.0",
        note = "please use `Error::new(exception::stop_iteration(), msg)` instead"
    )]
    pub fn stop_iteration<T>(msg: T) -> Self
    where
        T: Into<Cow<'static, str>>,
    {
        Self::Error(exception::stop_iteration(), msg.into())
    }

    /// Create a new `ScriptError` with `msg`.
    #[deprecated(
        since = "0.2.0",
        note = "please use `Error::new(exception::script_error(), msg)` instead"
    )]
    pub fn script_error<T>(msg: T) -> Self
    where
        T: Into<Cow<'static, str>>,
    {
        Self::Error(exception::script_error(), msg.into())
    }

    /// Matches the internal `Exception` against `class` with same semantics as
    /// Ruby's `rescue`.
    pub fn is_kind_of<T>(&self, class: T) -> bool
    where
        T: Deref<Target = Value> + Module,
    {
        match self {
            Error::Jump(_) => false,
            Error::Error(c, _) => c.is_inherited(class),
            Error::Exception(e) => e.is_kind_of(class),
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
pub fn protect<F>(func: F) -> Result<Value, Error>
where
    F: FnOnce() -> Value,
{
    // nested function as this is totally unsafe to call out of this context
    // arg should not be a VALUE, but a mutable pointer to F, cast to VALUE
    unsafe extern "C" fn call<F>(arg: VALUE) -> VALUE
    where
        F: FnOnce() -> Value,
    {
        let closure = (&mut *(arg as *mut Option<F>)).take().unwrap();
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
        rb_protect(Some(call::<F>), closure, &mut state as *mut c_int)
    };

    match state {
        // Tag::None
        0 => Ok(Value::new(result)),
        // Tag::Raise
        6 => unsafe {
            let ex = Exception::from_rb_value_unchecked(rb_errinfo());
            rb_set_errinfo(QNIL.as_rb_value());
            Err(Error::Exception(ex))
        },
        other => Err(Error::Jump(unsafe { transmute(other) })),
    }
}

pub(crate) fn ensure<F1, F2>(func: F1, ensure: F2) -> Value
where
    F1: FnOnce() -> Value,
    F2: FnOnce(),
{
    unsafe extern "C" fn call_func<F1>(arg: VALUE) -> VALUE
    where
        F1: FnOnce() -> Value,
    {
        let closure = (&mut *(arg as *mut Option<F1>)).take().unwrap();
        (closure)().as_rb_value()
    }

    unsafe extern "C" fn call_ensure<F2>(arg: VALUE) -> VALUE
    where
        F2: FnOnce(),
    {
        let closure = (&mut *(arg as *mut Option<F2>)).take().unwrap();
        (closure)();
        ruby_special_consts::RUBY_Qnil as VALUE
    }

    let result = unsafe {
        let call_func_ptr = call_func::<F1> as unsafe extern "C" fn(VALUE) -> VALUE;
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

    Value::new(result)
}

pub(crate) fn raise(e: Error) -> ! {
    match e {
        Error::Jump(tag) => tag.resume(),
        Error::Error(class, msg) => {
            debug_assert_value!(class);
            let msg = CString::new(msg.into_owned()).unwrap();
            unsafe { rb_raise(class.as_rb_value(), msg.as_ptr()) }
            unreachable!()
        }
        Error::Exception(e) => {
            debug_assert_value!(e);
            unsafe { rb_exc_raise(e.as_rb_value()) }
            unreachable!()
        }
    }
}
