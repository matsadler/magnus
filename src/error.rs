use std::{any::Any, borrow::Cow, ffi::CString, fmt, os::raw::c_int};

use crate::{
    debug_assert_value,
    exception::{Exception, ExceptionClass},
    ruby_sys::{
        rb_eEncodingError, rb_eRangeError, rb_eScriptError, rb_eTypeError, rb_errinfo,
        rb_exc_raise, rb_jump_tag, rb_protect, rb_raise, rb_set_errinfo, VALUE,
    },
    value::{Qnil, Value},
};

#[derive(Debug)]
pub enum Error {
    Jump(State),
    Error(ExceptionClass, Cow<'static, str>),
    Exception(Exception),
}

impl Error {
    pub fn new<T>(class: ExceptionClass, msg: T) -> Self
    where
        T: Into<Cow<'static, str>>,
    {
        Self::Error(class, msg.into())
    }

    pub fn runtime_error<T>(msg: T) -> Self
    where
        T: Into<Cow<'static, str>>,
    {
        Self::Error(Default::default(), msg.into())
    }

    pub fn range_error<T>(msg: T) -> Self
    where
        T: Into<Cow<'static, str>>,
    {
        Self::Error(ExceptionClass(unsafe { rb_eRangeError }), msg.into())
    }

    pub fn type_error<T>(msg: T) -> Self
    where
        T: Into<Cow<'static, str>>,
    {
        Self::Error(ExceptionClass(unsafe { rb_eTypeError }), msg.into())
    }

    pub fn encoding_error<T>(msg: T) -> Self
    where
        T: Into<Cow<'static, str>>,
    {
        Self::Error(ExceptionClass(unsafe { rb_eEncodingError }), msg.into())
    }

    pub(crate) fn from_panic(e: Box<dyn Any + Send + 'static>) -> Self {
        let msg = if let Some(&m) = e.downcast_ref::<&'static str>() {
            m.into()
        } else if let Some(m) = e.downcast_ref::<String>() {
            m.clone().into()
        } else {
            "panic".into()
        };
        Self::Error(ExceptionClass(unsafe { rb_eScriptError }), msg)
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Jump(s) => s.fmt(f),
            Error::Error(_, m) => m.fmt(f),
            Error::Exception(e) => e.fmt(f),
        }
    }
}

impl From<State> for Error {
    fn from(val: State) -> Self {
        Self::Jump(val)
    }
}

impl From<Exception> for Error {
    fn from(val: Exception) -> Self {
        Self::Exception(val)
    }
}

#[repr(transparent)]
pub struct State(pub(crate) c_int);

impl State {
    /// # Safety
    ///
    /// This function is currently marked unsafe as it is presumed that the
    /// State can get stale and thus no longer safe to resume.
    pub unsafe fn resume(self) -> ! {
        rb_jump_tag(self.0);
        unreachable!()
    }

    pub fn is_exception(&self) -> bool {
        // safe ffi to Ruby, call doesn't raise
        !Value::new(unsafe { rb_errinfo() }).is_nil()
    }

    fn exception(&self) -> Option<Exception> {
        // safe ffi to Ruby, call doesn't raise
        let val = Value::new(unsafe { rb_errinfo() });
        (val.is_nil()).then(|| Exception(val.into_inner()))
    }

    pub fn into_exception(self) -> Result<Exception, Self> {
        // need to clear errinfo, that's done by drop
        self.exception().ok_or(self)
    }
}

impl Drop for State {
    fn drop(&mut self) {
        // safe ffi to Ruby, call doesn't raise
        unsafe { rb_set_errinfo(Qnil::new().into_inner()) };
    }
}

impl fmt::Display for State {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.exception() {
            Some(e) => write!(f, "{}", e),
            None => write!(f, "protect state {}", self.0),
        }
    }
}

impl fmt::Debug for State {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.exception() {
            Some(e) => write!(f, "{:?}", e),
            None => f.debug_tuple("State").field(&self.0).finish(),
        }
    }
}

pub fn protect<F>(mut func: F) -> Result<Value, Error>
where
    F: FnMut() -> Value,
{
    // nested function as this is totally unsafe to call out of this context
    // arg should not be a VALUE, but a mutable pointer to F, cast to VALUE
    unsafe extern "C" fn call<F>(arg: VALUE) -> VALUE
    where
        F: FnMut() -> Value,
    {
        let closure = arg as *mut F;
        (*closure)().into_inner()
    }

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
        let closure = &mut func as *mut F as VALUE;
        rb_protect(Some(call::<F>), closure, &mut state as *mut _)
    };

    if state == 0 {
        Ok(Value::new(result))
    } else {
        Err(Error::Jump(State(state)))
    }
}

pub(crate) fn raise(e: Error) -> ! {
    match e {
        Error::Jump(state) => unsafe { state.resume() },
        Error::Error(class, msg) => {
            debug_assert_value!(class);
            let msg = CString::new(msg.into_owned()).unwrap();
            unsafe { rb_raise(class.into_inner(), msg.as_ptr()) }
            unreachable!()
        }
        Error::Exception(e) => {
            debug_assert_value!(e);
            unsafe { rb_exc_raise(e.into_inner()) }
            unreachable!()
        }
    }
}
