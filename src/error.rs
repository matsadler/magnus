use std::{any::Any, borrow::Cow, ffi::CString, fmt, ops::Deref, os::raw::c_int};

use crate::{
    debug_assert_value,
    exception::{Exception, ExceptionClass},
    module::Module,
    ruby_sys::{
        rb_eArgError, rb_eEncodingError, rb_eFatal, rb_eRangeError, rb_eStopIteration,
        rb_eTypeError, rb_ensure, rb_errinfo, rb_exc_raise, rb_jump_tag, rb_protect, rb_raise,
        rb_set_errinfo, ruby_special_consts, VALUE,
    },
    value::{Qnil, Value},
};

#[derive(Debug)]
pub enum Error {
    Jump(Tag),
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

    pub fn argument_error<T>(msg: T) -> Self
    where
        T: Into<Cow<'static, str>>,
    {
        Self::Error(
            unsafe { ExceptionClass::from_rb_value_unchecked(rb_eArgError) },
            msg.into(),
        )
    }

    pub fn range_error<T>(msg: T) -> Self
    where
        T: Into<Cow<'static, str>>,
    {
        Self::Error(
            unsafe { ExceptionClass::from_rb_value_unchecked(rb_eRangeError) },
            msg.into(),
        )
    }

    pub fn type_error<T>(msg: T) -> Self
    where
        T: Into<Cow<'static, str>>,
    {
        Self::Error(
            unsafe { ExceptionClass::from_rb_value_unchecked(rb_eTypeError) },
            msg.into(),
        )
    }

    pub fn encoding_error<T>(msg: T) -> Self
    where
        T: Into<Cow<'static, str>>,
    {
        Self::Error(
            unsafe { ExceptionClass::from_rb_value_unchecked(rb_eEncodingError) },
            msg.into(),
        )
    }

    pub fn stop_iteration<T>(msg: T) -> Self
    where
        T: Into<Cow<'static, str>>,
    {
        Self::Error(
            unsafe { ExceptionClass::from_rb_value_unchecked(rb_eStopIteration) },
            msg.into(),
        )
    }

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

    pub(crate) fn from_panic(e: Box<dyn Any + Send + 'static>) -> Self {
        let msg = if let Some(&m) = e.downcast_ref::<&'static str>() {
            m.into()
        } else if let Some(m) = e.downcast_ref::<String>() {
            m.clone().into()
        } else {
            "panic".into()
        };
        Self::Error(
            unsafe { ExceptionClass::from_rb_value_unchecked(rb_eFatal) },
            msg,
        )
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

#[derive(Debug)]
#[repr(i32)]
pub enum Tag {
    None = 0,
    Return = 1,
    Break = 2,
    Next = 3,
    Retry = 4,
    Redo = 5,
    Raise = 6,
    Throw = 7,
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
            Self::None => write!(f, "None"),
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

    let mut state = Tag::None;
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
        rb_protect(
            Some(call::<F>),
            closure,
            &mut state as *mut Tag as *mut c_int,
        )
    };

    match state {
        Tag::None => Ok(Value::new(result)),
        Tag::Raise => unsafe {
            let ex = Exception::from_rb_value_unchecked(rb_errinfo());
            rb_set_errinfo(Qnil::new().as_rb_value());
            Err(Error::Exception(ex))
        },
        other => Err(Error::Jump(other)),
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
        let mut some_func = Some(func);
        let func_closure = &mut some_func as *mut Option<F1> as VALUE;
        let mut some_ensure = Some(ensure);
        let ensure_closure = &mut some_ensure as *mut Option<F2> as VALUE;
        rb_ensure(
            Some(call_func::<F1>),
            func_closure,
            Some(call_ensure::<F2>),
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
