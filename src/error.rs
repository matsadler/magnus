use std::{any::Any, borrow::Cow, ffi::CString};

use crate::{
    debug_assert_value,
    exception::{Exception, ExceptionClass},
    ruby_sys::{rb_eRangeError, rb_eScriptError, rb_eTypeError, rb_exc_raise, rb_raise},
    State,
};

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
