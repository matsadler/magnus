use std::borrow::Cow;

use crate::{
    exception::{Exception, ExceptionClass},
    ruby_sys::rb_eRangeError,
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
