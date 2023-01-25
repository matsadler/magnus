use crate::{ruby_handle::RubyHandle, value::Value};

impl RubyHandle {
    #[allow(clippy::wrong_self_convention)]
    pub fn into_value<T>(&self, val: T) -> Value
    where
        T: IntoValue,
    {
        val.into_value_with(self)
    }
}

pub trait IntoValue: Sized {
    fn into_value(self) -> Value {
        self.into_value_with(&get_ruby!())
    }

    unsafe fn into_value_unchecked(self) -> Value {
        self.into_value_with(&RubyHandle::get_unchecked())
    }

    fn into_value_with(self, handle: &RubyHandle) -> Value;
}

pub unsafe trait IntoValueFromNative: IntoValue {}
