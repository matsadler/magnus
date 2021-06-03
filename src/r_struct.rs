use std::{fmt, ops::Deref};

use crate::{
    object::Object,
    ruby_sys::ruby_value_type,
    value::{NonZeroValue, Value},
};

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RStruct(NonZeroValue);

impl RStruct {
    /// # Safety
    ///
    /// val must not have been GC'd, return value must be kept on stack or
    /// otherwise protected from the GC.
    pub unsafe fn from_value(val: Value) -> Option<Self> {
        (val.rb_type() == ruby_value_type::RUBY_T_STRUCT)
            .then(|| Self(NonZeroValue::new_unchecked(val)))
    }
}

impl Deref for RStruct {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
    }
}

impl fmt::Display for RStruct {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for RStruct {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.inspect() })
    }
}

impl From<RStruct> for Value {
    fn from(val: RStruct) -> Self {
        *val
    }
}

impl Object for RStruct {}
