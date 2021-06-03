use std::{fmt, ops::Deref};

use crate::{
    ruby_sys::ruby_value_type,
    value::{NonZeroValue, Value},
};

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RRegexp(NonZeroValue);

impl RRegexp {
    /// # Safety
    ///
    /// val must not have been GC'd, return value must be kept on stack or
    /// otherwise protected from the GC.
    pub unsafe fn from_value(val: Value) -> Option<Self> {
        (val.rb_type() == ruby_value_type::RUBY_T_REGEXP)
            .then(|| Self(NonZeroValue::new_unchecked(val)))
    }
}

impl Deref for RRegexp {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
    }
}

impl fmt::Display for RRegexp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for RRegexp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.inspect() })
    }
}

impl From<RRegexp> for Value {
    fn from(val: RRegexp) -> Self {
        *val
    }
}
