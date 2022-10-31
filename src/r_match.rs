use std::{fmt, ops::Deref};

use rb_sys::ruby_value_type;

use crate::{
    error::Error,
    exception,
    object::Object,
    try_convert::TryConvert,
    value::{private, NonZeroValue, ReprValue, Value},
};

/// A Value pointer to a RMatch struct, Ruby's internal representation of the
/// MatchData returned from a regex match.
///
/// All [`Value`] methods should be available on this type through [`Deref`],
/// but some may be missed by this documentation.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RMatch(NonZeroValue);

impl RMatch {
    /// Return `Some(RMatch)` if `val` is a `RMatch`, `None` otherwise.
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            (val.rb_type() == ruby_value_type::RUBY_T_MATCH)
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }
}

impl Deref for RMatch {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
    }
}

impl fmt::Display for RMatch {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for RMatch {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl From<RMatch> for Value {
    fn from(val: RMatch) -> Self {
        *val
    }
}

impl Object for RMatch {}

unsafe impl private::ReprValue for RMatch {
    fn to_value(self) -> Value {
        *self
    }

    unsafe fn from_value_unchecked(val: Value) -> Self {
        Self(NonZeroValue::new_unchecked(val))
    }
}

impl ReprValue for RMatch {}

impl TryConvert for RMatch {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Self::from_value(val).ok_or_else(|| {
            Error::new(
                exception::type_error(),
                format!("no implicit conversion of {} into MatchData", unsafe {
                    val.classname()
                },),
            )
        })
    }
}
