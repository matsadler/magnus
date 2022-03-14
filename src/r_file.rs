use std::{fmt, ops::Deref};

use crate::{
    error::Error,
    exception,
    object::Object,
    ruby_sys::ruby_value_type,
    try_convert::TryConvert,
    value::{NonZeroValue, Value},
};

/// A Value pointer to a RFile struct, Ruby's internal representation of files.
///
/// All [`Value`] methods should be available on this type through [`Deref`],
/// but some may be missed by this documentation.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RFile(NonZeroValue);

impl RFile {
    /// Return `Some(RFile)` if `val` is a `RFile`, `None` otherwise.
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            (val.rb_type() == ruby_value_type::RUBY_T_FILE)
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }
}

impl Deref for RFile {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
    }
}

impl fmt::Display for RFile {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for RFile {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl From<RFile> for Value {
    fn from(val: RFile) -> Self {
        *val
    }
}

impl Object for RFile {}

impl TryConvert for RFile {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        Self::from_value(*val).ok_or_else(|| {
            Error::new(
                exception::type_error(),
                format!("no implicit conversion of {} into File", unsafe {
                    val.classname()
                },),
            )
        })
    }
}
