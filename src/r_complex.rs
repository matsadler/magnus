use std::{fmt, ops::Deref};

use rb_sys::ruby_value_type;

use crate::{
    error::Error,
    exception,
    into_value::IntoValue,
    ruby_handle::RubyHandle,
    try_convert::TryConvert,
    value::{private, NonZeroValue, ReprValue, Value},
};

/// A Value pointer to a RComplex struct, Ruby's internal representation of
/// complex numbers.
///
/// All [`Value`] methods should be available on this type through [`Deref`],
/// but some may be missed by this documentation.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RComplex(NonZeroValue);

impl RComplex {
    /// Return `Some(RComplex)` if `val` is a `RComplex`, `None` otherwise.
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            (val.rb_type() == ruby_value_type::RUBY_T_COMPLEX)
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }
}

impl Deref for RComplex {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
    }
}

impl fmt::Display for RComplex {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for RComplex {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl IntoValue for RComplex {
    fn into_value(self, _: &RubyHandle) -> Value {
        *self
    }
}

impl From<RComplex> for Value {
    fn from(val: RComplex) -> Self {
        *val
    }
}

unsafe impl private::ReprValue for RComplex {
    fn to_value(self) -> Value {
        *self
    }

    unsafe fn from_value_unchecked(val: Value) -> Self {
        Self(NonZeroValue::new_unchecked(val))
    }
}

impl ReprValue for RComplex {}

impl TryConvert for RComplex {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Self::from_value(val).ok_or_else(|| {
            Error::new(
                exception::type_error(),
                format!("no implicit conversion of {} into Complex", unsafe {
                    val.classname()
                },),
            )
        })
    }
}
