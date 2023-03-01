use std::fmt;

use rb_sys::{rb_float_new, rb_float_value, ruby_value_type, VALUE};

#[cfg(ruby_use_flonum)]
use crate::value::Flonum;
use crate::{
    error::Error,
    float::Float,
    into_value::IntoValue,
    numeric::Numeric,
    try_convert::TryConvert,
    value::{
        private::{self, ReprValue as _},
        NonZeroValue, ReprValue, Value,
    },
    Ruby,
};

#[allow(missing_docs)]
impl Ruby {
    #[cfg(ruby_use_flonum)]
    pub fn r_float_from_f64(&self, n: f64) -> Result<RFloat, Flonum> {
        unsafe {
            let val = Value::new(rb_float_new(n));
            RFloat::from_value(val)
                .ok_or_else(|| Flonum::from_rb_value_unchecked(val.as_rb_value()))
        }
    }

    #[cfg(not(ruby_use_flonum))]
    pub fn r_float_from_f64(&self, n: f64) -> Result<RFloat, RFloat> {
        unsafe { Ok(RFloat::from_rb_value_unchecked(rb_float_new(n))) }
    }
}

/// A Value pointer to a RFloat struct, Ruby's internal representation of
/// high precision floating point numbers.
///
/// See the [`ReprValue`] trait for additional methods available on this type.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RFloat(NonZeroValue);

impl RFloat {
    /// Return `Some(RFloat)` if `val` is a `RFloat`, `None` otherwise.
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            (val.rb_type() == ruby_value_type::RUBY_T_FLOAT)
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        Self(NonZeroValue::new_unchecked(Value::new(val)))
    }

    /// Create a new `RFloat` from an `f64.`
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread.
    ///
    /// Returns `Ok(RFloat)` if `n` requires a high precision float, otherwise
    /// returns `Err(Fixnum)`.
    #[cfg(ruby_use_flonum)]
    #[inline]
    pub fn from_f64(n: f64) -> Result<Self, Flonum> {
        get_ruby!().r_float_from_f64(n)
    }

    /// Create a new `RFloat` from an `f64.`
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread.
    #[cfg(not(ruby_use_flonum))]
    #[inline]
    pub fn from_f64(n: f64) -> Result<Self, Self> {
        get_ruby!().r_float_from_f64(n)
    }

    /// Convert `self` to a `f64`.
    pub fn to_f64(self) -> f64 {
        debug_assert_value!(self);
        unsafe { rb_float_value(self.as_rb_value()) }
    }
}

impl fmt::Display for RFloat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for RFloat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl IntoValue for RFloat {
    fn into_value_with(self, _: &Ruby) -> Value {
        self.0.get()
    }
}

impl Numeric for RFloat {}

unsafe impl private::ReprValue for RFloat {}

impl ReprValue for RFloat {}

impl TryConvert for RFloat {
    fn try_convert(val: Value) -> Result<Self, Error> {
        let float = Float::try_convert(val)?;
        if let Some(rfloat) = RFloat::from_value(float.as_value()) {
            Ok(rfloat)
        } else {
            Err(Error::new(
                Ruby::get_with(val).exception_range_error(),
                "float in range for flonum",
            ))
        }
    }
}
