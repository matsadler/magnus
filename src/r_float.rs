use std::fmt;

use rb_sys::{VALUE, rb_float_new, rb_float_value, ruby_value_type};

#[cfg(ruby_use_flonum)]
use crate::value::Flonum;
use crate::{
    Ruby,
    error::Error,
    float::Float,
    into_value::IntoValue,
    numeric::Numeric,
    try_convert::TryConvert,
    value::{
        NonZeroValue, ReprValue, Value,
        private::{self, ReprValue as _},
    },
};

/// # `RFloat`
///
/// Functions that can be used to create Ruby `Float`s.
///
/// See also the [`RFloat`] type.
impl Ruby {
    /// Create a new `RFloat` from an `f64.`
    ///
    /// Returns `Ok(RFloat)` if `n` requires a high precision float, otherwise
    /// returns `Err(Flonum)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby, rb_assert};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let f = ruby.r_float_from_f64(1.7272337110188890e-77).unwrap();
    ///     rb_assert!(ruby, "f == 1.7272337110188890e-77", f);
    ///
    ///     // can fit within a Flonum, so does not require an RFloat
    ///     assert!(ruby.r_float_from_f64(1.7272337110188893e-77).is_err());
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[cfg(ruby_use_flonum)]
    pub fn r_float_from_f64(&self, n: f64) -> Result<RFloat, Flonum> {
        unsafe {
            let val = Value::new(rb_float_new(n));
            RFloat::from_value(val)
                .ok_or_else(|| Flonum::from_rb_value_unchecked(val.as_rb_value()))
        }
    }

    /// Create a new `RFloat` from an `f64.`
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby, rb_assert};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let f = ruby.r_float_from_f64(1.7272337110188893e-77).unwrap();
    ///     rb_assert!(ruby, "f == 1.7272337110188893e-77", f);
    ///
    ///     let f = ruby.r_float_from_f64(1.7272337110188890e-77).unwrap();
    ///     rb_assert!(ruby, "f == 1.7272337110188890e-77", f);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[cfg(not(ruby_use_flonum))]
    pub fn r_float_from_f64(&self, n: f64) -> Result<RFloat, RFloat> {
        unsafe { Ok(RFloat::from_rb_value_unchecked(rb_float_new(n))) }
    }
}

/// A Value pointer to an RFloat struct, Ruby's internal representation of
/// high precision floating point numbers.
///
/// See also [`Float`] and [`Flonum`].
///
/// See the [`ReprValue`] trait for additional methods available on this type.
/// See [`Ruby`](Ruby#rfloat) for methods to create an `RFloat`.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RFloat(NonZeroValue);

impl RFloat {
    /// Return `Some(RFloat)` if `val` is a `RFloat`, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{RFloat, eval};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(RFloat::from_value(eval("1.7272337110188890e-77").unwrap()).is_some());
    /// // can fit within a Flonum, so does not require an RFloat
    /// assert!(RFloat::from_value(eval("1.7272337110188893e-77").unwrap()).is_none());
    /// // not an RFloat
    /// assert!(RFloat::from_value(eval("1").unwrap()).is_none());
    /// ```
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            (val.rb_type() == ruby_value_type::RUBY_T_FLOAT
                && (!cfg!(ruby_use_flonum) || !val.is_flonum()))
            .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        unsafe { Self(NonZeroValue::new_unchecked(Value::new(val))) }
    }

    /// Create a new `RFloat` from an `f64.`
    ///
    /// Returns `Ok(RFloat)` if `n` requires a high precision float, otherwise
    /// returns `Err(Flonum)`.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread. See [`Ruby::r_float_from_f64`]
    /// for the non-panicking version.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(deprecated)]
    /// use magnus::{RFloat, rb_assert};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let f = RFloat::from_f64(1.7272337110188890e-77).unwrap();
    /// rb_assert!("f == 1.7272337110188890e-77", f);
    ///
    /// // can fit within a Flonum, so does not require an RFloat
    /// assert!(RFloat::from_f64(1.7272337110188893e-77).is_err());
    /// ```
    #[cfg_attr(
        not(feature = "old-api"),
        deprecated(note = "please use `Ruby::r_float_from_f64` instead")
    )]
    #[cfg_attr(docsrs, doc(cfg(feature = "old-api")))]
    #[cfg(ruby_use_flonum)]
    #[inline]
    pub fn from_f64(n: f64) -> Result<Self, Flonum> {
        get_ruby!().r_float_from_f64(n)
    }

    /// Create a new `RFloat` from an `f64.`
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread. See [`Ruby::r_float_from_f64`]
    /// for the non-panicking version.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(deprecated)]
    /// use magnus::{RFloat, rb_assert};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let f = RFloat::from_f64(1.7272337110188893e-77).unwrap();
    /// rb_assert!("f == 1.7272337110188893e-77", f);
    ///
    /// let f = RFloat::from_f64(1.7272337110188890e-77).unwrap();
    /// rb_assert!("f == 1.7272337110188890e-77", f);
    /// ```
    #[cfg_attr(
        not(feature = "old-api"),
        deprecated(note = "please use `Ruby::r_float_from_f64` instead")
    )]
    #[cfg_attr(docsrs, doc(cfg(feature = "old-api")))]
    #[cfg(not(ruby_use_flonum))]
    #[inline]
    pub fn from_f64(n: f64) -> Result<Self, Self> {
        get_ruby!().r_float_from_f64(n)
    }

    /// Convert `self` to a `f64`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{RFloat, eval};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let f: RFloat = eval("1.7272337110188890e-77").unwrap();
    /// assert_eq!(f.to_f64(), 1.7272337110188890e-77);
    /// ```
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
    #[inline]
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
