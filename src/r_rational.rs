use std::{fmt, num::NonZeroI64};

use rb_sys::{VALUE, rb_rational_den, rb_rational_new, rb_rational_num, ruby_value_type};

use crate::{
    Ruby,
    error::Error,
    integer::Integer,
    into_value::IntoValue,
    numeric::Numeric,
    try_convert::TryConvert,
    value::{
        NonZeroValue, ReprValue, Value,
        private::{self, ReprValue as _},
    },
};

/// # `RRational`
///
/// Functions that can be used to create Ruby `Rational`s.
///
/// See also the [`RRational`] type.
impl Ruby {
    /// Create a new `RRational`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::num::NonZeroI64;
    ///
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let rational = ruby.rational_new(2, NonZeroI64::new(4).unwrap());
    ///     assert_eq!(rational.to_string(), "1/2");
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn rational_new(&self, num: i64, den: NonZeroI64) -> RRational {
        let num = self.into_value(num);
        let den = self.into_value(den.get());
        unsafe {
            RRational::from_rb_value_unchecked(rb_rational_new(
                num.as_rb_value(),
                den.as_rb_value(),
            ))
        }
    }
}

/// A Value pointer to a RRational struct, Ruby's internal representation of
/// rational numbers.
///
/// See the [`ReprValue`] trait for additional methods available on this type.
/// See [`Ruby`](Ruby#rrational) for methods to create an `RRational`.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RRational(NonZeroValue);

impl RRational {
    /// Return `Some(RRational)` if `val` is a `RRational`, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{RRational, eval};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(RRational::from_value(eval("1/2r").unwrap()).is_some());
    /// assert!(RRational::from_value(eval("0.5").unwrap()).is_none());
    /// ```
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            (val.rb_type() == ruby_value_type::RUBY_T_RATIONAL)
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        unsafe { Self(NonZeroValue::new_unchecked(Value::new(val))) }
    }

    /// Create a new `RRational`.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread. See [`Ruby::rational_new`] for
    /// the non-panicking version.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(deprecated)]
    /// use std::num::NonZeroI64;
    ///
    /// use magnus::RRational;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let rational = RRational::new(2, NonZeroI64::new(4).unwrap());
    /// assert_eq!(rational.to_string(), "1/2");
    /// ```
    #[cfg_attr(
        not(feature = "old-api"),
        deprecated(note = "please use `Ruby::rational_new` instead")
    )]
    #[cfg_attr(docsrs, doc(cfg(feature = "old-api")))]
    #[inline]
    pub fn new(num: i64, den: NonZeroI64) -> Self {
        get_ruby!().rational_new(num, den)
    }

    /// Returns `self`'s numerator.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::num::NonZeroI64;
    ///
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let rational = ruby.rational_new(6, NonZeroI64::new(9).unwrap());
    ///     assert_eq!(rational.num().to_i64()?, 2);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn num(self) -> Integer {
        unsafe { Integer::from_rb_value_unchecked(rb_rational_num(self.as_rb_value())) }
    }

    /// Returns `self`'s denominator.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::num::NonZeroI64;
    ///
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let rational = ruby.rational_new(6, NonZeroI64::new(9).unwrap());
    ///     assert_eq!(rational.den().to_i64()?, 3);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn den(self) -> Integer {
        unsafe { Integer::from_rb_value_unchecked(rb_rational_den(self.as_rb_value())) }
    }
}

impl fmt::Display for RRational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for RRational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl IntoValue for RRational {
    #[inline]
    fn into_value_with(self, _: &Ruby) -> Value {
        self.0.get()
    }
}

unsafe impl private::ReprValue for RRational {}

impl Numeric for RRational {}

impl ReprValue for RRational {}

impl TryConvert for RRational {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Self::from_value(val).ok_or_else(|| {
            Error::new(
                Ruby::get_with(val).exception_type_error(),
                format!("no implicit conversion of {} into Rational", unsafe {
                    val.classname()
                },),
            )
        })
    }
}
