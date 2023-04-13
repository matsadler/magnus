use std::{fmt, num::NonZeroI64};

use rb_sys::{rb_rational_den, rb_rational_new, rb_rational_num, ruby_value_type, VALUE};

use crate::{
    error::Error,
    integer::Integer,
    into_value::IntoValue,
    numeric::Numeric,
    try_convert::TryConvert,
    value::{
        private::{self, ReprValue as _},
        NonZeroValue, ReprValue, Value,
    },
    Ruby,
};

/// # `RRational`
///
/// See also the [`RRational`] type.
#[allow(missing_docs)]
impl Ruby {
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
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            (val.rb_type() == ruby_value_type::RUBY_T_RATIONAL)
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        Self(NonZeroValue::new_unchecked(Value::new(val)))
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
    /// use std::num::NonZeroI64;
    ///
    /// use magnus::RRational;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let rational = RRational::new(2, NonZeroI64::new(4).unwrap());
    /// assert_eq!(rational.to_string(), "1/2");
    /// ```
    #[cfg(feature = "friendly-api")]
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
    /// use magnus::RRational;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let rational = RRational::new(6, NonZeroI64::new(9).unwrap());
    /// assert_eq!(rational.num().to_i64().unwrap(), 2);
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
    /// use magnus::RRational;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let rational = RRational::new(6, NonZeroI64::new(9).unwrap());
    /// assert_eq!(rational.den().to_i64().unwrap(), 3);
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
