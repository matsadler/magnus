use std::fmt;

use rb_sys::{
    rb_complex_abs, rb_complex_arg, rb_complex_conjugate, rb_complex_imag, rb_complex_new,
    rb_complex_new_polar, rb_complex_real, ruby_value_type, VALUE,
};

use crate::{
    error::{protect, Error},
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

/// A Value pointer to a RComplex struct, Ruby's internal representation of
/// complex numbers.
///
/// See the [`ReprValue`] trait for additional methods available on this type.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RComplex(NonZeroValue);

impl RComplex {
    /// Return `Some(RComplex)` if `val` is a `RComplex`, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RComplex};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(RComplex::from_value(eval("2+1i").unwrap()).is_some());
    /// assert!(RComplex::from_value(eval("3").unwrap()).is_none());
    /// ```
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            (val.rb_type() == ruby_value_type::RUBY_T_COMPLEX)
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        Self(NonZeroValue::new_unchecked(Value::new(val)))
    }

    /// Create a new `RComplex`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, RComplex, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let complex = RComplex::new(ruby.integer_from_i64(2), ruby.integer_from_i64(1));
    ///     assert_eq!(complex.to_string(), "2+1i");
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn new<T, U>(real: T, imag: U) -> RComplex
    where
        T: Numeric,
        U: Numeric,
    {
        unsafe {
            RComplex::from_rb_value_unchecked(rb_complex_new(
                real.as_rb_value(),
                imag.as_rb_value(),
            ))
        }
    }

    /// Create a new `RComplex` using polar representation.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, RComplex, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let complex = RComplex::polar(ruby.integer_from_i64(2), ruby.integer_from_i64(3))?;
    ///     assert_eq!(
    ///         complex.to_string(),
    ///         "-1.9799849932008908+0.2822400161197344i"
    ///     );
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn polar<T, U>(real: T, imag: U) -> Result<RComplex, Error>
    where
        T: Numeric,
        U: Numeric,
    {
        protect(|| unsafe {
            RComplex::from_rb_value_unchecked(rb_complex_new_polar(
                real.as_rb_value(),
                imag.as_rb_value(),
            ))
        })
    }

    /// Returns the real part of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, RComplex, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let complex = RComplex::new(ruby.integer_from_i64(9), ruby.integer_from_i64(-4));
    ///     assert_eq!(complex.real::<i64>()?, 9);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn real<T>(self) -> Result<T, Error>
    where
        T: TryConvert,
    {
        let val = unsafe { Value::new(rb_complex_real(self.as_rb_value())) };
        T::try_convert(val)
    }

    /// Returns the imaginary part of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, RComplex, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let complex = RComplex::new(ruby.integer_from_i64(9), ruby.integer_from_i64(-4));
    ///     assert_eq!(complex.imag::<i64>()?, -4);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn imag<T>(self) -> Result<T, Error>
    where
        T: TryConvert,
    {
        let val = unsafe { Value::new(rb_complex_imag(self.as_rb_value())) };
        T::try_convert(val)
    }

    /// Returns the complex conjugate.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, RComplex, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let complex = RComplex::new(ruby.integer_from_i64(1), ruby.integer_from_i64(2));
    ///     assert_eq!(complex.conjugate().to_string(), "1-2i");
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn conjugate(self) -> Self {
        unsafe { Self::from_rb_value_unchecked(rb_complex_conjugate(self.as_rb_value())) }
    }

    /// Returns the absolute (or the magnitude) of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, RComplex, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let complex = RComplex::new(ruby.integer_from_i64(3), ruby.integer_from_i64(-4));
    ///     assert_eq!(complex.abs(), 5.0);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn abs(self) -> f64 {
        unsafe { Float::from_rb_value_unchecked(rb_complex_abs(self.as_rb_value())).to_f64() }
    }

    /// Returns the argument (or the angle) of the polar form of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::f64::consts::PI;
    ///
    /// use magnus::{Error, RComplex, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let complex = RComplex::polar(ruby.integer_from_i64(3), ruby.float_from_f64(PI / 2.0))?;
    ///     assert_eq!(complex.arg(), 1.5707963267948966);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn arg(self) -> f64 {
        unsafe { Float::from_rb_value_unchecked(rb_complex_arg(self.as_rb_value())).to_f64() }
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
    #[inline]
    fn into_value_with(self, _: &Ruby) -> Value {
        self.0.get()
    }
}

unsafe impl private::ReprValue for RComplex {}

impl Numeric for RComplex {}

impl ReprValue for RComplex {}

impl TryConvert for RComplex {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Self::from_value(val).ok_or_else(|| {
            Error::new(
                Ruby::get_with(val).exception_type_error(),
                format!("no implicit conversion of {} into Complex", unsafe {
                    val.classname()
                },),
            )
        })
    }
}
