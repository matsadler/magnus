use std::fmt;

use rb_sys::{rb_float_new_in_heap, VALUE};

use crate::{
    into_value::IntoValue,
    numeric::Numeric,
    try_convert::TryConvertOwned,
    value::{
        private::{self, ReprValue as _},
        NonZeroValue, ReprValue,
    },
    Error, Float, RFloat, Ruby, TryConvert, Value,
};

/// # `Flonum`
///
/// Functions that can be used to create instances of Ruby's lower precision
/// floating point representation.
///
/// See also the [`Flonum`] type.
impl Ruby {
    /// Create a new `Flonum` from a `f64.`
    ///
    /// Returns `Ok(Flonum)` if `n` can be represented as a `Flonum`, otherwise
    /// returns `Err(RFloat)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let f = ruby.flonum_from_f64(1.7272337110188893e-77).unwrap();
    ///     rb_assert!(ruby, "f == 1.7272337110188893e-77", f);
    ///
    ///     // representable as a Float, but Flonum does not have enough precision
    ///     assert!(ruby.flonum_from_f64(1.7272337110188890e-77).is_err());
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn flonum_from_f64(&self, n: f64) -> Result<Flonum, RFloat> {
        Flonum::from_f64_impl(n)
            .ok_or_else(|| unsafe { RFloat::from_rb_value_unchecked(rb_float_new_in_heap(n)) })
    }
}

/// A Value known to be a flonum, Ruby's internal representation of lower
/// precision floating point numbers.
///
/// See also [`Float`] and [`RFloat`].
///
/// See the [`ReprValue`] trait for additional methods available on this type.
/// See [`Ruby`](Ruby#flonum) for methods to create a `Flonum`.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Flonum(NonZeroValue);

impl Flonum {
    /// Return `Some(Flonum)` if `val` is a `Flonum`, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Flonum};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(Flonum::from_value(eval("1.7272337110188893e-77").unwrap()).is_some());
    /// // representable as a Float, but Flonum does not have enough precision
    /// assert!(Flonum::from_value(eval("1.7272337110188890e-77").unwrap()).is_none());
    /// // not a Flonum
    /// assert!(Flonum::from_value(eval("1").unwrap()).is_none());
    /// ```
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            val.is_flonum()
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        Self(NonZeroValue::new_unchecked(Value::new(val)))
    }

    #[inline]
    pub(crate) fn from_f64_impl(d: f64) -> Option<Self> {
        let v = d.to_bits();
        let bits = v >> 60 & 0x7;
        if v != 0x3000000000000000 && bits.wrapping_sub(3) & !0x01 == 0 {
            return Some(unsafe { Self::from_rb_value_unchecked(v.rotate_left(3) & !0x01 | 0x02) });
        } else if v == 0 {
            return Some(unsafe { Self::from_rb_value_unchecked(0x8000000000000002) });
        }
        None
    }

    /// Create a new `Flonum` from a `f64.`
    ///
    /// Returns `Ok(Flonum)` if `n` can be represented as a `Flonum`, otherwise
    /// returns `Err(RFloat)`.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread. See [`Ruby::flonum_from_f64`]
    /// for the non-panicking version.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(deprecated)]
    /// use magnus::{rb_assert, Flonum};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let f = Flonum::from_f64(1.7272337110188893e-77).unwrap();
    /// rb_assert!("f == 1.7272337110188893e-77", f);
    ///
    /// // representable as a Float, but Flonum does not have enough precision
    /// assert!(Flonum::from_f64(1.7272337110188890e-77).is_err());
    /// ```
    #[cfg_attr(
        not(feature = "old-api"),
        deprecated(note = "please use `Ruby::flonum_from_f64` instead")
    )]
    #[inline]
    pub fn from_f64(n: f64) -> Result<Self, RFloat> {
        get_ruby!().flonum_from_f64(n)
    }

    /// Convert `self` to a `f64`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Flonum};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let f: Flonum = eval("2.0").unwrap();
    /// assert_eq!(f.to_f64(), 2.0);
    /// ```
    #[inline]
    pub fn to_f64(self) -> f64 {
        let v = self.as_rb_value();
        if v != 0x8000000000000002 {
            let b63 = v >> 63;
            let v = (2_u64.wrapping_sub(b63) | v & !0x03).rotate_right(3);
            return f64::from_bits(v);
        }
        0.0
    }
}

impl fmt::Display for Flonum {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for Flonum {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl IntoValue for Flonum {
    #[inline]
    fn into_value_with(self, _: &Ruby) -> Value {
        self.0.get()
    }
}

impl Numeric for Flonum {}

unsafe impl private::ReprValue for Flonum {}

impl ReprValue for Flonum {}

impl TryConvert for Flonum {
    fn try_convert(val: Value) -> Result<Self, Error> {
        let float = Float::try_convert(val)?;
        if let Some(flonum) = Flonum::from_value(float.as_value()) {
            Ok(flonum)
        } else {
            Err(Error::new(
                Ruby::get_with(val).exception_range_error(),
                "float out of range for flonum",
            ))
        }
    }
}
unsafe impl TryConvertOwned for Flonum {}
