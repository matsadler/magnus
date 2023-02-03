use std::{fmt, ops::Deref};

use rb_sys::{rb_float_new_in_heap, VALUE};

use crate::{
    exception,
    into_value::IntoValue,
    numeric::Numeric,
    ruby_handle::RubyHandle,
    try_convert::TryConvertOwned,
    value::{private, NonZeroValue, ReprValue},
    Error, Float, RFloat, TryConvert, Value,
};

impl RubyHandle {
    #[inline]
    pub fn flonum_from_f64(&self, n: f64) -> Result<Flonum, RFloat> {
        Flonum::from_f64_impl(n)
            .ok_or_else(|| unsafe { RFloat::from_rb_value_unchecked(rb_float_new_in_heap(n)) })
    }
}

/// A Value known to be a flonum, Ruby's internal representation of lower
/// precision floating point numbers.
///
/// See also `Float`.
///
/// All [`Value`] methods should be available on this type through [`Deref`],
/// but some may be missed by this documentation.
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
    /// Panics if called from a non-Ruby thread.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Flonum};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(Flonum::from_f64(1.7272337110188893e-77).is_ok());
    /// // representable as a Float, but Flonum does not have enough precision
    /// assert!(Flonum::from_f64(1.7272337110188890e-77).is_err());
    /// ```
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
    /// assert_eq!(eval::<Flonum>("2.0").unwrap().to_f64(), 2.0);
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

impl Deref for Flonum {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
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
    fn into_value_with(self, _: &RubyHandle) -> Value {
        *self
    }
}

impl From<Flonum> for Value {
    fn from(val: Flonum) -> Self {
        *val
    }
}

impl Numeric for Flonum {}

unsafe impl private::ReprValue for Flonum {
    fn to_value(self) -> Value {
        *self
    }

    unsafe fn from_value_unchecked(val: Value) -> Self {
        Self(NonZeroValue::new_unchecked(val))
    }
}

impl ReprValue for Flonum {}

impl TryConvert for Flonum {
    fn try_convert(val: Value) -> Result<Self, Error> {
        let float = val.try_convert::<Float>()?;
        if let Some(flonum) = Flonum::from_value(*float) {
            Ok(flonum)
        } else {
            Err(Error::new(
                exception::range_error(),
                "float out of range for flonum",
            ))
        }
    }
}
impl TryConvertOwned for Flonum {}
