use std::{fmt, ops::Deref};

use crate::{
    debug_assert_value,
    error::{protect, Error},
    ruby_sys::{
        rb_float_new, rb_float_value, rb_to_float, ruby_special_consts, ruby_value_type, VALUE,
    },
    try_convert::TryConvert,
    value::{private, NonZeroValue, ReprValue, Value},
};

/// A type wrapping either a [`Flonum`](`crate::value::Flonum`) value or a
/// Value known to be an instance of Float.
///
/// All [`Value`] methods should be available on this type through [`Deref`],
/// but some may be missed by this documentation.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Float(NonZeroValue);

impl Float {
    /// Return `Some(Float)` if `val` is a `Float`, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Float};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(Float::from_value(eval("1.7272337110188893e-77").unwrap()).is_some());
    /// assert!(Float::from_value(eval("1.7272337110188890e-77").unwrap()).is_some());
    /// ```
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            if val.as_rb_value() & ruby_special_consts::RUBY_FLONUM_MASK as VALUE
                == ruby_special_consts::RUBY_FLONUM_FLAG as VALUE
            {
                return Some(Self(NonZeroValue::new_unchecked(val)));
            }
            debug_assert_value!(val);
            (val.rb_type() == ruby_value_type::RUBY_T_FLOAT)
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        Self(NonZeroValue::new_unchecked(Value::new(val)))
    }

    /// Create a new `Float` from an `f64`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Float};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let res: bool = eval!("f == 1.7272337110188893e-77", f = Float::from_f64(1.7272337110188893e-77)).unwrap();
    /// assert!(res);
    /// let res: bool = eval!("f == 1.7272337110188890e-77", f = Float::from_f64(1.7272337110188890e-77)).unwrap();
    /// assert!(res);
    /// ```
    pub fn from_f64(n: f64) -> Self {
        unsafe { Float::from_rb_value_unchecked(rb_float_new(n)) }
    }

    /// Convert `self` to a `f64`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Float};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert_eq!(eval::<Float>("2.0").unwrap().to_f64(), 2.0);
    /// ```
    pub fn to_f64(self) -> f64 {
        unsafe { rb_float_value(self.as_rb_value()) }
    }
}

impl Deref for Float {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
    }
}

impl fmt::Display for Float {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for Float {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl From<Float> for Value {
    fn from(val: Float) -> Self {
        *val
    }
}

unsafe impl private::ReprValue for Float {
    fn to_value(self) -> Value {
        *self
    }

    unsafe fn from_value_unchecked(val: Value) -> Self {
        Self(NonZeroValue::new_unchecked(val))
    }
}

impl ReprValue for Float {}

impl TryConvert for Float {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        unsafe {
            match Self::from_value(*val) {
                Some(i) => Ok(i),
                None => protect(|| {
                    debug_assert_value!(val);
                    Value::new(rb_to_float(val.as_rb_value()))
                })
                .map(|res| Self::from_rb_value_unchecked(res.as_rb_value())),
            }
        }
    }
}
