use std::{convert::TryFrom, fmt};

use rb_sys::{rb_ll2inum, rb_to_int, rb_ull2inum, ruby_special_consts, ruby_value_type, VALUE};

use crate::{
    error::{protect, Error},
    exception,
    into_value::IntoValue,
    numeric::Numeric,
    r_bignum::RBignum,
    try_convert::TryConvert,
    value::{
        private::{self, ReprValue as _},
        Fixnum, NonZeroValue, ReprValue, Value,
    },
    Ruby,
};

pub(crate) enum IntegerType {
    Fixnum(Fixnum),
    Bignum(RBignum),
}

impl Ruby {
    #[inline]
    pub fn integer_from_i64(&self, n: i64) -> Integer {
        unsafe {
            Integer::from_rb_value_unchecked(
                Fixnum::from_i64_impl(n)
                    .map(|f| f.as_rb_value())
                    .unwrap_or_else(|| rb_ll2inum(n)),
            )
        }
    }

    #[inline]
    pub fn integer_from_u64(&self, n: u64) -> Integer {
        unsafe {
            Integer::from_rb_value_unchecked(
                Fixnum::from_i64_impl(i64::try_from(n).unwrap_or(i64::MAX))
                    .map(|f| f.as_rb_value())
                    .unwrap_or_else(|| rb_ull2inum(n)),
            )
        }
    }
}

/// A type wrapping either a [`Fixnum`] or a [`RBignum`].
///
/// See the [`ReprValue`] trait for additional methods available on this type.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Integer(NonZeroValue);

impl Integer {
    /// Return `Some(Integer)` if `val` is an `Integer`, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Integer};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(Integer::from_value(eval("0").unwrap()).is_some());
    /// assert!(Integer::from_value(eval("9223372036854775807").unwrap()).is_some());
    /// // not an int
    /// assert!(Integer::from_value(eval("1.23").unwrap()).is_none());
    /// ```
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            if val.as_rb_value() & ruby_special_consts::RUBY_FIXNUM_FLAG as VALUE != 0 {
                return Some(Self(NonZeroValue::new_unchecked(val)));
            }
            debug_assert_value!(val);
            (val.rb_type() == ruby_value_type::RUBY_T_BIGNUM)
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        Self(NonZeroValue::new_unchecked(Value::new(val)))
    }

    pub(crate) fn integer_type(self) -> IntegerType {
        unsafe {
            if self.as_rb_value() & ruby_special_consts::RUBY_FIXNUM_FLAG as VALUE != 0 {
                IntegerType::Fixnum(Fixnum::from_rb_value_unchecked(self.as_rb_value()))
            } else {
                IntegerType::Bignum(RBignum::from_rb_value_unchecked(self.as_rb_value()))
            }
        }
    }

    /// Create a new `Integer` from an `i64.`
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Integer};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let res: bool = eval!("i == 0", i = Integer::from_i64(0)).unwrap();
    /// assert!(res);
    /// let res: bool = eval!("i == 4611686018427387904", i = Integer::from_i64(4611686018427387904)).unwrap();
    /// assert!(res);
    /// let res: bool = eval!("i == -4611686018427387905", i = Integer::from_i64(-4611686018427387905)).unwrap();
    /// assert!(res);
    /// ```
    #[inline]
    pub fn from_i64(n: i64) -> Self {
        get_ruby!().integer_from_i64(n)
    }

    /// Create a new `Integer` from a `u64.`
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Integer};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let res: bool = eval!("i == 0", i = Integer::from_u64(0)).unwrap();
    /// assert!(res);
    /// let res: bool = eval!("i == 4611686018427387904", i = Integer::from_u64(4611686018427387904)).unwrap();
    /// assert!(res);
    /// ```
    #[inline]
    pub fn from_u64(n: u64) -> Self {
        get_ruby!().integer_from_u64(n)
    }

    /// Convert `self` to an `i8`. Returns `Err` if `self` is out of range for
    /// `i8`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Integer};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert_eq!(eval::<Integer>("127").unwrap().to_i8().unwrap(), 127);
    /// assert!(eval::<Integer>("128").unwrap().to_i8().is_err());
    /// assert_eq!(eval::<Integer>("-128").unwrap().to_i8().unwrap(), -128);
    /// assert!(eval::<Integer>("-129").unwrap().to_i8().is_err());
    /// ```
    #[inline]
    pub fn to_i8(self) -> Result<i8, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => fix.to_i8(),
            IntegerType::Bignum(_) => Err(Error::new(
                exception::range_error(),
                "bignum too big to convert into `i8`",
            )),
        }
    }

    /// Convert `self` to an `i16`. Returns `Err` if `self` is out of range for
    /// `i16`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Integer};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert_eq!(eval::<Integer>("32767").unwrap().to_i16().unwrap(), 32767);
    /// assert!(eval::<Integer>("32768").unwrap().to_i16().is_err());
    /// assert_eq!(eval::<Integer>("-32768").unwrap().to_i16().unwrap(), -32768);
    /// assert!(eval::<Integer>("-32769").unwrap().to_i16().is_err());
    /// ```
    #[inline]
    pub fn to_i16(self) -> Result<i16, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => fix.to_i16(),
            IntegerType::Bignum(_) => Err(Error::new(
                exception::range_error(),
                "bignum too big to convert into `i16`",
            )),
        }
    }

    /// Convert `self` to an `i32`. Returns `Err` if `self` is out of range for
    /// `i32`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Integer};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert_eq!(eval::<Integer>("2147483647").unwrap().to_i32().unwrap(), 2147483647);
    /// assert!(eval::<Integer>("2147483648").unwrap().to_i32().is_err());
    /// assert_eq!(eval::<Integer>("-2147483648").unwrap().to_i32().unwrap(), -2147483648);
    /// assert!(eval::<Integer>("-2147483649").unwrap().to_i32().is_err());
    /// ```
    #[inline]
    pub fn to_i32(self) -> Result<i32, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => fix.to_i32(),
            IntegerType::Bignum(big) => big.to_i32(),
        }
    }

    /// Convert `self` to an `i64`. Returns `Err` if `self` is out of range for
    /// `i64`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Integer};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert_eq!(eval::<Integer>("4611686018427387903").unwrap().to_i64().unwrap(), 4611686018427387903);
    /// assert_eq!(eval::<Integer>("-4611686018427387904").unwrap().to_i64().unwrap(), -4611686018427387904);
    /// assert!(eval::<Integer>("9223372036854775808").unwrap().to_i64().is_err());
    /// assert!(eval::<Integer>("-9223372036854775809").unwrap().to_i64().is_err());
    /// ```
    #[inline]
    pub fn to_i64(self) -> Result<i64, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => Ok(fix.to_i64()),
            IntegerType::Bignum(big) => big.to_i64(),
        }
    }

    /// Convert `self` to an `isize`. Returns `Err` if `self` is out of range
    /// for `isize`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Integer};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert_eq!(eval::<Integer>("4611686018427387903").unwrap().to_isize().unwrap(), 4611686018427387903);
    /// assert_eq!(eval::<Integer>("-4611686018427387904").unwrap().to_isize().unwrap(), -4611686018427387904);
    /// ```
    #[inline]
    pub fn to_isize(self) -> Result<isize, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => Ok(fix.to_isize()),
            IntegerType::Bignum(big) => big.to_isize(),
        }
    }

    /// Convert `self` to a `u8`. Returns `Err` if `self` is negative or out of
    /// range for `u8`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Integer};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert_eq!(eval::<Integer>("255").unwrap().to_u8().unwrap(), 255);
    /// assert!(eval::<Integer>("256").unwrap().to_u8().is_err());
    /// assert!(eval::<Integer>("-1").unwrap().to_u8().is_err());
    /// ```
    #[inline]
    pub fn to_u8(self) -> Result<u8, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => fix.to_u8(),
            IntegerType::Bignum(_) => Err(Error::new(
                exception::range_error(),
                "bignum too big to convert into `u8`",
            )),
        }
    }

    /// Convert `self` to a `u16`. Returns `Err` if `self` is negative or out
    /// of range for `u16`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Integer};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert_eq!(eval::<Integer>("65535").unwrap().to_u16().unwrap(), 65535);
    /// assert!(eval::<Integer>("65536").unwrap().to_u16().is_err());
    /// assert!(eval::<Integer>("-1").unwrap().to_u16().is_err());
    /// ```
    #[inline]
    pub fn to_u16(self) -> Result<u16, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => fix.to_u16(),
            IntegerType::Bignum(_) => Err(Error::new(
                exception::range_error(),
                "bignum too big to convert into `u16`",
            )),
        }
    }

    /// Convert `self` to a `u32`. Returns `Err` if `self` is negative or out
    /// of range for `u32`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Integer};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert_eq!(eval::<Integer>("4294967295").unwrap().to_u32().unwrap(), 4294967295);
    /// assert!(eval::<Integer>("4294967296").unwrap().to_u32().is_err());
    /// assert!(eval::<Integer>("-1").unwrap().to_u32().is_err());
    /// ```
    #[inline]
    pub fn to_u32(self) -> Result<u32, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => fix.to_u32(),
            IntegerType::Bignum(big) => big.to_u32(),
        }
    }

    /// Convert `self` to a `u64`. Returns `Err` if `self` is negative or out
    /// of range for `u64`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Integer};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert_eq!(eval::<Integer>("4611686018427387903").unwrap().to_u64().unwrap(), 4611686018427387903);
    /// assert!(eval::<Integer>("-1").unwrap().to_u64().is_err());
    /// assert!(eval::<Integer>("18446744073709551616").unwrap().to_u64().is_err());
    /// ```
    #[inline]
    pub fn to_u64(self) -> Result<u64, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => fix.to_u64(),
            IntegerType::Bignum(big) => big.to_u64(),
        }
    }

    /// Convert `self` to a `usize`. Returns `Err` if `self` is negative or out
    /// of range for `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Integer};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert_eq!(eval::<Integer>("4611686018427387903").unwrap().to_usize().unwrap(), 4611686018427387903);
    /// assert!(eval::<Integer>("-1").unwrap().to_usize().is_err());
    /// ```
    #[inline]
    pub fn to_usize(self) -> Result<usize, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => fix.to_usize(),
            IntegerType::Bignum(big) => big.to_usize(),
        }
    }
}

impl fmt::Display for Integer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for Integer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl IntoValue for Integer {
    fn into_value_with(self, _: &Ruby) -> Value {
        self.0.get()
    }
}

impl Numeric for Integer {}

unsafe impl private::ReprValue for Integer {}

impl ReprValue for Integer {}

impl TryConvert for Integer {
    fn try_convert(val: Value) -> Result<Self, Error> {
        match Self::from_value(val) {
            Some(i) => Ok(i),
            None => protect(|| {
                debug_assert_value!(val);
                unsafe { Self::from_rb_value_unchecked(rb_to_int(val.as_rb_value())) }
            }),
        }
    }
}
