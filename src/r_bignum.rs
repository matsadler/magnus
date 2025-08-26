use std::{
    fmt,
    os::raw::{c_long, c_longlong, c_ulong, c_ulonglong},
};

use rb_sys::{
    VALUE, rb_big2str, rb_ll2inum, rb_num2ll, rb_num2long, rb_num2ull, rb_num2ulong, rb_ull2inum,
    ruby_fl_type, ruby_value_type,
};

use crate::{
    RString, Ruby,
    error::{Error, protect},
    integer::{Integer, IntegerType},
    into_value::IntoValue,
    numeric::Numeric,
    try_convert::TryConvert,
    value::{
        Fixnum, NonZeroValue, ReprValue, Value,
        private::{self, ReprValue as _},
    },
};

/// # `RBignum`
///
/// Functions that can be used to create instances of Ruby's large interger
/// representation.
///
/// See also the [`RBignum`] type.
impl Ruby {
    /// Create a new `RBignum` from an `i64.`
    ///
    /// Returns `Ok(RBignum)` if `n` is large enough to require a bignum,
    /// otherwise returns `Err(Fixnum)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     assert!(ruby.bignum_from_i64(4611686018427387904).is_ok());
    ///     assert!(ruby.bignum_from_i64(-4611686018427387905).is_ok());
    ///     // too small
    ///     assert!(ruby.bignum_from_i64(0).is_err());
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn bignum_from_i64(&self, n: i64) -> Result<RBignum, Fixnum> {
        unsafe {
            let val = Value::new(rb_ll2inum(n));
            RBignum::from_value(val)
                .ok_or_else(|| Fixnum::from_rb_value_unchecked(val.as_rb_value()))
        }
    }

    /// Create a new `RBignum` from an `u64.`
    ///
    /// Returns `Ok(RBignum)` if `n` is large enough to require a bignum,
    /// otherwise returns `Err(Fixnum)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     assert!(ruby.bignum_from_u64(4611686018427387904).is_ok());
    ///     // too small
    ///     assert!(ruby.bignum_from_u64(0).is_err());
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn bignum_from_u64(&self, n: u64) -> Result<RBignum, Fixnum> {
        unsafe {
            let val = Value::new(rb_ull2inum(n));
            RBignum::from_value(val)
                .ok_or_else(|| Fixnum::from_rb_value_unchecked(val.as_rb_value()))
        }
    }
}

/// A Value pointer to a RBignum struct, Ruby's internal representation of
/// large integers.
///
/// See also [`Integer`].
///
/// See the [`ReprValue`] trait for additional methods available on this type.
/// See [`Ruby`](Ruby#rbignum) for methods to create an `RBignum`.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RBignum(NonZeroValue);

impl RBignum {
    /// Return `Some(RBignum)` if `val` is a `RBignum`, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{RBignum, eval};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(RBignum::from_value(eval("9223372036854775807").unwrap()).is_some());
    /// // too small
    /// assert!(RBignum::from_value(eval("0").unwrap()).is_none());
    /// // not an int
    /// assert!(RBignum::from_value(eval("1.23").unwrap()).is_none());
    /// ```
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            (val.rb_type() == ruby_value_type::RUBY_T_BIGNUM)
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        unsafe { Self(NonZeroValue::new_unchecked(Value::new(val))) }
    }

    /// Create a new `RBignum` from an `i64.`
    ///
    /// Returns `Ok(RBignum)` if `n` is large enough to require a bignum,
    /// otherwise returns `Err(Fixnum)`.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread. See [`Ruby::bignum_from_i64`]
    /// for the non-panicking version.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(deprecated)]
    /// use magnus::RBignum;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(RBignum::from_i64(4611686018427387904).is_ok());
    /// assert!(RBignum::from_i64(-4611686018427387905).is_ok());
    /// // too small
    /// assert!(RBignum::from_i64(0).is_err());
    /// ```
    #[cfg_attr(
        not(feature = "old-api"),
        deprecated(note = "please use `Ruby::bignum_from_i64` instead")
    )]
    #[cfg_attr(docsrs, doc(cfg(feature = "old-api")))]
    #[inline]
    pub fn from_i64(n: i64) -> Result<Self, Fixnum> {
        get_ruby!().bignum_from_i64(n)
    }

    /// Create a new `RBignum` from an `u64.`
    ///
    /// Returns `Ok(RBignum)` if `n` is large enough to require a bignum,
    /// otherwise returns `Err(Fixnum)`.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread. See [`Ruby::bignum_from_u64`]
    /// for the non-panicking version.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(deprecated)]
    /// use magnus::RBignum;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(RBignum::from_u64(4611686018427387904).is_ok());
    /// // too small
    /// assert!(RBignum::from_u64(0).is_err());
    /// ```
    #[cfg_attr(
        not(feature = "old-api"),
        deprecated(note = "please use `Ruby::bignum_from_u64` instead")
    )]
    #[cfg_attr(docsrs, doc(cfg(feature = "old-api")))]
    #[inline]
    pub fn from_u64(n: u64) -> Result<Self, Fixnum> {
        get_ruby!().bignum_from_u64(n)
    }

    /// Create a new `RBignum` from a `i32.`
    ///
    /// This will only succeed on a 32 bit system. On a 64 bit system bignum
    /// will always be out of range.
    #[doc(hidden)]
    pub fn to_i32(self) -> Result<i32, Error> {
        debug_assert_value!(self);
        let handle = Ruby::get_with(self);
        let mut res = 0;
        protect(|| {
            unsafe { res = rb_num2long(self.as_rb_value()) };
            handle.qnil()
        })?;
        if res > i32::MAX as c_long {
            return Err(Error::new(
                handle.exception_range_error(),
                "bignum too big to convert into `i32`",
            ));
        }
        Ok(res as i32)
    }

    /// Convert `self` to an `i64`. Returns `Err` if `self` is out of range for
    /// `i64`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{RBignum, eval};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert_eq!(
    ///     eval::<RBignum>("4611686018427387904")
    ///         .unwrap()
    ///         .to_i64()
    ///         .unwrap(),
    ///     4611686018427387904
    /// );
    /// assert_eq!(
    ///     eval::<RBignum>("-4611686018427387905")
    ///         .unwrap()
    ///         .to_i64()
    ///         .unwrap(),
    ///     -4611686018427387905
    /// );
    /// assert!(
    ///     eval::<RBignum>("9223372036854775808")
    ///         .unwrap()
    ///         .to_i64()
    ///         .is_err()
    /// );
    /// assert!(
    ///     eval::<RBignum>("-9223372036854775809")
    ///         .unwrap()
    ///         .to_i64()
    ///         .is_err()
    /// );
    /// ```
    pub fn to_i64(self) -> Result<i64, Error> {
        debug_assert_value!(self);
        let mut res = 0;
        protect(|| {
            unsafe { res = rb_num2ll(self.as_rb_value()) };
            Ruby::get_with(self).qnil()
        })?;
        Ok(res)
    }

    /// Convert `self` to an `i128`. Returns `Err` if `self` is out of range for
    /// `i128`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{RBignum, eval};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert_eq!(
    ///     eval::<RBignum>("170141183460469231731687303715884105727")
    ///         .unwrap()
    ///         .to_i128()
    ///         .unwrap(),
    ///     170141183460469231731687303715884105727
    /// );
    /// assert_eq!(
    ///     eval::<RBignum>("-170141183460469231731687303715884105728")
    ///         .unwrap()
    ///         .to_i128()
    ///         .unwrap(),
    ///     -170141183460469231731687303715884105728
    /// );
    /// assert!(
    ///     eval::<RBignum>("170141183460469231731687303715884105728")
    ///         .unwrap()
    ///         .to_i128()
    ///         .is_err()
    /// );
    /// assert!(
    ///     eval::<RBignum>("-170141183460469231731687303715884105729")
    ///         .unwrap()
    ///         .to_i128()
    ///         .is_err()
    /// );
    /// ```
    pub fn to_i128(self) -> Result<i128, Error> {
        debug_assert_value!(self);
        let handle = Ruby::get_with(self);
        let mut res = 0;
        protect(|| {
            unsafe { res = rb_big2str(self.as_rb_value(), 10) };
            handle.qnil()
        })?;
        unsafe {
            RString::from_rb_value_unchecked(res)
                .as_str()
                .unwrap()
                .parse::<i128>()
        }
        .map_err(|_| {
            Error::new(
                handle.exception_range_error(),
                "bignum too big to convert into `i128`",
            )
        })
    }

    /// Convert `self` to an `isize`. Returns `Err` if `self` is out of range
    /// for `isize`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{RBignum, eval};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert_eq!(
    ///     eval::<RBignum>("4611686018427387904")
    ///         .unwrap()
    ///         .to_isize()
    ///         .unwrap(),
    ///     4611686018427387904
    /// );
    /// assert_eq!(
    ///     eval::<RBignum>("-4611686018427387905")
    ///         .unwrap()
    ///         .to_isize()
    ///         .unwrap(),
    ///     -4611686018427387905
    /// );
    /// ```
    pub fn to_isize(self) -> Result<isize, Error> {
        debug_assert_value!(self);
        let handle = Ruby::get_with(self);
        let mut res = 0;
        protect(|| {
            unsafe { res = rb_num2ll(self.as_rb_value()) };
            handle.qnil()
        })?;
        if res > isize::MAX as c_longlong {
            return Err(Error::new(
                handle.exception_range_error(),
                "bignum too big to convert into `isize`",
            ));
        }
        Ok(res as isize)
    }

    /// Create a new `RBignum` from a `u32.`
    ///
    /// This will only succeed on a 32 bit system. On a 64 bit system bignum
    /// will always be out of range.
    #[doc(hidden)]
    pub fn to_u32(self) -> Result<u32, Error> {
        debug_assert_value!(self);
        let handle = Ruby::get_with(self);
        if self.is_negative() {
            return Err(Error::new(
                handle.exception_range_error(),
                "can't convert negative integer to unsigned",
            ));
        }
        let mut res = 0;
        protect(|| {
            unsafe { res = rb_num2ulong(self.as_rb_value()) };
            handle.qnil()
        })?;
        if res > u32::MAX as c_ulong {
            return Err(Error::new(
                handle.exception_range_error(),
                "bignum too big to convert into `u32`",
            ));
        }
        Ok(res as u32)
    }

    /// Convert `self` to a `u64`. Returns `Err` if `self` is negative or out
    /// of range for `u64`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{RBignum, eval};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert_eq!(
    ///     eval::<RBignum>("4611686018427387904")
    ///         .unwrap()
    ///         .to_u64()
    ///         .unwrap(),
    ///     4611686018427387904
    /// );
    /// assert!(
    ///     eval::<RBignum>("18446744073709551616")
    ///         .unwrap()
    ///         .to_u64()
    ///         .is_err()
    /// );
    /// ```
    pub fn to_u64(self) -> Result<u64, Error> {
        debug_assert_value!(self);
        let handle = Ruby::get_with(self);
        if self.is_negative() {
            return Err(Error::new(
                handle.exception_range_error(),
                "can't convert negative integer to unsigned",
            ));
        }
        let mut res = 0;
        protect(|| {
            unsafe { res = rb_num2ull(self.as_rb_value()) };
            handle.qnil()
        })?;
        Ok(res)
    }

    /// Convert `self` to a `u128`. Returns `Err` if `self` is negative or out
    /// of range for `u128`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{RBignum, eval};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert_eq!(
    ///     eval::<RBignum>("340282366920938463463374607431768211455")
    ///         .unwrap()
    ///         .to_u128()
    ///         .unwrap(),
    ///     340282366920938463463374607431768211455
    /// );
    /// assert!(
    ///     eval::<RBignum>("340282366920938463463374607431768211456")
    ///         .unwrap()
    ///         .to_u128()
    ///         .is_err()
    /// );
    /// ```
    pub fn to_u128(self) -> Result<u128, Error> {
        debug_assert_value!(self);
        let handle = Ruby::get_with(self);
        if self.is_negative() {
            return Err(Error::new(
                handle.exception_range_error(),
                "can't convert negative integer to unsigned",
            ));
        }
        let mut res = 0;
        protect(|| {
            unsafe { res = rb_big2str(self.as_rb_value(), 10) };
            handle.qnil()
        })?;
        unsafe {
            RString::from_rb_value_unchecked(res)
                .as_str()
                .unwrap()
                .parse::<u128>()
        }
        .map_err(|_| {
            Error::new(
                handle.exception_range_error(),
                "bignum too big to convert into `u128`",
            )
        })
    }

    /// Convert `self` to a `usize`. Returns `Err` if `self` is negative or out
    /// of range for `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{RBignum, eval};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert_eq!(
    ///     eval::<RBignum>("4611686018427387904")
    ///         .unwrap()
    ///         .to_usize()
    ///         .unwrap(),
    ///     4611686018427387904
    /// );
    /// assert!(
    ///     eval::<RBignum>("18446744073709551616")
    ///         .unwrap()
    ///         .to_usize()
    ///         .is_err()
    /// );
    /// ```
    pub fn to_usize(self) -> Result<usize, Error> {
        debug_assert_value!(self);
        let handle = Ruby::get_with(self);
        if self.is_negative() {
            return Err(Error::new(
                handle.exception_range_error(),
                "can't convert negative integer to unsigned",
            ));
        }
        let mut res = 0;
        protect(|| {
            unsafe { res = rb_num2ull(self.as_rb_value()) };
            handle.qnil()
        })?;
        if res > usize::MAX as c_ulonglong {
            return Err(Error::new(
                handle.exception_range_error(),
                "bignum too big to convert into `usize`",
            ));
        }
        Ok(res as usize)
    }

    /// Check if `self` is positive.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let num = ruby.bignum_from_u64(4611686018427387904).unwrap();
    ///     assert!(num.is_positive());
    ///
    ///     let num = ruby.bignum_from_i64(-4611686018427387905).unwrap();
    ///     assert!(!num.is_positive());
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn is_positive(self) -> bool {
        debug_assert_value!(self);
        unsafe {
            let r_basic = self.r_basic_unchecked();
            r_basic.as_ref().flags & (ruby_fl_type::RUBY_FL_USER1 as VALUE) != 0
        }
    }

    /// Check if `self` is negative.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let num = ruby.bignum_from_i64(-4611686018427387905).unwrap();
    ///     assert!(num.is_negative());
    ///
    ///     let num = ruby.bignum_from_u64(4611686018427387904).unwrap();
    ///     assert!(!num.is_negative());
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn is_negative(self) -> bool {
        !self.is_positive()
    }
}

impl fmt::Display for RBignum {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for RBignum {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl IntoValue for RBignum {
    #[inline]
    fn into_value_with(self, _: &Ruby) -> Value {
        self.0.get()
    }
}

unsafe impl private::ReprValue for RBignum {}

impl Numeric for RBignum {}

impl ReprValue for RBignum {}

impl TryConvert for RBignum {
    fn try_convert(val: Value) -> Result<Self, Error> {
        match Integer::try_convert(val)?.integer_type() {
            IntegerType::Fixnum(_) => Err(Error::new(
                Ruby::get_with(val).exception_range_error(),
                "integer to small for bignum",
            )),
            IntegerType::Bignum(big) => Ok(big),
        }
    }
}
