use std::{
    fmt,
    ops::Deref,
    os::raw::{c_long, c_ulong},
};

use crate::{
    debug_assert_value,
    error::{protect, Error},
    integer::{Integer, IntegerType},
    ruby_sys::{
        rb_ll2inum, rb_num2ll, rb_num2long, rb_num2ull, rb_num2ulong, rb_ull2inum, ruby_fl_type,
        ruby_value_type, VALUE,
    },
    try_convert::TryConvert,
    value::{Fixnum, NonZeroValue, Value, QNIL},
};

/// A Value pointer to a RBignum struct, Ruby's internal representation of
/// large integers.
///
/// All [`Value`] methods should be available on this type through [`Deref`],
/// but some may be missed by this documentation.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RBignum(NonZeroValue);

impl RBignum {
    /// Return `Some(RBignum)` if `val` is a `RBignum`, `None` otherwise.
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            (val.rb_type() == ruby_value_type::RUBY_T_BIGNUM)
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        Self(NonZeroValue::new_unchecked(Value::new(val)))
    }

    /// Create a new `RBignum` from an `i64.`
    ///
    /// Returns `Ok(RBignum)` if `n` is large enough to require a bignum,
    /// otherwise returns `Err(Fixnum)`.
    pub fn from_i64(n: i64) -> Result<Self, Fixnum> {
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
    pub fn from_u64(n: u64) -> Result<Self, Fixnum> {
        unsafe {
            let val = Value::new(rb_ull2inum(n));
            RBignum::from_value(val)
                .ok_or_else(|| Fixnum::from_rb_value_unchecked(val.as_rb_value()))
        }
    }

    fn is_negative(self) -> bool {
        debug_assert_value!(self);
        unsafe {
            let r_basic = self.r_basic_unchecked();
            r_basic.as_ref().flags & (ruby_fl_type::RUBY_FL_USER1 as VALUE) == 0
        }
    }

    /// Create a new `RBignum` from a `i32.`
    ///
    /// This will only succeed on a 32 bit system. On a 64 bit system bignum
    /// will always be out of range.
    #[doc(hidden)]
    pub fn to_i32(self) -> Result<i32, Error> {
        debug_assert_value!(self);
        let mut res = 0;
        protect(|| {
            res = unsafe { rb_num2long(self.as_rb_value()) };
            *QNIL
        })?;
        if res > i32::MAX as c_long {
            return Err(Error::range_error("bignum too big to convert into `i32`"));
        }
        Ok(res as i32)
    }

    /// Convert `self` to an `i64`. Returns `Err` if `self` is out of range for
    /// `i64`.
    pub fn to_i64(self) -> Result<i64, Error> {
        debug_assert_value!(self);
        let mut res = 0;
        protect(|| {
            res = unsafe { rb_num2ll(self.as_rb_value()) };
            *QNIL
        })?;
        Ok(res)
    }

    /// Convert `self` to an `isize`. Returns `Err` if `self` is out of range
    /// for `isize`.
    pub fn to_isize(self) -> Result<isize, Error> {
        debug_assert_value!(self);
        let mut res = 0;
        protect(|| {
            res = unsafe { rb_num2long(self.as_rb_value()) };
            *QNIL
        })?;
        if res > isize::MAX as c_long {
            return Err(Error::range_error("bignum too big to convert into `isize`"));
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
        if self.is_negative() {
            return Err(Error::range_error(
                "can't convert negative integer to unsigned",
            ));
        }
        let mut res = 0;
        protect(|| {
            res = unsafe { rb_num2ulong(self.as_rb_value()) };
            *QNIL
        })?;
        if res > u32::MAX as c_ulong {
            return Err(Error::range_error("bignum too big to convert into `u32`"));
        }
        Ok(res as u32)
    }

    /// Convert `self` to a `u64`. Returns `Err` if `self` is negative or out
    /// of range for `u64`.
    pub fn to_u64(self) -> Result<u64, Error> {
        debug_assert_value!(self);
        if self.is_negative() {
            return Err(Error::range_error(
                "can't convert negative integer to unsigned",
            ));
        }
        let mut res = 0;
        protect(|| {
            res = unsafe { rb_num2ull(self.as_rb_value()) };
            *QNIL
        })?;
        Ok(res)
    }

    /// Convert `self` to a `usize`. Returns `Err` if `self` is negative or out
    /// of range for `usize`.
    pub fn to_usize(self) -> Result<usize, Error> {
        debug_assert_value!(self);
        if self.is_negative() {
            return Err(Error::range_error(
                "can't convert negative integer to unsigned",
            ));
        }
        let mut res = 0;
        protect(|| {
            res = unsafe { rb_num2ulong(self.as_rb_value()) };
            *QNIL
        })?;
        if res > usize::MAX as c_ulong {
            return Err(Error::range_error("bignum too big to convert into `usize`"));
        }
        Ok(res as usize)
    }
}

impl Deref for RBignum {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
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

impl From<RBignum> for Value {
    fn from(val: RBignum) -> Self {
        *val
    }
}

impl TryConvert for RBignum {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        match val.try_convert::<Integer>()?.integer_type() {
            IntegerType::Fixnum(_) => Err(Error::range_error("integer to small for bignum")),
            IntegerType::Bignum(big) => Ok(big),
        }
    }
}
