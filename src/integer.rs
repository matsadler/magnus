use std::{fmt, ops::Deref};

use crate::{
    debug_assert_value,
    error::{protect, Error},
    r_bignum::RBignum,
    ruby_sys::{rb_ll2inum, rb_to_int, rb_ull2inum, ruby_special_consts, ruby_value_type, VALUE},
    try_convert::TryConvert,
    value::{Fixnum, NonZeroValue, Value},
};

pub(crate) enum IntegerType {
    Fixnum(Fixnum),
    Bignum(RBignum),
}

/// A type wrapping either a [`Fixnum`] or a [`RBignum`].
///
/// All [`Value`] methods should be available on this type through [`Deref`],
/// but some may be missed by this documentation.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Integer(NonZeroValue);

impl Integer {
    /// Return `Some(Integer)` if `val` is an `Integer`, `None` otherwise.
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
    pub fn from_i64(n: i64) -> Self {
        unsafe { Self::from_rb_value_unchecked(rb_ll2inum(n)) }
    }

    /// Create a new `Integer` from a `u64.`
    pub fn from_u64(n: u64) -> Self {
        unsafe { Self::from_rb_value_unchecked(rb_ull2inum(n)) }
    }

    /// Convert `self` to an `i8`. Returns `Err` if `self` is out of range for
    /// `i8`.
    pub fn to_i8(self) -> Result<i8, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => fix.to_i8(),
            IntegerType::Bignum(_) => {
                Err(Error::range_error("bignum too big to convert into `i8`"))
            }
        }
    }

    /// Convert `self` to an `i16`. Returns `Err` if `self` is out of range for
    /// `i16`.
    pub fn to_i16(self) -> Result<i16, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => fix.to_i16(),
            IntegerType::Bignum(_) => {
                Err(Error::range_error("bignum too big to convert into `i16`"))
            }
        }
    }

    /// Convert `self` to an `i32`. Returns `Err` if `self` is out of range for
    /// `i32`.
    pub fn to_i32(self) -> Result<i32, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => fix.to_i32(),
            IntegerType::Bignum(big) => big.to_i32(),
        }
    }

    /// Convert `self` to an `i64`. Returns `Err` if `self` is out of range for
    /// `i64`.
    pub fn to_i64(self) -> Result<i64, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => Ok(fix.to_i64()),
            IntegerType::Bignum(big) => big.to_i64(),
        }
    }

    /// Convert `self` to an `isize`. Returns `Err` if `self` is out of range
    /// for `isize`.
    pub fn to_isize(self) -> Result<isize, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => fix.to_isize(),
            IntegerType::Bignum(big) => big.to_isize(),
        }
    }

    /// Convert `self` to a `u8`. Returns `Err` if `self` is negative or out of
    /// range for `u8`.
    pub fn to_u8(self) -> Result<u8, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => fix.to_u8(),
            IntegerType::Bignum(_) => {
                Err(Error::range_error("bignum too big to convert into `u8`"))
            }
        }
    }

    /// Convert `self` to a `u16`. Returns `Err` if `self` is negative or out
    /// of range for `u16`.
    pub fn to_u16(self) -> Result<u16, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => fix.to_u16(),
            IntegerType::Bignum(_) => {
                Err(Error::range_error("bignum too big to convert into `u16`"))
            }
        }
    }

    /// Convert `self` to a `u32`. Returns `Err` if `self` is negative or out
    /// of range for `u32`.
    pub fn to_u32(self) -> Result<u32, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => fix.to_u32(),
            IntegerType::Bignum(big) => big.to_u32(),
        }
    }

    /// Convert `self` to a `u64`. Returns `Err` if `self` is negative or out
    /// of range for `u64`.
    pub fn to_u64(self) -> Result<u64, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => fix.to_u64(),
            IntegerType::Bignum(big) => big.to_u64(),
        }
    }

    /// Convert `self` to a `usize`. Returns `Err` if `self` is negative or out
    /// of range for `usize`.
    pub fn to_usize(self) -> Result<usize, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => fix.to_usize(),
            IntegerType::Bignum(big) => big.to_usize(),
        }
    }
}

impl Deref for Integer {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
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

impl From<Integer> for Value {
    fn from(val: Integer) -> Self {
        *val
    }
}

impl TryConvert for Integer {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        unsafe {
            match Self::from_value(*val) {
                Some(i) => Ok(i),
                None => protect(|| {
                    debug_assert_value!(val);
                    Value::new(rb_to_int(val.as_rb_value()))
                })
                .map(|res| Self::from_rb_value_unchecked(res.as_rb_value())),
            }
        }
    }
}
