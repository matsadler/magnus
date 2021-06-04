use std::{fmt, ops::Deref};

use crate::{
    debug_assert_value,
    error::{protect, Error},
    r_bignum::RBignum,
    ruby_sys::{rb_ll2inum, rb_to_int, rb_ull2inum, ruby_special_consts, ruby_value_type, VALUE},
    try_convert::TryConvert,
    value::{Fixnum, NonZeroValue, Value},
};

enum IntegerType {
    Fixnum(Fixnum),
    Bignum(RBignum),
}

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Integer(NonZeroValue);

impl Integer {
    /// # Safety
    ///
    /// val must not have been GC'd, return value must be kept on stack or
    /// otherwise protected from the GC.
    #[inline]
    pub unsafe fn from_value(val: Value) -> Option<Self> {
        if val.as_rb_value() & ruby_special_consts::RUBY_FIXNUM_FLAG as VALUE != 0 {
            return Some(Self(NonZeroValue::new_unchecked(val)));
        }
        debug_assert_value!(val);
        (val.rb_type() == ruby_value_type::RUBY_T_BIGNUM)
            .then(|| Self(NonZeroValue::new_unchecked(val)))
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        Self(NonZeroValue::new_unchecked(Value::new(val)))
    }

    fn integer_type(self) -> IntegerType {
        unsafe {
            if self.as_rb_value() & ruby_special_consts::RUBY_FIXNUM_FLAG as VALUE != 0 {
                IntegerType::Fixnum(Fixnum::from_rb_value_unchecked(self.as_rb_value()))
            } else {
                IntegerType::Bignum(RBignum::from_rb_value_unchecked(self.as_rb_value()))
            }
        }
    }

    pub fn from_i64(n: i64) -> Self {
        unsafe { Self::from_rb_value_unchecked(rb_ll2inum(n)) }
    }

    pub fn from_u64(n: u64) -> Self {
        unsafe { Self::from_rb_value_unchecked(rb_ull2inum(n)) }
    }

    pub fn to_i8(self) -> Result<i8, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => fix.to_i8(),
            IntegerType::Bignum(_) => {
                Err(Error::range_error("bignum too big to convert into `i8`"))
            }
        }
    }

    pub fn to_i16(self) -> Result<i16, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => fix.to_i16(),
            IntegerType::Bignum(_) => {
                Err(Error::range_error("bignum too big to convert into `i16`"))
            }
        }
    }

    /// # Safety
    ///
    /// val must not have been GC'd.
    pub unsafe fn to_i32(self) -> Result<i32, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => fix.to_i32(),
            IntegerType::Bignum(big) => big.to_i32(),
        }
    }

    /// # Safety
    ///
    /// val must not have been GC'd.
    pub unsafe fn to_i64(self) -> Result<i64, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => Ok(fix.to_i64()),
            IntegerType::Bignum(big) => big.to_i64(),
        }
    }

    /// # Safety
    ///
    /// val must not have been GC'd.
    pub unsafe fn to_isize(self) -> Result<isize, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => fix.to_isize(),
            IntegerType::Bignum(big) => big.to_isize(),
        }
    }

    pub fn to_u8(self) -> Result<u8, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => fix.to_u8(),
            IntegerType::Bignum(_) => {
                Err(Error::range_error("bignum too big to convert into `u8`"))
            }
        }
    }

    pub fn to_u16(self) -> Result<u16, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => fix.to_u16(),
            IntegerType::Bignum(_) => {
                Err(Error::range_error("bignum too big to convert into `u16`"))
            }
        }
    }

    /// # Safety
    ///
    /// val must not have been GC'd.
    pub unsafe fn to_u32(self) -> Result<u32, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => fix.to_u32(),
            IntegerType::Bignum(big) => big.to_u32(),
        }
    }

    /// # Safety
    ///
    /// val must not have been GC'd.
    pub unsafe fn to_u64(self) -> Result<u64, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => fix.to_u64(),
            IntegerType::Bignum(big) => big.to_u64(),
        }
    }

    /// # Safety
    ///
    /// val must not have been GC'd.
    pub unsafe fn to_usize(self) -> Result<usize, Error> {
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
        write!(f, "{}", unsafe { self.inspect() })
    }
}

impl From<Integer> for Value {
    fn from(val: Integer) -> Self {
        *val
    }
}

impl TryConvert for Integer {
    #[inline]
    unsafe fn try_convert(val: &Value) -> Result<Self, Error> {
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
