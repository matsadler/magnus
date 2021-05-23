use std::ops::Deref;

use crate::{
    error::Error,
    r_basic::RBasic,
    r_bignum::RBignum,
    ruby_sys::{
        rb_ll2inum, rb_ull2inum, ruby_special_consts, ruby_value_type, VALUE,
    },
    value::{Fixnum, Value},
};

enum IntegerType {
    Fixnum(Fixnum),
    Bignum(RBignum),
}

#[repr(transparent)]
pub struct Integer(VALUE);

impl Integer {
    /// # Safety
    ///
    /// val must not have been GC'd, return value must be kept on stack or
    /// otherwise protected from the GC.
    pub unsafe fn from_value(val: &Value) -> Option<Self> {
        if val.into_inner() & ruby_special_consts::RUBY_FIXNUM_FLAG as VALUE != 0 {
            return Some(Self(val.into_inner()));
        }
        let r_basic = RBasic::from_value(val)?;
        (r_basic.builtin_type() == ruby_value_type::RUBY_T_BIGNUM).then(|| Self(val.into_inner()))
    }

    fn integer_type(&self) -> IntegerType {
        if self.into_inner() & ruby_special_consts::RUBY_FIXNUM_FLAG as VALUE != 0 {
            IntegerType::Fixnum(Fixnum(self.into_inner()))
        } else {
            IntegerType::Bignum(RBignum(self.into_inner()))
        }
    }

    pub fn from_i64(n: i64) -> Self {
        Self(unsafe { rb_ll2inum(n) })
    }

    pub fn from_u64(n: u64) -> Self {
        Self(unsafe { rb_ull2inum(n) })
    }

    /// # Safety
    ///
    /// val must not have been GC'd.
    pub unsafe fn to_i64(&self) -> Result<i64, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => Ok(fix.to_i64()),
            IntegerType::Bignum(big) => big.to_i64(),
        }
    }

    /// # Safety
    ///
    /// val must not have been GC'd.
    pub unsafe fn to_u64(&self) -> Result<u64, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => fix.to_u64(),
            IntegerType::Bignum(big) => big.to_u64(),
        }
    }

    /// # Safety
    ///
    /// val must not have been GC'd.
    pub unsafe fn to_isize(&self) -> Result<isize, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => fix.to_isize(),
            IntegerType::Bignum(big) => big.to_isize(),
        }
    }

    /// # Safety
    ///
    /// val must not have been GC'd.
    pub unsafe fn to_usize(&self) -> Result<usize, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => fix.to_usize(),
            IntegerType::Bignum(big) => big.to_usize(),
        }
    }

    /// # Safety
    ///
    /// val must not have been GC'd.
    pub unsafe fn to_i32(&self) -> Result<i32, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => fix.to_i32(),
            IntegerType::Bignum(big) => big.to_i32(),
        }
    }

    /// # Safety
    ///
    /// val must not have been GC'd.
    pub unsafe fn to_u32(&self) -> Result<u32, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => fix.to_u32(),
            IntegerType::Bignum(big) => big.to_u32(),
        }
    }

    pub fn to_i16(&self) -> Result<i16, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => fix.to_i16(),
            IntegerType::Bignum(_) => Err(Error::range_error("bignum too big to convert into `i16`")),
        }
    }

    pub fn to_u16(&self) -> Result<u16, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => fix.to_u16(),
            IntegerType::Bignum(_) => Err(Error::range_error("bignum too big to convert into `u16`")),
        }
    }

    pub fn to_i8(&self) -> Result<i8, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => fix.to_i8(),
            IntegerType::Bignum(_) => Err(Error::range_error("bignum too big to convert into `i8`")),
        }
    }

    pub fn to_u8(&self) -> Result<u8, Error> {
        match self.integer_type() {
            IntegerType::Fixnum(fix) => fix.to_u8(),
            IntegerType::Bignum(_) => Err(Error::range_error("bignum too big to convert into `u8`")),
        }
    }
}

impl Deref for Integer {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        let self_ptr = self as *const Self;
        let value_ptr = self_ptr as *const Self::Target;
        // we just got this pointer from &self, so we know it's valid to deref
        unsafe { &*value_ptr }
    }
}
