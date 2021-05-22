use std::ops::Deref;

use crate::{
    error::Error,
    protect,
    r_basic::RBasic,
    ruby_sys::{rb_ll2inum, ruby_fl_type, rb_num2ll, rb_num2ull, rb_ull2inum, ruby_value_type, VALUE},
    value::{Fixnum, Qnil, Value},
};

#[repr(transparent)]
pub struct RBignum(VALUE);

impl RBignum {
    /// # Safety
    ///
    /// val must not have been GC'd, return value must be kept on stack or
    /// otherwise protected from the GC.
    pub unsafe fn from_value(val: &Value) -> Option<Self> {
        let r_basic = RBasic::from_value(val)?;
        (r_basic.builtin_type() == ruby_value_type::RUBY_T_BIGNUM).then(|| Self(val.into_inner()))
    }

    pub fn from_i64(n: i64) -> Result<Self, Fixnum> {
        unsafe {
            let val = Value::new(rb_ll2inum(n));
            RBignum::from_value(&val).ok_or_else(|| {
                Fixnum::from_value(&val).expect("i64 should convert to fixnum or bignum")
            })
        }
    }

    pub fn from_u64(n: u64) -> Result<Self, Fixnum> {
        unsafe {
            let val = Value::new(rb_ull2inum(n));
            RBignum::from_value(&val).ok_or_else(|| {
                Fixnum::from_value(&val).expect("u64 should convert to fixnum or bignum")
            })
        }
    }

    /// # Safety
    ///
    /// val must not have been GC'd.
    pub unsafe fn to_i64(&self) -> Result<i64, Error> {
        let mut res = 0;
        protect(|| {
            res = rb_num2ll(self.into_inner());
            *Qnil::new()
        })?;
        Ok(res)
    }

    pub(crate) unsafe fn is_negative(&self) -> bool {
        let r_basic = RBasic::from_value(self).expect("bignum missing RBasic");
        r_basic.as_internal().as_ref().flags & (ruby_fl_type::RUBY_FL_USER1 as VALUE) == 0
    }

    /// # Safety
    ///
    /// val must not have been GC'd.
    pub unsafe fn to_u64(&self) -> Result<u64, Error> {
        if self.is_negative() {
            return Err(Error::range_error(
                "can't convert negative integer to unsigned",
            ));
        }
        let mut res = 0;
        protect(|| {
            res = rb_num2ull(self.into_inner());
            *Qnil::new()
        })?;
        Ok(res)
    }
}

impl Deref for RBignum {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        let self_ptr = self as *const Self;
        let value_ptr = self_ptr as *const Self::Target;
        // we just got this pointer from &self, so we know it's valid to deref
        unsafe { &*value_ptr }
    }
}
