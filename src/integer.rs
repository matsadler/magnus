use std::ops::Deref;

use crate::{
    error::Error,
    protect,
    r_basic::RBasic,
    r_bignum::RBignum,
    ruby_sys::{
        rb_ll2inum, rb_num2ll, rb_num2ull, rb_ull2inum, ruby_special_consts, ruby_value_type, VALUE,
    },
    value::{Fixnum, Qnil, Value},
};

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
        let mut res = 0;
        protect(|| {
            res = rb_num2ll(self.into_inner());
            *Qnil::new()
        })?;
        Ok(res)
    }

    unsafe fn is_negative(&self) -> bool {
        if let Some(f) = Fixnum::from_value(self) {
            return f.is_negative();
        }
        if let Some(b) = RBignum::from_value(self) {
            return b.is_negative();
        }
        unreachable!()
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

impl Deref for Integer {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        let self_ptr = self as *const Self;
        let value_ptr = self_ptr as *const Self::Target;
        // we just got this pointer from &self, so we know it's valid to deref
        unsafe { &*value_ptr }
    }
}
