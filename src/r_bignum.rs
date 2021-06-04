use std::{
    fmt,
    ops::Deref,
    os::raw::{c_long, c_ulong},
};

use crate::{
    debug_assert_value,
    error::{protect, Error},
    ruby_sys::{
        rb_ll2inum, rb_num2ll, rb_num2long, rb_num2ull, rb_num2ulong, rb_ull2inum, ruby_fl_type,
        ruby_value_type, VALUE,
    },
    value::{Fixnum, NonZeroValue, Qnil, Value},
};

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RBignum(NonZeroValue);

impl RBignum {
    /// # Safety
    ///
    /// val must not have been GC'd, return value must be kept on stack or
    /// otherwise protected from the GC.
    #[inline]
    pub unsafe fn from_value(val: Value) -> Option<Self> {
        (val.rb_type() == ruby_value_type::RUBY_T_BIGNUM)
            .then(|| Self(NonZeroValue::new_unchecked(val)))
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        Self(NonZeroValue::new_unchecked(Value::new(val)))
    }

    pub fn from_i64(n: i64) -> Result<Self, Fixnum> {
        unsafe {
            let val = Value::new(rb_ll2inum(n));
            RBignum::from_value(val).ok_or_else(|| {
                Fixnum::from_value(val).expect("i64 should convert to fixnum or bignum")
            })
        }
    }

    pub fn from_u64(n: u64) -> Result<Self, Fixnum> {
        unsafe {
            let val = Value::new(rb_ull2inum(n));
            RBignum::from_value(val).ok_or_else(|| {
                Fixnum::from_value(val).expect("u64 should convert to fixnum or bignum")
            })
        }
    }

    unsafe fn is_negative(self) -> bool {
        debug_assert_value!(self);
        let r_basic = self.r_basic_unchecked();
        r_basic.as_ref().flags & (ruby_fl_type::RUBY_FL_USER1 as VALUE) == 0
    }

    /// Will only succeed on a 32 bit system. On a 64 bit system bignum will
    /// always be out of range.
    ///
    /// # Safety
    ///
    /// self must not have been GC'd.
    pub unsafe fn to_i32(self) -> Result<i32, Error> {
        debug_assert_value!(self);
        let mut res = 0;
        protect(|| {
            res = rb_num2long(self.as_rb_value());
            *Qnil::new()
        })?;
        if res > i32::MAX as c_long {
            return Err(Error::range_error("bignum too big to convert into `i32`"));
        }
        Ok(res as i32)
    }

    /// # Safety
    ///
    /// self must not have been GC'd.
    pub unsafe fn to_i64(self) -> Result<i64, Error> {
        debug_assert_value!(self);
        let mut res = 0;
        protect(|| {
            res = rb_num2ll(self.as_rb_value());
            *Qnil::new()
        })?;
        Ok(res)
    }

    /// # Safety
    ///
    /// self must not have been GC'd.
    pub unsafe fn to_isize(self) -> Result<isize, Error> {
        debug_assert_value!(self);
        let mut res = 0;
        protect(|| {
            res = rb_num2long(self.as_rb_value());
            *Qnil::new()
        })?;
        if res > isize::MAX as c_long {
            return Err(Error::range_error("bignum too big to convert into `isize`"));
        }
        Ok(res as isize)
    }

    /// Will only succeed on a 32 bit system. On a 64 bit system bignum will
    /// always be out of range.
    ///
    /// # Safety
    ///
    /// self must not have been GC'd.
    pub unsafe fn to_u32(self) -> Result<u32, Error> {
        debug_assert_value!(self);
        if self.is_negative() {
            return Err(Error::range_error(
                "can't convert negative integer to unsigned",
            ));
        }
        let mut res = 0;
        protect(|| {
            res = rb_num2ulong(self.as_rb_value());
            *Qnil::new()
        })?;
        if res > u32::MAX as c_ulong {
            return Err(Error::range_error("bignum too big to convert into `u32`"));
        }
        Ok(res as u32)
    }

    /// # Safety
    ///
    /// self must not have been GC'd.
    pub unsafe fn to_u64(self) -> Result<u64, Error> {
        debug_assert_value!(self);
        if self.is_negative() {
            return Err(Error::range_error(
                "can't convert negative integer to unsigned",
            ));
        }
        let mut res = 0;
        protect(|| {
            res = rb_num2ull(self.as_rb_value());
            *Qnil::new()
        })?;
        Ok(res)
    }

    /// # Safety
    ///
    /// self must not have been GC'd.
    pub unsafe fn to_usize(self) -> Result<usize, Error> {
        debug_assert_value!(self);
        if self.is_negative() {
            return Err(Error::range_error(
                "can't convert negative integer to unsigned",
            ));
        }
        let mut res = 0;
        protect(|| {
            res = rb_num2ulong(self.as_rb_value());
            *Qnil::new()
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
        write!(f, "{}", unsafe { self.inspect() })
    }
}

impl From<RBignum> for Value {
    fn from(val: RBignum) -> Self {
        *val
    }
}
