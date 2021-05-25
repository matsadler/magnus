use std::{
    mem::transmute,
    ops::{Deref, DerefMut},
    os::raw::{c_long, c_ulong},
};

use crate::{
    error::Error,
    float::Float,
    integer::Integer,
    protect,
    r_bignum::RBignum,
    r_float::RFloat,
    ruby_sys::{
        rb_float_new, rb_float_value, rb_gc_register_address, rb_gc_register_mark_object,
        rb_gc_unregister_address, rb_id2sym, rb_ll2inum, rb_num2ll, rb_num2long, rb_num2short,
        rb_num2ull, rb_num2ulong, rb_num2ushort, rb_sym2id, rb_ull2inum, ruby_special_consts, ID,
        VALUE,
    },
};

// This isn't infallible, if the original object was gc'd and that slot
// reused already this won't panic like it should, but we're trying our
// best here.
#[macro_export]
macro_rules! debug_assert_value {
    ($value:expr) => {
        #[cfg(debug_assertions)]
        if let Some(r_basic) = crate::r_basic::RBasic::from_value(&$value) {
            // The memory this points to is managed by Ruby's GC and we can't
            // really know if it's safe to access as with GC compaction this
            // may point to memory now outside that owned by the process. We
            // will likly segfault in that case, which is kind of OK, as we're
            // trying to panic anyway.
            #[allow(unused_unsafe)]
            match unsafe { r_basic.builtin_type() } {
                crate::ruby_sys::ruby_value_type::RUBY_T_NONE
                | crate::ruby_sys::ruby_value_type::RUBY_T_ZOMBIE
                | crate::ruby_sys::ruby_value_type::RUBY_T_MOVED => {
                    panic!("Attempting to access garbage collected Object")
                }
                _ => (),
            }
        };
    };
}

#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct Value(VALUE);

impl Value {
    #[inline]
    pub(crate) fn new(val: VALUE) -> Self {
        Self(val)
    }

    #[inline]
    pub(crate) fn into_inner(self) -> VALUE {
        self.0
    }

    pub fn leak(&self) {
        debug_assert_value!(self);
        // safe ffi to Ruby, call doesn't raise
        unsafe { rb_gc_register_mark_object(self.0 as VALUE) }
    }

    #[inline]
    pub fn to_bool(&self) -> bool {
        self.0 & !(ruby_special_consts::RUBY_Qnil as VALUE) != 0
    }

    #[inline]
    pub fn is_nil(&self) -> bool {
        self.0 == ruby_special_consts::RUBY_Qnil as VALUE
    }
}

impl Default for Value {
    fn default() -> Self {
        Value(ruby_special_consts::RUBY_Qnil as VALUE)
    }
}

impl From<i8> for Value {
    fn from(value: i8) -> Self {
        Integer::from_i64(value as i64).into()
    }
}

impl From<i16> for Value {
    fn from(value: i16) -> Self {
        Integer::from_i64(value as i64).into()
    }
}

impl From<i32> for Value {
    fn from(value: i32) -> Self {
        Integer::from_i64(value as i64).into()
    }
}

impl From<i64> for Value {
    fn from(value: i64) -> Self {
        Integer::from_i64(value).into()
    }
}

impl From<isize> for Value {
    fn from(value: isize) -> Self {
        Integer::from_i64(value as i64).into()
    }
}

impl From<u8> for Value {
    fn from(value: u8) -> Self {
        Integer::from_u64(value as u64).into()
    }
}

impl From<u16> for Value {
    fn from(value: u16) -> Self {
        Integer::from_u64(value as u64).into()
    }
}

impl From<u32> for Value {
    fn from(value: u32) -> Self {
        Integer::from_u64(value as u64).into()
    }
}

impl From<u64> for Value {
    fn from(value: u64) -> Self {
        Integer::from_u64(value).into()
    }
}

impl From<usize> for Value {
    fn from(value: usize) -> Self {
        Integer::from_u64(value as u64).into()
    }
}

impl From<f32> for Value {
    fn from(value: f32) -> Self {
        Float::from_f64(value as f64).into()
    }
}

impl From<f64> for Value {
    fn from(value: f64) -> Self {
        Float::from_f64(value).into()
    }
}

/// Protects a Ruby Value from the garbage collector
///
/// See also Value::leak for a value that should be permanently excluded from
/// garbage collection
pub struct BoxValue(Box<Value>);

impl BoxValue {
    /// # Safety
    ///
    /// Value must not have been garbage collected. The easiest way to verify
    /// this from Rust is to have only ever kept the Value on the stack (Ruby's
    /// GC scans the stack and treats it as a GC root), never on the heap (e.g.
    /// in a Box or collection like a Vec).
    pub unsafe fn new(val: Value) -> Self {
        debug_assert_value!(val);
        let mut boxed = Box::new(val);
        rb_gc_register_address(boxed.as_mut() as *mut _ as *mut VALUE);
        Self(boxed)
    }
}

impl Drop for BoxValue {
    fn drop(&mut self) {
        unsafe {
            rb_gc_unregister_address(self.0.as_mut() as *mut _ as *mut VALUE);
        }
    }
}

impl AsRef<Value> for BoxValue {
    fn as_ref(&self) -> &Value {
        &self.0
    }
}

impl AsMut<Value> for BoxValue {
    fn as_mut(&mut self) -> &mut Value {
        &mut self.0
    }
}

impl Deref for BoxValue {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for BoxValue {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl From<BoxValue> for Value {
    fn from(val: BoxValue) -> Self {
        *val
    }
}

#[repr(transparent)]
pub struct Qfalse(VALUE);

impl Qfalse {
    pub const fn new() -> Self {
        Qfalse(ruby_special_consts::RUBY_Qfalse as VALUE)
    }

    pub fn from_value(val: &Value) -> Option<Self> {
        (val.into_inner() == ruby_special_consts::RUBY_Qfalse as VALUE).then(Self::new)
    }
}

impl Deref for Qfalse {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        let self_ptr = self as *const Self;
        let value_ptr = self_ptr as *const Self::Target;
        // we just got this pointer from &self, so we know it's valid to deref
        unsafe { &*value_ptr }
    }
}

impl From<Qfalse> for Value {
    fn from(val: Qfalse) -> Self {
        *val
    }
}

#[repr(transparent)]
pub struct Qtrue(VALUE);

impl Qtrue {
    pub const fn new() -> Self {
        Qtrue(ruby_special_consts::RUBY_Qtrue as VALUE)
    }

    pub fn from_value(val: &Value) -> Option<Self> {
        (val.into_inner() == ruby_special_consts::RUBY_Qtrue as VALUE).then(Self::new)
    }
}

impl Deref for Qtrue {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        let self_ptr = self as *const Self;
        let value_ptr = self_ptr as *const Self::Target;
        // we just got this pointer from &self, so we know it's valid to deref
        unsafe { &*value_ptr }
    }
}

impl From<Qtrue> for Value {
    fn from(val: Qtrue) -> Self {
        *val
    }
}

#[repr(transparent)]
pub struct Qnil(VALUE);

impl Qnil {
    pub const fn new() -> Self {
        Qnil(ruby_special_consts::RUBY_Qnil as VALUE)
    }

    pub fn from_value(val: &Value) -> Option<Self> {
        (val.into_inner() == ruby_special_consts::RUBY_Qnil as VALUE).then(Self::new)
    }
}

impl Deref for Qnil {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        let self_ptr = self as *const Self;
        let value_ptr = self_ptr as *const Self::Target;
        // we just got this pointer from &self, so we know it's valid to deref
        unsafe { &*value_ptr }
    }
}

impl From<Qnil> for Value {
    fn from(val: Qnil) -> Self {
        *val
    }
}

#[repr(transparent)]
pub struct Qundef(VALUE);

impl Qundef {
    pub const fn new() -> Self {
        Qundef(ruby_special_consts::RUBY_Qundef as VALUE)
    }

    pub fn from_value(val: &Value) -> Option<Self> {
        (val.into_inner() == ruby_special_consts::RUBY_Qundef as VALUE).then(Self::new)
    }

    pub fn to_value(&self) -> Value {
        Value::new(self.0)
    }
}

#[repr(transparent)]
pub struct Symbol(VALUE);

impl Symbol {
    pub fn from_value(val: &Value) -> Option<Self> {
        const MASK: usize = !(usize::MAX << ruby_special_consts::RUBY_SPECIAL_SHIFT as usize);
        ((val.into_inner() as usize & MASK) == ruby_special_consts::RUBY_SYMBOL_FLAG as usize)
            .then(|| Self(val.into_inner()))
    }

    // TODO does this have a use?
    #[allow(dead_code)]
    pub(crate) fn from_id(id: &Id) -> Self {
        // safe ffi to Ruby, arg is value from Ruby, call doesn't raise
        unsafe { Self(rb_id2sym(id.0)) }
    }

    pub(crate) fn to_id(&self) -> Id {
        // safe ffi to Ruby, arg is value from Ruby, call doesn't raise
        unsafe { Id(rb_sym2id(self.0)) }
    }
}

impl Deref for Symbol {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        let self_ptr = self as *const Self;
        let value_ptr = self_ptr as *const Self::Target;
        // we just got this pointer from &self, so we know it's valid to deref
        unsafe { &*value_ptr }
    }
}

impl From<Symbol> for Value {
    fn from(val: Symbol) -> Self {
        *val
    }
}

#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub(crate) struct Id(ID);

impl Id {
    pub(crate) fn into_inner(self) -> ID {
        self.0
    }
}

#[repr(transparent)]
pub struct Fixnum(pub(crate) VALUE);

impl Fixnum {
    pub fn from_value(val: &Value) -> Option<Self> {
        (val.into_inner() & ruby_special_consts::RUBY_FIXNUM_FLAG as VALUE != 0)
            .then(|| Self(val.into_inner()))
    }

    pub fn from_i64(n: i64) -> Result<Self, RBignum> {
        let val = unsafe { Value::new(rb_ll2inum(n)) };
        Self::from_value(&val).ok_or_else(|| {
            unsafe { RBignum::from_value(&val) }.expect("i64 should convert to fixnum or bignum")
        })
    }

    pub fn from_u64(n: u64) -> Result<Self, RBignum> {
        let val = unsafe { Value::new(rb_ull2inum(n)) };
        Self::from_value(&val).ok_or_else(|| {
            unsafe { RBignum::from_value(&val) }.expect("u64 should convert to fixnum or bignum")
        })
    }

    fn is_negative(&self) -> bool {
        unsafe { transmute::<_, c_long>(self.0) < 0 }
    }

    pub fn to_i8(&self) -> Result<i8, Error> {
        let mut res = 0;
        protect(|| {
            res = unsafe { rb_num2long(self.into_inner()) };
            *Qnil::new()
        })?;
        if res > i8::MAX as c_long {
            return Err(Error::range_error("fixnum too big to convert into `i8`"));
        }
        Ok(res as i8)
    }

    pub fn to_i16(&self) -> Result<i16, Error> {
        let mut res = 0;
        protect(|| {
            res = unsafe { rb_num2short(self.into_inner()) };
            *Qnil::new()
        })?;
        Ok(res)
    }

    pub fn to_i32(&self) -> Result<i32, Error> {
        let mut res = 0;
        protect(|| {
            res = unsafe { rb_num2long(self.into_inner()) };
            *Qnil::new()
        })?;
        if res > i32::MAX as c_long {
            return Err(Error::range_error("fixnum too big to convert into `i32`"));
        }
        Ok(res as i32)
    }

    pub fn to_i64(&self) -> i64 {
        unsafe { rb_num2ll(self.into_inner()) }
    }

    pub fn to_isize(&self) -> Result<isize, Error> {
        let mut res = 0;
        protect(|| {
            res = unsafe { rb_num2long(self.into_inner()) };
            *Qnil::new()
        })?;
        if res > isize::MAX as c_long {
            return Err(Error::range_error("fixnum too big to convert into `isize`"));
        }
        Ok(res as isize)
    }

    pub fn to_u8(&self) -> Result<u8, Error> {
        if self.is_negative() {
            return Err(Error::range_error(
                "can't convert negative integer to unsigned",
            ));
        }
        let mut res = 0;
        protect(|| {
            res = unsafe { rb_num2ulong(self.into_inner()) };
            *Qnil::new()
        })?;
        if res > u8::MAX as c_ulong {
            return Err(Error::range_error("fixnum too big to convert into `u8`"));
        }
        Ok(res as u8)
    }

    pub fn to_u16(&self) -> Result<u16, Error> {
        if self.is_negative() {
            return Err(Error::range_error(
                "can't convert negative integer to unsigned",
            ));
        }
        let mut res = 0;
        protect(|| {
            res = unsafe { rb_num2ushort(self.into_inner()) };
            *Qnil::new()
        })?;
        Ok(res)
    }

    pub fn to_u32(&self) -> Result<u32, Error> {
        if self.is_negative() {
            return Err(Error::range_error(
                "can't convert negative integer to unsigned",
            ));
        }
        let mut res = 0;
        protect(|| {
            res = unsafe { rb_num2ulong(self.into_inner()) };
            *Qnil::new()
        })?;
        if res > u32::MAX as c_ulong {
            return Err(Error::range_error("fixnum too big to convert into `u32`"));
        }
        Ok(res as u32)
    }

    pub fn to_u64(&self) -> Result<u64, Error> {
        if self.is_negative() {
            return Err(Error::range_error(
                "can't convert negative integer to unsigned",
            ));
        }
        let mut res = 0;
        unsafe {
            protect(|| {
                res = rb_num2ull(self.into_inner());
                *Qnil::new()
            })?;
        }
        Ok(res)
    }

    pub fn to_usize(&self) -> Result<usize, Error> {
        if self.is_negative() {
            return Err(Error::range_error(
                "can't convert negative integer to unsigned",
            ));
        }
        let mut res = 0;
        protect(|| {
            res = unsafe { rb_num2ulong(self.into_inner()) };
            *Qnil::new()
        })?;
        if res > usize::MAX as c_ulong {
            return Err(Error::range_error("fixnum too big to convert into `usize`"));
        }
        Ok(res as usize)
    }
}

impl Deref for Fixnum {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        let self_ptr = self as *const Self;
        let value_ptr = self_ptr as *const Self::Target;
        // we just got this pointer from &self, so we know it's valid to deref
        unsafe { &*value_ptr }
    }
}

impl From<Fixnum> for Value {
    fn from(val: Fixnum) -> Self {
        *val
    }
}

#[repr(transparent)]
pub struct Flonum(pub(crate) VALUE);

impl Flonum {
    pub fn from_value(val: &Value) -> Option<Self> {
        (val.into_inner() & ruby_special_consts::RUBY_FLONUM_MASK as VALUE
            == ruby_special_consts::RUBY_FLONUM_FLAG as VALUE)
            .then(|| Self(val.into_inner()))
    }

    pub fn from_f64(n: f64) -> Result<Self, RFloat> {
        let val = unsafe { Value::new(rb_float_new(n)) };
        Self::from_value(&val).ok_or_else(|| {
            unsafe { RFloat::from_value(&val) }.expect("f64 should convert to flonum or float")
        })
    }

    pub fn to_f64(&self) -> f64 {
        unsafe { rb_float_value(self.into_inner()) }
    }
}

impl Deref for Flonum {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        let self_ptr = self as *const Self;
        let value_ptr = self_ptr as *const Self::Target;
        // we just got this pointer from &self, so we know it's valid to deref
        unsafe { &*value_ptr }
    }
}

impl From<Flonum> for Value {
    fn from(val: Flonum) -> Self {
        *val
    }
}
