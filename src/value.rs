use std::{
    borrow::Cow,
    ffi::CStr,
    fmt,
    mem::transmute,
    num::NonZeroUsize,
    ops::{Deref, DerefMut},
    os::raw::{c_char, c_int, c_long, c_ulong},
    ptr,
};

use crate::{
    enumerator::Enumerator,
    error::{protect, Error},
    float::Float,
    integer::{Integer, IntegerType},
    module::Module,
    r_bignum::RBignum,
    r_class::RClass,
    r_float::RFloat,
    r_string::RString,
    ruby_sys::{
        rb_any_to_s, rb_cFalseClass, rb_cFloat, rb_cInteger, rb_cNilClass, rb_cSymbol,
        rb_cTrueClass, rb_enumeratorize_with_size, rb_float_new, rb_float_value, rb_funcallv,
        rb_gc_register_address, rb_gc_register_mark_object, rb_gc_unregister_address, rb_id2name,
        rb_id2sym, rb_inspect, rb_intern2, rb_ll2inum, rb_num2ll, rb_num2long, rb_num2short,
        rb_num2ull, rb_num2ulong, rb_num2ushort, rb_obj_as_string, rb_obj_classname, rb_obj_freeze,
        rb_obj_is_kind_of, rb_sym2id, rb_ull2inum, ruby_fl_type, ruby_special_consts,
        ruby_value_type, RBasic, ID, VALUE,
    },
    symbol::Symbol,
    try_convert::{ArgList, TryConvert, TryConvertOwned},
};

// This isn't infallible, if the original object was gc'd and that slot
// reused already this won't panic like it should, but we're trying our
// best here.
#[macro_export]
macro_rules! debug_assert_value {
    ($value:expr) => {
        // The memory this points to is managed by Ruby's GC and we can't
        // really know if it's safe to access as with GC compaction this may
        // point to memory now outside that owned by the process. We will likly
        // segfault in that case, which is kind of OK, as we're trying to panic
        // anyway.
        #[allow(unused_unsafe)]
        #[cfg(debug_assertions)]
        match unsafe { $value.rb_type() } {
            crate::ruby_sys::ruby_value_type::RUBY_T_NONE
            | crate::ruby_sys::ruby_value_type::RUBY_T_ZOMBIE => {
                panic!("Attempting to access garbage collected Object")
            }
            #[cfg(ruby_gte_2_7)]
            crate::ruby_sys::ruby_value_type::RUBY_T_MOVED => {
                panic!("Attempting to access garbage collected Object")
            }
            _ => (),
        };
    };
}

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Value(VALUE);

impl Value {
    #[inline]
    pub(crate) const fn new(val: VALUE) -> Self {
        Self(val)
    }

    #[inline]
    pub(crate) unsafe fn r_basic_unchecked(self) -> ptr::NonNull<RBasic> {
        #[cfg(debug_assertions)]
        if self.is_immediate() {
            panic!("attempting to access immediate value as pointer");
        }
        ptr::NonNull::new_unchecked(self.0 as *mut RBasic)
    }

    #[inline]
    fn is_immediate(self) -> bool {
        let value_p = self.as_rb_value();
        let immediate_p = value_p & ruby_special_consts::RUBY_IMMEDIATE_MASK as VALUE != 0;
        let test = value_p & !(ruby_special_consts::RUBY_Qnil as VALUE) != 0;
        immediate_p || !test // special_const_p
    }

    #[inline]
    pub(crate) fn r_basic(self) -> Option<ptr::NonNull<RBasic>> {
        unsafe { (!self.is_immediate()).then(|| self.r_basic_unchecked()) }
    }

    #[inline]
    fn is_false(self) -> bool {
        self.as_rb_value() == ruby_special_consts::RUBY_Qfalse as VALUE
    }

    #[inline]
    pub fn is_nil(self) -> bool {
        self.as_rb_value() == ruby_special_consts::RUBY_Qnil as VALUE
    }

    #[inline]
    fn is_true(self) -> bool {
        self.as_rb_value() == ruby_special_consts::RUBY_Qtrue as VALUE
    }

    #[inline]
    pub(crate) fn is_undef(self) -> bool {
        self.as_rb_value() == ruby_special_consts::RUBY_Qundef as VALUE
    }

    #[inline]
    fn is_fixnum(self) -> bool {
        self.as_rb_value() & ruby_special_consts::RUBY_FIXNUM_FLAG as VALUE != 0
    }

    #[inline]
    pub(crate) fn is_static_symbol(self) -> bool {
        const MASK: usize = !(usize::MAX << ruby_special_consts::RUBY_SPECIAL_SHIFT as usize);
        self.as_rb_value() as usize & MASK == ruby_special_consts::RUBY_SYMBOL_FLAG as usize
    }

    #[inline]
    fn is_flonum(self) -> bool {
        self.as_rb_value() & ruby_special_consts::RUBY_FLONUM_MASK as VALUE
            == ruby_special_consts::RUBY_FLONUM_FLAG as VALUE
    }

    // derefs a raw pointer that under GC compaction may be outside the
    // process's memory space if the Value has been allowed to get GC'd
    pub(crate) fn rb_type(self) -> ruby_value_type {
        match self.r_basic() {
            Some(r_basic) => {
                unsafe {
                    let ret = r_basic.as_ref().flags & (ruby_value_type::RUBY_T_MASK as VALUE);
                    // this bit is safe, ruby_value_type is #[repr(u32)], the flags
                    // value set by Ruby, and Ruby promises that flags masked like
                    // this will always be a valid entry in this enum
                    std::mem::transmute(ret as u32)
                }
            }
            None => {
                if self.is_false() {
                    ruby_value_type::RUBY_T_FALSE
                } else if self.is_nil() {
                    ruby_value_type::RUBY_T_NIL
                } else if self.is_true() {
                    ruby_value_type::RUBY_T_TRUE
                } else if self.is_undef() {
                    ruby_value_type::RUBY_T_UNDEF
                } else if self.is_fixnum() {
                    ruby_value_type::RUBY_T_FIXNUM
                } else if self.is_static_symbol() {
                    ruby_value_type::RUBY_T_SYMBOL
                } else if self.is_flonum() {
                    ruby_value_type::RUBY_T_FLOAT
                } else {
                    unreachable!()
                }
            }
        }
    }

    pub fn class(self) -> RClass {
        unsafe {
            match self.r_basic() {
                Some(r_basic) => RClass::from_rb_value_unchecked(r_basic.as_ref().klass),
                None => {
                    if self.is_false() {
                        RClass::from_rb_value_unchecked(rb_cFalseClass)
                    } else if self.is_nil() {
                        RClass::from_rb_value_unchecked(rb_cNilClass)
                    } else if self.is_true() {
                        RClass::from_rb_value_unchecked(rb_cTrueClass)
                    } else if self.is_undef() {
                        panic!("undef does not have a class")
                    } else if self.is_fixnum() {
                        RClass::from_rb_value_unchecked(rb_cInteger)
                    } else if self.is_static_symbol() {
                        RClass::from_rb_value_unchecked(rb_cSymbol)
                    } else if self.is_flonum() {
                        RClass::from_rb_value_unchecked(rb_cFloat)
                    } else {
                        unreachable!()
                    }
                }
            }
        }
    }

    #[inline]
    pub(crate) const fn as_rb_value(self) -> VALUE {
        self.0
    }

    pub fn leak(self) {
        debug_assert_value!(self);
        // safe ffi to Ruby, call doesn't raise
        unsafe { rb_gc_register_mark_object(self.as_rb_value()) }
    }

    pub fn is_frozen(self) -> bool {
        match self.r_basic() {
            None => true,
            Some(r_basic) => unsafe {
                r_basic.as_ref().flags & ruby_fl_type::RUBY_FL_FREEZE as VALUE != 0
            },
        }
    }

    pub fn check_frozen(self) -> Result<(), Error> {
        if self.is_frozen() {
            Err(Error::frozen_error(format!(
                "can't modify frozen {}",
                unsafe { self.classname() }
            )))
        } else {
            Ok(())
        }
    }

    pub fn freeze(self) {
        unsafe { rb_obj_freeze(self.as_rb_value()) };
    }

    #[inline]
    pub fn to_bool(self) -> bool {
        self.as_rb_value() & !(ruby_special_consts::RUBY_Qnil as VALUE) != 0
    }

    pub fn funcall<M, A, T>(self, method: M, args: A) -> Result<T, Error>
    where
        M: Into<Id>,
        A: ArgList,
        T: TryConvert,
    {
        unsafe {
            let id = method.into();
            let args = args.into_arg_list();
            let slice = args.as_ref();
            protect(|| {
                Value::new(rb_funcallv(
                    self.as_rb_value(),
                    id.as_rb_id(),
                    slice.len() as c_int,
                    slice.as_ptr() as *const VALUE,
                ))
            })
            .and_then(|v| v.try_convert())
        }
    }

    pub fn to_r_string(self) -> Result<RString, Error> {
        match RString::from_value(self) {
            Some(v) => Ok(v),
            None => unsafe {
                protect(|| Value::new(rb_obj_as_string(self.as_rb_value())))
                    .map(|v| RString::from_rb_value_unchecked(v.as_rb_value()))
            },
        }
    }

    /// # Safety
    ///
    /// Ruby may modify or free the memory backing the returned str, the caller
    /// must ensure this does not happen.
    #[allow(clippy::wrong_self_convention)]
    pub unsafe fn to_s(&self) -> Result<Cow<str>, Error> {
        if let Some(s) = RString::ref_from_value(self) {
            if s.is_utf8_compatible_encoding() {
                return s.as_str().map(Cow::Borrowed);
            } else {
                return (*s).to_string().map(Cow::Owned);
            }
        }
        self.to_r_string()
            .and_then(|s| s.to_string().map(Cow::Owned))
    }

    /// # Safety
    ///
    /// Ruby may modify or free the memory backing the returned str, the caller
    /// must ensure this does not happen.
    #[allow(clippy::wrong_self_convention)]
    pub(crate) unsafe fn to_s_infallible(&self) -> Cow<str> {
        match self.to_s() {
            Ok(v) => v,
            Err(_) => Cow::Owned(
                RString::from_rb_value_unchecked(rb_any_to_s(self.as_rb_value()))
                    .to_string_lossy()
                    .into_owned(),
            ),
        }
    }

    pub fn inspect(self) -> String {
        unsafe {
            let s = protect(|| Value::new(rb_inspect(self.as_rb_value())))
                .map(|v| RString::from_rb_value_unchecked(v.as_rb_value()))
                .unwrap_or_else(|_| {
                    RString::from_rb_value_unchecked(rb_any_to_s(self.as_rb_value()))
                });
            s.encode_utf8().unwrap_or(s).to_string_lossy().into_owned()
        }
    }

    /// # Safety
    ///
    /// Ruby may modify or free the memory backing the returned str, the caller
    /// must ensure this does not happen.
    pub unsafe fn classname(&self) -> Cow<str> {
        let ptr = rb_obj_classname(self.as_rb_value());
        let cstr = CStr::from_ptr(ptr);
        cstr.to_string_lossy()
    }

    pub fn is_kind_of<T>(self, class: T) -> bool
    where
        T: Deref<Target = Value> + Module,
    {
        unsafe { Value::new(rb_obj_is_kind_of(self.as_rb_value(), class.as_rb_value())).to_bool() }
    }

    pub fn enumeratorize<M, A>(self, method: M, args: A) -> Enumerator
    where
        M: Into<Symbol>,
        A: ArgList,
    {
        let args = args.into_arg_list();
        let slice = args.as_ref();
        unsafe {
            Enumerator::from_rb_value_unchecked(rb_enumeratorize_with_size(
                self.as_rb_value(),
                method.into().as_rb_value(),
                slice.len() as c_int,
                slice.as_ptr() as *const VALUE,
                None,
            ))
        }
    }

    #[inline]
    pub fn try_convert<T>(&self) -> Result<T, Error>
    where
        T: TryConvert,
    {
        T::try_convert(self)
    }
}

impl Default for Value {
    fn default() -> Self {
        Value::new(ruby_special_consts::RUBY_Qnil as VALUE)
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
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

impl TryConvert for Value {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        Ok(*val)
    }
}

#[derive(Clone, Copy)]
#[repr(transparent)]
pub(crate) struct NonZeroValue(NonZeroUsize);

impl NonZeroValue {
    #[inline]
    pub(crate) const unsafe fn new_unchecked(val: Value) -> Self {
        Self(NonZeroUsize::new_unchecked(val.as_rb_value() as usize))
    }

    pub(crate) const fn get(self) -> Value {
        Value::new(self.0.get() as VALUE)
    }

    pub(crate) fn get_ref(&self) -> &Value {
        let self_ptr = self as *const Self;
        let value_ptr = self_ptr as *const Value;
        // we just got this pointer from &self, so we know it's valid to deref
        unsafe { &*value_ptr }
    }
}

/// Protects a Ruby Value from the garbage collector
///
/// See also Value::leak for a value that should be permanently excluded from
/// garbage collection
pub struct BoxValue(Box<Value>);

impl BoxValue {
    pub fn new(val: Value) -> Self {
        debug_assert_value!(val);
        let mut boxed = Box::new(val);
        unsafe { rb_gc_register_address(boxed.as_mut() as *mut _ as *mut VALUE) };
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

impl fmt::Display for BoxValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for BoxValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl From<BoxValue> for Value {
    fn from(val: BoxValue) -> Self {
        *val
    }
}

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Qfalse(VALUE);

pub const QFALSE: Qfalse = Qfalse::new();

impl Qfalse {
    #[inline]
    pub const fn new() -> Self {
        Qfalse(ruby_special_consts::RUBY_Qfalse as VALUE)
    }

    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        val.is_false().then(Self::new)
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

impl fmt::Display for Qfalse {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for Qfalse {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl From<Qfalse> for Value {
    fn from(val: Qfalse) -> Self {
        *val
    }
}

impl TryConvert for Qfalse {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        Self::from_value(*val).ok_or_else(|| {
            Error::type_error(format!(
                "no implicit conversion of {} into FalseClass",
                unsafe { val.classname() },
            ))
        })
    }
}
impl TryConvertOwned for Qfalse {}

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Qnil(NonZeroValue);

pub const QNIL: Qnil = Qnil::new();

impl Qnil {
    #[inline]
    pub const fn new() -> Self {
        unsafe {
            Self(NonZeroValue::new_unchecked(Value::new(
                ruby_special_consts::RUBY_Qnil as VALUE,
            )))
        }
    }

    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        val.is_nil().then(Self::new)
    }
}

impl Deref for Qnil {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
    }
}

impl fmt::Display for Qnil {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for Qnil {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl From<Qnil> for Value {
    fn from(val: Qnil) -> Self {
        *val
    }
}

impl From<()> for Value {
    fn from(_: ()) -> Self {
        QNIL.into()
    }
}

impl<T> From<Option<T>> for Value
where
    T: Into<Value>,
{
    fn from(val: Option<T>) -> Self {
        match val {
            Some(t) => t.into(),
            None => QNIL.into(),
        }
    }
}

impl TryConvert for Qnil {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        Self::from_value(*val).ok_or_else(|| {
            Error::type_error(format!(
                "no implicit conversion of {} into NilClass",
                unsafe { val.classname() },
            ))
        })
    }
}
impl TryConvertOwned for Qnil {}

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Qtrue(NonZeroValue);

pub const QTRUE: Qtrue = Qtrue::new();

impl Qtrue {
    #[inline]
    pub const fn new() -> Self {
        unsafe {
            Self(NonZeroValue::new_unchecked(Value::new(
                ruby_special_consts::RUBY_Qtrue as VALUE,
            )))
        }
    }

    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        val.is_true().then(Self::new)
    }
}

impl Deref for Qtrue {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
    }
}

impl fmt::Display for Qtrue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for Qtrue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl From<Qtrue> for Value {
    fn from(val: Qtrue) -> Self {
        *val
    }
}

impl From<bool> for Value {
    fn from(val: bool) -> Self {
        if val {
            QTRUE.into()
        } else {
            QFALSE.into()
        }
    }
}

impl TryConvert for Qtrue {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        Self::from_value(*val).ok_or_else(|| {
            Error::type_error(format!(
                "no implicit conversion of {} into TrueClass",
                unsafe { val.classname() },
            ))
        })
    }
}
impl TryConvertOwned for Qtrue {}

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Qundef(NonZeroValue);

pub const QUNDEF: Qundef = Qundef::new();

impl Qundef {
    #[inline]
    pub const fn new() -> Self {
        unsafe {
            Self(NonZeroValue::new_unchecked(Value::new(
                ruby_special_consts::RUBY_Qundef as VALUE,
            )))
        }
    }

    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        val.is_undef().then(Self::new)
    }

    #[inline]
    pub fn to_value(self) -> Value {
        self.0.get()
    }
}

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Fixnum(NonZeroValue);

impl Fixnum {
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            val.is_fixnum()
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        Self(NonZeroValue::new_unchecked(Value::new(val)))
    }

    pub fn from_i64(n: i64) -> Result<Self, RBignum> {
        let val = unsafe { Value::new(rb_ll2inum(n)) };
        Self::from_value(val)
            .ok_or_else(|| unsafe { RBignum::from_rb_value_unchecked(val.as_rb_value()) })
    }

    pub fn from_u64(n: u64) -> Result<Self, RBignum> {
        let val = unsafe { Value::new(rb_ull2inum(n)) };
        Self::from_value(val)
            .ok_or_else(|| unsafe { RBignum::from_rb_value_unchecked(val.as_rb_value()) })
    }

    fn is_negative(self) -> bool {
        unsafe { transmute::<_, c_long>(self.0) < 0 }
    }

    pub fn to_i8(self) -> Result<i8, Error> {
        let mut res = 0;
        protect(|| {
            res = unsafe { rb_num2long(self.as_rb_value()) };
            *QNIL
        })?;
        if res > i8::MAX as c_long {
            return Err(Error::range_error("fixnum too big to convert into `i8`"));
        }
        Ok(res as i8)
    }

    pub fn to_i16(self) -> Result<i16, Error> {
        let mut res = 0;
        protect(|| {
            res = unsafe { rb_num2short(self.as_rb_value()) };
            *QNIL
        })?;
        Ok(res)
    }

    pub fn to_i32(self) -> Result<i32, Error> {
        let mut res = 0;
        protect(|| {
            res = unsafe { rb_num2long(self.as_rb_value()) };
            *QNIL
        })?;
        if res > i32::MAX as c_long {
            return Err(Error::range_error("fixnum too big to convert into `i32`"));
        }
        Ok(res as i32)
    }

    pub fn to_i64(self) -> i64 {
        unsafe { rb_num2ll(self.as_rb_value()) }
    }

    pub fn to_isize(self) -> Result<isize, Error> {
        let mut res = 0;
        protect(|| {
            res = unsafe { rb_num2long(self.as_rb_value()) };
            *QNIL
        })?;
        if res > isize::MAX as c_long {
            return Err(Error::range_error("fixnum too big to convert into `isize`"));
        }
        Ok(res as isize)
    }

    pub fn to_u8(self) -> Result<u8, Error> {
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
        if res > u8::MAX as c_ulong {
            return Err(Error::range_error("fixnum too big to convert into `u8`"));
        }
        Ok(res as u8)
    }

    pub fn to_u16(self) -> Result<u16, Error> {
        if self.is_negative() {
            return Err(Error::range_error(
                "can't convert negative integer to unsigned",
            ));
        }
        let mut res = 0;
        protect(|| {
            res = unsafe { rb_num2ushort(self.as_rb_value()) };
            *QNIL
        })?;
        Ok(res)
    }

    pub fn to_u32(self) -> Result<u32, Error> {
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
            return Err(Error::range_error("fixnum too big to convert into `u32`"));
        }
        Ok(res as u32)
    }

    pub fn to_u64(self) -> Result<u64, Error> {
        if self.is_negative() {
            return Err(Error::range_error(
                "can't convert negative integer to unsigned",
            ));
        }
        let mut res = 0;
        unsafe {
            protect(|| {
                res = rb_num2ull(self.as_rb_value());
                *QNIL
            })?;
        }
        Ok(res)
    }

    pub fn to_usize(self) -> Result<usize, Error> {
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
            return Err(Error::range_error("fixnum too big to convert into `usize`"));
        }
        Ok(res as usize)
    }
}

impl Deref for Fixnum {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
    }
}

impl fmt::Display for Fixnum {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for Fixnum {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl From<Fixnum> for Value {
    fn from(val: Fixnum) -> Self {
        *val
    }
}

impl TryConvert for Fixnum {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        match val.try_convert::<Integer>()?.integer_type() {
            IntegerType::Fixnum(fix) => Ok(fix),
            IntegerType::Bignum(_) => Err(Error::range_error("integer to big for fixnum")),
        }
    }
}
impl TryConvertOwned for Fixnum {}

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct StaticSymbol(NonZeroValue);

impl StaticSymbol {
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            val.is_static_symbol()
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        Self(NonZeroValue::new_unchecked(Value::new(val)))
    }

    #[inline]
    pub fn new<T: Into<Id>>(name: T) -> Self {
        name.into().into()
    }

    pub fn name(self) -> Result<&'static str, Error> {
        Id::from(self).name()
    }
}

impl Deref for StaticSymbol {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
    }
}

impl fmt::Display for StaticSymbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for StaticSymbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl From<Id> for StaticSymbol {
    fn from(id: Id) -> Self {
        unsafe { Self::from_rb_value_unchecked(rb_id2sym(id.as_rb_id())) }
    }
}

impl From<&str> for StaticSymbol {
    fn from(s: &str) -> Self {
        Id::from(s).into()
    }
}

impl From<String> for StaticSymbol {
    fn from(s: String) -> Self {
        Id::from(s).into()
    }
}

impl From<StaticSymbol> for Value {
    fn from(val: StaticSymbol) -> Self {
        *val
    }
}

impl TryConvert for StaticSymbol {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        val.try_convert::<Symbol>().map(|s| s.to_static())
    }
}
impl TryConvertOwned for StaticSymbol {}

#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct Id(ID);

impl Id {
    pub(crate) fn as_rb_id(self) -> ID {
        self.0
    }

    pub fn name(self) -> Result<&'static str, Error> {
        unsafe {
            let ptr = rb_id2name(self.as_rb_id());
            let cstr = CStr::from_ptr(ptr);
            cstr.to_str()
                .map_err(|e| Error::encoding_error(e.to_string()))
        }
    }
}

impl From<&str> for Id {
    fn from(s: &str) -> Self {
        Self(unsafe { rb_intern2(s.as_ptr() as *const c_char, s.len() as c_long) })
    }
}

impl From<String> for Id {
    fn from(s: String) -> Self {
        s.as_str().into()
    }
}

impl From<StaticSymbol> for Id {
    fn from(sym: StaticSymbol) -> Self {
        Self(unsafe { rb_sym2id(sym.as_rb_value()) })
    }
}

impl From<Symbol> for Id {
    fn from(sym: Symbol) -> Self {
        Self(unsafe { rb_sym2id(sym.as_rb_value()) })
    }
}

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Flonum(NonZeroValue);

impl Flonum {
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            val.is_flonum()
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        Self(NonZeroValue::new_unchecked(Value::new(val)))
    }

    pub fn from_f64(n: f64) -> Result<Self, RFloat> {
        let val = unsafe { Value::new(rb_float_new(n)) };
        Self::from_value(val)
            .ok_or_else(|| unsafe { RFloat::from_rb_value_unchecked(val.as_rb_value()) })
    }

    pub fn to_f64(self) -> f64 {
        unsafe { rb_float_value(self.as_rb_value()) }
    }
}

impl Deref for Flonum {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
    }
}

impl fmt::Display for Flonum {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for Flonum {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl From<Flonum> for Value {
    fn from(val: Flonum) -> Self {
        *val
    }
}

impl TryConvert for Flonum {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        let float = val.try_convert::<Float>()?;
        if let Some(flonum) = Flonum::from_value(*float) {
            Ok(flonum)
        } else {
            Err(Error::range_error("float out of range for flonum"))
        }
    }
}
impl TryConvertOwned for Flonum {}
