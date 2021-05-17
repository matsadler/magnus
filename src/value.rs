use std::ops::{Deref, DerefMut};

use crate::ruby_sys::{
    rb_gc_register_address, rb_gc_register_mark_object, rb_gc_unregister_address, rb_id2sym,
    rb_sym2id, ruby_special_consts, ID, VALUE,
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
        Value(ruby_special_consts::RUBY_Qundef as VALUE)
    }
}

impl<T> From<T> for Value
where
    T: Deref<Target = Value>,
{
    fn from(val: T) -> Self {
        *val
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

impl Symbol {
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

#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub(crate) struct Id(ID);

impl Id {
    pub(crate) fn into_inner(self) -> ID {
        self.0
    }
}

#[repr(transparent)]
pub struct Fixnum(VALUE);

impl Fixnum {
    pub fn from_value(val: &Value) -> Option<Self> {
        (val.into_inner() & ruby_special_consts::RUBY_FIXNUM_FLAG as VALUE != 0)
            .then(|| Self(val.into_inner()))
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

#[repr(transparent)]
pub struct Flonum(VALUE);

impl Flonum {
    pub fn from_value(val: &Value) -> Option<Self> {
        (val.into_inner() & ruby_special_consts::RUBY_FLONUM_MASK as VALUE
            == ruby_special_consts::RUBY_FLONUM_FLAG as VALUE)
            .then(|| Self(val.into_inner()))
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
