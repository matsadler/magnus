//! Types for working with Ruby's VALUE type, representing all objects, and 'immediate' values such as Fixnum.

#[cfg(ruby_use_flonum)]
mod flonum;

use std::{
    borrow::{Borrow, Cow},
    cell::UnsafeCell,
    convert::TryFrom,
    ffi::CStr,
    fmt,
    hash::{Hash, Hasher},
    marker::PhantomData,
    mem::transmute,
    num::NonZeroUsize,
    ops::{Deref, DerefMut},
    os::raw::{c_char, c_int, c_long, c_ulong},
    ptr,
    sync::Once,
};

#[cfg(ruby_use_flonum)]
pub use flonum::Flonum;
use rb_sys::{
    rb_any_to_s, rb_block_call, rb_check_funcall, rb_check_id, rb_check_id_cstr,
    rb_check_symbol_cstr, rb_enumeratorize_with_size, rb_eql, rb_equal, rb_funcall_with_block,
    rb_funcallv, rb_funcallv_public, rb_gc_register_address, rb_gc_unregister_address, rb_hash,
    rb_id2name, rb_id2sym, rb_inspect, rb_intern3, rb_ll2inum, rb_obj_as_string, rb_obj_classname,
    rb_obj_freeze, rb_obj_is_kind_of, rb_obj_respond_to, rb_sym2id, rb_ull2inum, ruby_fl_type,
    ruby_special_consts, ruby_value_type, RBasic, ID, VALUE,
};

// These don't seem to appear consistently in bindgen output, not sure if they
// aren't consistently defined in the headers or what. Lets just do it
// ourselves.
const RUBY_FIXNUM_MAX: c_ulong = (c_long::MAX / 2) as c_ulong;
const RUBY_FIXNUM_MIN: c_long = c_long::MIN / 2;

use crate::{
    block::Proc,
    class::RClass,
    encoding::EncodingCapable,
    enumerator::Enumerator,
    error::{protect, Error},
    integer::{Integer, IntegerType},
    into_value::{ArgList, IntoValue, IntoValueFromNative},
    method::{Block, BlockReturn},
    module::Module,
    numeric::Numeric,
    r_bignum::RBignum,
    r_string::RString,
    symbol::{IntoSymbol, Symbol},
    try_convert::{TryConvert, TryConvertOwned},
    Ruby,
};

/// Ruby's `VALUE` type, which can represent any Ruby object.
///
/// Methods for `Value` are implemented on the [`ReprValue`] trait, which is
/// also implemented for all Ruby types.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Value(VALUE, PhantomData<*mut RBasic>);

impl Value {
    #[inline]
    pub(crate) const fn new(val: VALUE) -> Self {
        Self(val, PhantomData)
    }

    #[inline]
    pub(crate) const fn as_rb_value(self) -> VALUE {
        self.0
    }

    /// Convert `self` to the Rust type `T`.
    ///
    /// `val.try_convert()` is equivalent to `TryConvert::try_convert(val)`.
    ///
    /// See the types that [`TryConvert`] is implemented on for what this
    /// method can convert to.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Value};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert_eq!(eval::<Value>("42").unwrap().try_convert::<i64>().unwrap(), 42);
    /// assert_eq!(eval::<Value>("1.23").unwrap().try_convert::<i64>().unwrap(), 1);
    /// assert_eq!(eval::<Value>("1").unwrap().try_convert::<f64>().unwrap(), 1.0);
    /// assert_eq!(eval::<Value>("nil").unwrap().try_convert::<Option<i64>>().unwrap(), None);
    /// assert_eq!(eval::<Value>("42").unwrap().try_convert::<Option<i64>>().unwrap(), Some(42));
    /// ```
    pub fn try_convert<T>(self) -> Result<T, Error>
    where
        T: TryConvert,
    {
        T::try_convert(self.as_value())
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

impl IntoValue for Value {
    fn into_value_with(self, _: &Ruby) -> Value {
        self
    }
}

impl IntoValue for i8 {
    fn into_value_with(self, handle: &Ruby) -> Value {
        handle.integer_from_i64(self as i64).into_value_with(handle)
    }
}

unsafe impl IntoValueFromNative for i8 {}

impl IntoValue for i16 {
    fn into_value_with(self, handle: &Ruby) -> Value {
        handle.integer_from_i64(self as i64).into_value_with(handle)
    }
}

unsafe impl IntoValueFromNative for i16 {}

impl IntoValue for i32 {
    fn into_value_with(self, handle: &Ruby) -> Value {
        handle.integer_from_i64(self as i64).into_value_with(handle)
    }
}

unsafe impl IntoValueFromNative for i32 {}

impl IntoValue for i64 {
    fn into_value_with(self, handle: &Ruby) -> Value {
        handle.integer_from_i64(self).into_value_with(handle)
    }
}

unsafe impl IntoValueFromNative for i64 {}

impl IntoValue for isize {
    fn into_value_with(self, handle: &Ruby) -> Value {
        handle.integer_from_i64(self as i64).into_value_with(handle)
    }
}

unsafe impl IntoValueFromNative for isize {}

impl IntoValue for u8 {
    fn into_value_with(self, handle: &Ruby) -> Value {
        handle.integer_from_u64(self as u64).into_value_with(handle)
    }
}

unsafe impl IntoValueFromNative for u8 {}

impl IntoValue for u16 {
    fn into_value_with(self, handle: &Ruby) -> Value {
        handle.integer_from_u64(self as u64).into_value_with(handle)
    }
}

unsafe impl IntoValueFromNative for u16 {}

impl IntoValue for u32 {
    fn into_value_with(self, handle: &Ruby) -> Value {
        handle.integer_from_u64(self as u64).into_value_with(handle)
    }
}

unsafe impl IntoValueFromNative for u32 {}

impl IntoValue for u64 {
    fn into_value_with(self, handle: &Ruby) -> Value {
        handle.integer_from_u64(self).into_value_with(handle)
    }
}

unsafe impl IntoValueFromNative for u64 {}

impl IntoValue for usize {
    fn into_value_with(self, handle: &Ruby) -> Value {
        handle.integer_from_u64(self as u64).into_value_with(handle)
    }
}

unsafe impl IntoValueFromNative for usize {}

impl IntoValue for f32 {
    fn into_value_with(self, handle: &Ruby) -> Value {
        handle.float_from_f64(self as f64).into_value_with(handle)
    }
}

unsafe impl IntoValueFromNative for f32 {}

impl IntoValue for f64 {
    fn into_value_with(self, handle: &Ruby) -> Value {
        handle.float_from_f64(self).into_value_with(handle)
    }
}

unsafe impl IntoValueFromNative for f64 {}

impl TryConvert for Value {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Ok(val)
    }
}

/// A wrapper to make a Ruby type [`Send`] + [`Sync`].
///
/// Ruby types are not [`Send`] or [`Sync`] as they provide a way to call
/// Ruby's APIs, which it is not safe to do from a non-Ruby thread.
///
/// Ruby types are safe to send between Ruby threads, but Rust's trait system
/// currently can not model this detail.
///
/// To resolve this, the `Opaque` type makes a Ruby type [`Send`] + [`Sync`]
/// by removing the ability to do anything with it, making it impossible to
/// call Ruby's API on non-Ruby threads.
///
/// An `Opaque<T>` can be unwrapped to `T` with [`Ruby::unwrap_opaque`],
/// as it is only possible to instantiate a [`Ruby`] on a Ruby thread.
/// # Examples
///
/// ```
/// use magnus::{eval, value::Opaque, RString, Ruby};
/// # let _cleanup = unsafe { magnus::embed::init() };
/// let opaque_str = Opaque::from(RString::new("example"));
///
/// // send to another Ruby thread
///
/// let handle = Ruby::get().unwrap(); // errors on non-Ruby thread
/// let str = handle.unwrap_opaque(opaque_str);
/// let res: bool = eval!(r#"str == "example""#, str).unwrap();
/// assert!(res);
/// ```
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Opaque<T>(T);

// implementation detail for opaque_attr_accessor proc macro attribute
#[doc(hidden)]
pub trait OpaqueVal {
    type Val: ReprValue;
}

impl<T> OpaqueVal for Opaque<T>
where
    T: ReprValue,
{
    type Val = T;
}

impl<T> From<T> for Opaque<T>
where
    T: ReprValue,
{
    fn from(val: T) -> Self {
        Self(val)
    }
}

impl<T> IntoValue for Opaque<T>
where
    T: IntoValue,
{
    fn into_value_with(self, handle: &Ruby) -> Value {
        self.0.into_value_with(handle)
    }
}

#[allow(missing_docs)]
impl Ruby {
    pub fn unwrap_opaque<T>(&self, val: Opaque<T>) -> T
    where
        T: ReprValue,
    {
        val.0
    }
}

unsafe impl<T: ReprValue> Send for Opaque<T> {}
unsafe impl<T: ReprValue> Sync for Opaque<T> {}

pub(crate) mod private {
    use super::*;
    use crate::value::ReprValue as _;

    /// Marker trait for types that have the same representation as [`Value`].
    ///
    /// Types that are `ReprValue` can be safely transmuted to Value.
    ///
    /// # Safety
    ///
    /// This trait should only be implemented for types that a guaranteed to
    /// have the same layout as [`Value`] and have come from the Ruby VM.
    pub unsafe trait ReprValue: Copy {
        /// Convert `val` to a `Self`.
        ///
        /// # Safety
        ///
        /// This should only be used when `val` is known to uphold all the
        // invariants of `Self`. It is recommended not to use this method.
        unsafe fn from_value_unchecked(val: Value) -> Self {
            *(&val as *const Value as *const Self)
        }

        fn copy_as_value(self) -> Value {
            // This trait is only ever implemented for things with the same
            // representation as Value
            unsafe { *(&self as *const Self as *const Value) }
        }

        fn as_value_ref(&self) -> &Value {
            // This trait is only ever implemented for things with the same
            // representation as Value
            unsafe { &*(self as *const Self as *const Value) }
        }

        fn as_rb_value(self) -> VALUE {
            self.copy_as_value().0
        }

        unsafe fn r_basic_unchecked(self) -> ptr::NonNull<RBasic> {
            #[cfg(debug_assertions)]
            if self.is_immediate() {
                panic!("attempting to access immediate value as pointer");
            }
            ptr::NonNull::new_unchecked(self.copy_as_value().0 as *mut RBasic)
        }

        /// Returns whether `self` is an 'immediate' value.
        ///
        /// 'immediate' values are encoded directly into the `Value` and require
        /// no additional lookup. They will never be garbage collected.
        ///
        /// non-immediate values are pointers to other memory holding the data for
        /// the object.
        fn is_immediate(self) -> bool {
            let value_p = self.as_rb_value();
            let immediate_p = value_p & ruby_special_consts::RUBY_IMMEDIATE_MASK as VALUE != 0;
            let test = value_p & !(ruby_special_consts::RUBY_Qnil as VALUE) != 0;
            immediate_p || !test // special_const_p
        }

        fn r_basic(self) -> Option<ptr::NonNull<RBasic>> {
            unsafe { (!self.is_immediate()).then(|| self.r_basic_unchecked()) }
        }

        fn is_false(self) -> bool {
            self.as_rb_value() == ruby_special_consts::RUBY_Qfalse as VALUE
        }

        fn is_true(self) -> bool {
            self.as_rb_value() == ruby_special_consts::RUBY_Qtrue as VALUE
        }

        fn is_undef(self) -> bool {
            self.as_rb_value() == ruby_special_consts::RUBY_Qundef as VALUE
        }

        fn is_fixnum(self) -> bool {
            self.as_rb_value() & ruby_special_consts::RUBY_FIXNUM_FLAG as VALUE != 0
        }

        fn is_static_symbol(self) -> bool {
            const MASK: usize = !(usize::MAX << ruby_special_consts::RUBY_SPECIAL_SHIFT as usize);
            self.as_rb_value() as usize & MASK == ruby_special_consts::RUBY_SYMBOL_FLAG as usize
        }

        fn is_flonum(self) -> bool {
            self.as_rb_value() & ruby_special_consts::RUBY_FLONUM_MASK as VALUE
                == ruby_special_consts::RUBY_FLONUM_FLAG as VALUE
        }

        // derefs a raw pointer that under GC compaction may be outside the
        // process's memory space if the Value has been allowed to get GC'd
        fn rb_type(self) -> ruby_value_type {
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
                    } else if self.copy_as_value().is_nil() {
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

        /// Convert `self` to a string. If an error is encountered returns a
        /// generic string (usually the object's class name).
        ///
        /// # Safety
        ///
        /// This may return a direct view of memory owned and managed by Ruby. Ruby
        /// may modify or free the memory backing the returned str, the caller must
        /// ensure this does not happen.
        #[allow(clippy::wrong_self_convention)]
        unsafe fn to_s_infallible(&self) -> Cow<str> {
            match self.as_value_ref().to_s() {
                Ok(v) => v,
                Err(_) => Cow::Owned(
                    RString::from_rb_value_unchecked(rb_any_to_s(self.as_rb_value()))
                        .to_string_lossy()
                        .into_owned(),
                ),
            }
        }
    }
}

use private::ReprValue as _;

/// Marker trait for types that have the same representation as [`Value`].
///
/// Types that are `ReprValue` can be safely transmuted to Value.
pub trait ReprValue: private::ReprValue {
    /// Return `self` as a [`Value`].
    fn as_value(self) -> Value {
        // This trait is only ever implemented for things with the same
        // representation as Value
        unsafe { *(&self as *const Self as *const Value) }
    }

    /// Returns whether `self` is Ruby's `nil` value.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, prelude::*, Value};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(eval::<Value>("nil").unwrap().is_nil());
    /// assert!(!eval::<Value>("Object.new").unwrap().is_nil());
    /// assert!(!eval::<Value>("0").unwrap().is_nil());
    /// assert!(!eval::<Value>("[]").unwrap().is_nil());
    /// ```
    fn is_nil(self) -> bool {
        self.as_rb_value() == ruby_special_consts::RUBY_Qnil as VALUE
    }

    /// Checks for equality, delegating to the Ruby method `#==`.
    ///
    /// Ruby optimises this check if `self` and `other` are the same object
    /// or some built-in types, then calling the `#==` method will be skipped.
    ///
    /// Returns `Err` if `#==` raises.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{prelude::*, Integer, RArray};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let a = RArray::from_vec(vec![1, 2, 3]);
    /// let b = RArray::from_vec(vec![1, 2, 3]);
    /// let c = RArray::from_vec(vec![4, 5, 6]);
    /// let d = Integer::from_i64(1);
    /// assert!(a.equal(a).unwrap());
    /// assert!(a.equal(b).unwrap());
    /// assert!(!a.equal(c).unwrap());
    /// assert!(!a.equal(d).unwrap());
    /// ```
    ///
    /// ```
    /// use magnus::{eval, prelude::*, Value};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let (a, b): (Value, Value) = eval!("
    ///     class Example
    ///       def ==(other)
    ///         raise
    ///       end
    ///     end
    ///     [Example.new, Example.new]
    /// ").unwrap();
    ///
    /// assert!(a.equal(b).is_err());
    /// ```
    fn equal<T>(self, other: T) -> Result<bool, Error>
    where
        T: ReprValue,
    {
        unsafe {
            protect(|| Value::new(rb_equal(self.as_rb_value(), other.as_rb_value())))
                .map(Value::to_bool)
        }
    }

    /// Checks for equality, delegating to the Ruby method `#eql?`.
    ///
    /// See [`Value::equal`] for the equivalent of the `#==` method.
    ///
    /// Ruby optimises this check if `self` and `other` are the same object
    /// for some built-in types, then calling the `#==` method will be skipped.
    ///
    /// Returns `Err` if `#eql?` raises.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{prelude::*, Integer, RArray};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let a = RArray::from_vec(vec![1, 2, 3]);
    /// let b = RArray::from_vec(vec![1, 2, 3]);
    /// let c = RArray::from_vec(vec![4, 5, 6]);
    /// let d = Integer::from_i64(1);
    /// assert!(a.eql(a).unwrap());
    /// assert!(a.eql(b).unwrap());
    /// assert!(!a.eql(c).unwrap());
    /// assert!(!a.eql(d).unwrap());
    /// ```
    ///
    /// ```
    /// use magnus::{eval, prelude::*, Value};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let (a, b): (Value, Value) = eval!("
    ///     class Example
    ///       def eql?(other)
    ///         raise
    ///       end
    ///     end
    ///     [Example.new, Example.new]
    /// ").unwrap();
    ///
    /// assert!(a.eql(b).is_err());
    /// ```
    fn eql<T>(self, other: T) -> Result<bool, Error>
    where
        T: ReprValue,
    {
        unsafe {
            protect(|| Value::new(rb_eql(self.as_rb_value(), other.as_rb_value()) as VALUE))
                .map(Value::to_bool)
        }
    }

    /// Returns an integer non-uniquely identifying `self`.
    ///
    /// The return value is not stable between different Ruby processes.
    ///
    /// Ruby guarantees the return value will be in the range of a C `long`,
    /// this is usually equivalent to a `i64`, though will be `i32` on Windows.
    ///
    /// Ruby built-in classes will not error, but it is possible for badly
    /// behaving 3rd party classes (or collections such as `Array` containing
    /// them) to error in this function.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{prelude::*, RString};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(RString::new("test").hash().unwrap()
    ///     .equal(RString::new("test").hash().unwrap())
    ///     .unwrap());
    /// ```
    fn hash(self) -> Result<Integer, Error> {
        unsafe { protect(|| Integer::from_rb_value_unchecked(rb_hash(self.as_rb_value()))) }
    }

    /// Returns the class that `self` is an instance of.
    ///
    /// # Panics
    ///
    /// panics if self is `Qundef`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, prelude::*, Value};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert_eq!(eval::<Value>("true").unwrap().class().inspect(), "TrueClass");
    /// assert_eq!(eval::<Value>("[1,2,3]").unwrap().class().inspect(), "Array");
    /// ```
    fn class(self) -> RClass {
        let handle = Ruby::get_with(self);
        unsafe {
            match self.r_basic() {
                Some(r_basic) => RClass::from_rb_value_unchecked(r_basic.as_ref().klass),
                None => {
                    if self.is_false() {
                        handle.class_false_class()
                    } else if self.is_nil() {
                        handle.class_nil_class()
                    } else if self.is_true() {
                        handle.class_true_class()
                    } else if self.is_undef() {
                        panic!("undef does not have a class")
                    } else if self.is_fixnum() {
                        handle.class_integer()
                    } else if self.is_static_symbol() {
                        handle.class_symbol()
                    } else if self.is_flonum() {
                        handle.class_float()
                    } else {
                        unreachable!()
                    }
                }
            }
        }
    }

    /// Returns whether `self` is 'frozen'.
    ///
    /// Ruby prevents modifying frozen objects.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, prelude::*, Value};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(eval::<Value>(":foo").unwrap().is_frozen());
    /// assert!(eval::<Value>("42").unwrap().is_frozen());
    /// assert!(!eval::<Value>("[]").unwrap().is_frozen());
    /// ```
    fn is_frozen(self) -> bool {
        match self.r_basic() {
            None => true,
            Some(r_basic) => unsafe {
                r_basic.as_ref().flags & ruby_fl_type::RUBY_FL_FREEZE as VALUE != 0
            },
        }
    }

    /// Returns an error if `self` is 'frozen'.
    ///
    /// Useful for checking if an object is frozen in a function that would
    /// modify it.
    ///
    /// # Examples
    /// ```
    /// use magnus::{eval, prelude::*, Error, Value};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// fn mutate(val: Value) -> Result<(), Error> {
    ///     val.check_frozen()?;
    ///
    ///     /// ...
    ///
    ///     Ok(())
    /// }
    ///
    /// assert!(mutate(eval("Object.new").unwrap()).is_ok());
    /// assert!(mutate(eval(":foo").unwrap()).is_err());
    /// ```
    fn check_frozen(self) -> Result<(), Error> {
        if self.is_frozen() {
            Err(Error::new(
                Ruby::get_with(self).exception_frozen_error(),
                format!("can't modify frozen {}", unsafe { self.classname() }),
            ))
        } else {
            Ok(())
        }
    }

    /// Mark `self` as frozen.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, prelude::*, RArray};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = RArray::new();
    /// assert!(!ary.is_frozen());
    /// ary.freeze();
    /// assert!(ary.is_frozen());
    /// ```
    fn freeze(self) {
        unsafe { rb_obj_freeze(self.as_rb_value()) };
    }

    /// Convert `self` to a `bool`, following Ruby's rules of `false` and `nil`
    /// as boolean `false` and everything else boolean `true`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, prelude::*, Value};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(!eval::<Value>("false").unwrap().to_bool());
    /// assert!(!eval::<Value>("nil").unwrap().to_bool());
    ///
    /// assert!(eval::<Value>("true").unwrap().to_bool());
    /// assert!(eval::<Value>("0").unwrap().to_bool());
    /// assert!(eval::<Value>("[]").unwrap().to_bool());
    /// assert!(eval::<Value>(":foo").unwrap().to_bool());
    /// assert!(eval::<Value>("Object.new").unwrap().to_bool());
    /// ```
    fn to_bool(self) -> bool {
        self.as_rb_value() & !(ruby_special_consts::RUBY_Qnil as VALUE) != 0
    }

    /// Call the method named `method` on `self` with `args`.
    ///
    /// Returns `Ok(T)` if the method returns without error and the return
    /// value converts to a `T`, or returns `Err` if the method raises or the
    /// conversion fails.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, prelude::*, RArray};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let values = eval::<RArray>(r#"["foo", 1, :bar]"#).unwrap();
    /// let result: String = values.funcall("join", (" & ",)).unwrap();
    /// assert_eq!(result, "foo & 1 & bar");
    /// ```
    fn funcall<M, A, T>(self, method: M, args: A) -> Result<T, Error>
    where
        M: IntoId,
        A: ArgList,
        T: TryConvert,
    {
        let handle = Ruby::get_with(self);
        let id = method.into_id_with(&handle);
        let args = args.into_arg_list_with(&handle);
        let slice = args.as_ref();
        unsafe {
            protect(|| {
                Value::new(rb_funcallv(
                    self.as_rb_value(),
                    id.as_rb_id(),
                    slice.len() as c_int,
                    slice.as_ptr() as *const VALUE,
                ))
            })
            .and_then(TryConvert::try_convert)
        }
    }

    /// Call the ic method named `method` on `self` with `args`.
    ///
    /// Returns `Ok(T)` if the method returns without error and the return
    /// value converts to a `T`, or returns `Err` if the method raises or the
    /// conversion fails.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, prelude::*, Error, RObject, Symbol};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let object: RObject = eval!(r#"
    ///     class Foo
    ///       def bar
    ///         :bar
    ///       end
    ///
    ///       private
    ///
    ///       def baz
    ///         :baz
    ///       end
    ///     end
    ///
    ///     Foo.new
    /// "#).unwrap();
    ///
    /// let result: Symbol = object.funcall_public("bar", ()).unwrap();
    /// assert_eq!(result.name().unwrap(), "bar");
    ///
    /// let result: Result<Symbol, Error> = object.funcall_public("baz", ());
    /// assert!(result.is_err());
    /// ```
    fn funcall_public<M, A, T>(self, method: M, args: A) -> Result<T, Error>
    where
        M: IntoId,
        A: ArgList,
        T: TryConvert,
    {
        let handle = Ruby::get_with(self);
        let id = method.into_id_with(&handle);
        let args = args.into_arg_list_with(&handle);
        let slice = args.as_ref();
        unsafe {
            protect(|| {
                Value::new(rb_funcallv_public(
                    self.as_rb_value(),
                    id.as_rb_id(),
                    slice.len() as c_int,
                    slice.as_ptr() as *const VALUE,
                ))
            })
            .and_then(TryConvert::try_convert)
        }
    }

    /// If `self` responds to the method named `method`, call it with `args`.
    ///
    /// Returns `Some(Ok(T))` if the method exists and returns without error,
    /// `None` if it does not exist, or `Some(Err)` if an exception was raised.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{prelude::*, Float, Integer, RString};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let val = Float::from_f64(1.23);
    /// let res: Integer = val.check_funcall("to_int", ()).unwrap().unwrap();
    /// assert_eq!(res.to_i64().unwrap(), 1);
    ///
    /// let val = RString::new("1.23");
    /// let res: Option<Result<Integer, _>> = val.check_funcall("to_int", ());
    /// assert!(res.is_none());
    /// ```
    fn check_funcall<M, A, T>(self, method: M, args: A) -> Option<Result<T, Error>>
    where
        M: IntoId,
        A: ArgList,
        T: TryConvert,
    {
        let handle = Ruby::get_with(self);
        let id = method.into_id_with(&handle);
        let args = args.into_arg_list_with(&handle);
        let slice = args.as_ref();
        unsafe {
            let result = protect(|| {
                Value::new(rb_check_funcall(
                    self.as_rb_value(),
                    id.as_rb_id(),
                    slice.len() as c_int,
                    slice.as_ptr() as *const VALUE,
                ))
            });
            match result {
                Ok(v) if v.is_undef() => None,
                Ok(v) => Some(T::try_convert(v)),
                Err(e) => Some(Err(e)),
            }
        }
    }

    /// Call the method named `method` on `self` with `args` and `block`.
    ///
    /// Similar to [`funcall`](Value::funcall), but passes `block` as a Ruby
    /// block to the method.
    ///
    /// See also [`block_call`](Value::block_call).
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, block::Proc, prelude::*, RArray, Value};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let values = eval::<RArray>(r#"["foo", 1, :bar]"#).unwrap();
    /// let block = Proc::new(|args, _block| args.first().unwrap().to_r_string());
    /// let _: Value = values.funcall_with_block("map!", (), block).unwrap();
    /// assert_eq!(values.to_vec::<String>().unwrap(), vec!["foo", "1", "bar"]);
    /// ```
    fn funcall_with_block<M, A, T>(self, method: M, args: A, block: Proc) -> Result<T, Error>
    where
        M: IntoId,
        A: ArgList,
        T: TryConvert,
    {
        let handle = Ruby::get_with(self);
        let id = method.into_id_with(&handle);
        let args = args.into_arg_list_with(&handle);
        let slice = args.as_ref();
        unsafe {
            protect(|| {
                Value::new(rb_funcall_with_block(
                    self.as_rb_value(),
                    id.as_rb_id(),
                    slice.len() as c_int,
                    slice.as_ptr() as *const VALUE,
                    block.as_rb_value(),
                ))
            })
            .and_then(TryConvert::try_convert)
        }
    }

    /// Call the method named `method` on `self` with `args` and `block`.
    ///
    /// Similar to [`funcall`](Value::funcall), but passes `block` as a Ruby
    /// block to the method.
    ///
    /// As `block` is a function pointer, only functions and closures that do
    /// not capture any variables are permitted. For more flexibility (at the
    /// cost of allocating) see [`Proc::from_fn`] and
    /// [`funcall_with_block`](Value::funcall_with_block).
    ///
    /// The function passed as `block` will receive values yielded to the block
    /// as a slice of [`Value`]s, plus `Some(Proc)` if the block itself was
    /// called with a block, or `None` otherwise.
    ///
    /// The `block` function may return any `R` or `Result<R, Error>` where `R`
    /// implements [`IntoValue`]. Returning `Err(Error)` will raise the error
    /// as a Ruby exception.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, prelude::*, RArray, Value};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let values = eval::<RArray>(r#"["foo", 1, :bar]"#).unwrap();
    /// let _: Value = values.block_call("map!", (), |args, _block| args.first().unwrap().to_r_string()).unwrap();
    /// assert_eq!(values.to_vec::<String>().unwrap(), vec!["foo", "1", "bar"]);
    /// ```
    fn block_call<M, A, R, T>(
        self,
        method: M,
        args: A,
        block: fn(&[Value], Option<Proc>) -> R,
    ) -> Result<T, Error>
    where
        M: IntoId,
        A: ArgList,
        R: BlockReturn,
        T: TryConvert,
    {
        unsafe extern "C" fn call<R>(
            _yielded_arg: VALUE,
            callback_arg: VALUE,
            argc: c_int,
            argv: *const VALUE,
            blockarg: VALUE,
        ) -> VALUE
        where
            R: BlockReturn,
        {
            let func = std::mem::transmute::<VALUE, fn(&[Value], Option<Proc>) -> R>(callback_arg);
            func.call_handle_error(argc, argv as *const Value, Value::new(blockarg))
                .as_rb_value()
        }

        let handle = Ruby::get_with(self);
        let id = method.into_id_with(&handle);
        let args = args.into_arg_list_with(&handle);
        let slice = args.as_ref();
        let call_func =
            call::<R> as unsafe extern "C" fn(VALUE, VALUE, c_int, *const VALUE, VALUE) -> VALUE;
        #[cfg(ruby_lt_2_7)]
        let call_func: unsafe extern "C" fn() -> VALUE = unsafe { std::mem::transmute(call_func) };

        protect(|| unsafe {
            #[allow(clippy::fn_to_numeric_cast)]
            Value::new(rb_block_call(
                self.as_rb_value(),
                id.as_rb_id(),
                slice.len() as c_int,
                slice.as_ptr() as *const VALUE,
                Some(call_func),
                block as VALUE,
            ))
        })
        .and_then(TryConvert::try_convert)
    }

    /// Check if `self` responds to the given Ruby method.
    ///
    /// The `include_private` agument controls whether `self`'s private methods
    /// are checked. If `false` they are not, if `true` they are.
    ///
    /// See also [`Value::check_funcall`].
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{prelude::*, RString};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let s = RString::new("example");
    /// assert!(s.respond_to("to_str", false).unwrap());
    /// assert!(!s.respond_to("puts", false).unwrap());
    /// assert!(s.respond_to("puts", true).unwrap());
    /// assert!(!s.respond_to("non_existant", false).unwrap());
    /// assert!(!s.respond_to("non_existant", true).unwrap());
    /// ```
    fn respond_to<M>(self, method: M, include_private: bool) -> Result<bool, Error>
    where
        M: IntoId,
    {
        let handle = Ruby::get_with(self);
        let id = method.into_id_with(&handle);
        let mut res = false;
        protect(|| {
            unsafe {
                res = rb_obj_respond_to(self.as_rb_value(), id.as_rb_id(), include_private as c_int)
                    != 0
            };
            handle.qnil()
        })?;
        Ok(res)
    }

    /// Convert `self` to a Ruby `String`.
    ///
    /// If `self` is already a `String` is it wrapped as a `RString`, otherwise
    /// the Ruby `to_s` method is called.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, class, prelude::*, Value};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let value = eval::<Value>("[]").unwrap();
    /// assert!(value.to_r_string().unwrap().is_kind_of(class::string()));
    /// ```
    fn to_r_string(self) -> Result<RString, Error> {
        match RString::from_value(self.as_value()) {
            Some(v) => Ok(v),
            None => protect(|| unsafe {
                RString::from_rb_value_unchecked(rb_obj_as_string(self.as_rb_value()))
            }),
        }
    }

    /// Convert `self` to a Rust string.
    ///
    /// # Safety
    ///
    /// This may return a direct view of memory owned and managed by Ruby. Ruby
    /// may modify or free the memory backing the returned str, the caller must
    /// ensure this does not happen.
    ///
    /// This can be used safely by immediately calling
    /// [`into_owned`](Cow::into_owned) on the return value.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, prelude::*, IntoValue, QTRUE};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let value = QTRUE.into_value();
    /// // safe as we never give Ruby a chance to free the string.
    /// let s = unsafe { value.to_s() }.unwrap().into_owned();
    /// assert_eq!(s, "true");
    /// ```
    #[allow(clippy::wrong_self_convention)]
    unsafe fn to_s(&self) -> Result<Cow<str>, Error> {
        if let Some(s) = RString::ref_from_value(self.as_value_ref()) {
            if s.is_utf8_compatible_encoding() {
                return s.as_str().map(Cow::Borrowed);
            } else {
                return (*s).to_string().map(Cow::Owned);
            }
        }
        self.to_r_string()
            .and_then(|s| s.to_string().map(Cow::Owned))
    }

    /// Convert `self` to its Ruby debug representation.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, prelude::*, IntoValue, Symbol, QNIL};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert_eq!(QNIL.into_value().inspect(), "nil");
    /// assert_eq!(Symbol::new("foo").inspect(), ":foo");
    /// ```
    fn inspect(self) -> String {
        let handle = Ruby::get_with(self);
        unsafe {
            let s = protect(|| RString::from_rb_value_unchecked(rb_inspect(self.as_rb_value())))
                .unwrap_or_else(|_| {
                    RString::from_rb_value_unchecked(rb_any_to_s(self.as_rb_value()))
                });
            s.conv_enc(handle.utf8_encoding())
                .unwrap_or(s)
                .to_string_lossy()
                .into_owned()
        }
    }

    /// Return the name of `self`'s class.
    ///
    /// # Safety
    ///
    /// Ruby may modify or free the memory backing the returned str, the caller
    /// must ensure this does not happen.
    ///
    /// This can be used safely by immediately calling
    /// [`into_owned`](Cow::into_owned) on the return value.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, prelude::*, RHash};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let value = RHash::new();
    /// // safe as we never give Ruby a chance to free the string.
    /// let s = unsafe { value.classname() }.into_owned();
    /// assert_eq!(s, "Hash");
    /// ```
    unsafe fn classname(&self) -> Cow<str> {
        let ptr = rb_obj_classname(self.as_rb_value());
        let cstr = CStr::from_ptr(ptr);
        cstr.to_string_lossy()
    }

    /// Returns whether or not `self` is an instance of `class`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{class, eval, prelude::*, Value};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let value = eval::<Value>("[]").unwrap();
    /// assert!(value.is_kind_of(class::array()));
    /// ```
    fn is_kind_of<T>(self, class: T) -> bool
    where
        T: ReprValue + Module,
    {
        unsafe { Value::new(rb_obj_is_kind_of(self.as_rb_value(), class.as_rb_value())).to_bool() }
    }

    /// Generate an [`Enumerator`] from `method` on `self`, passing `args` to
    /// `method`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{class, eval, prelude::*, r_string};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let s = r_string!("foo\\bar\\baz");
    /// let mut i = 0;
    /// for line in s.enumeratorize("each_line", ("\\",)) {
    ///     assert!(line.unwrap().is_kind_of(class::string()));
    ///     i += 1;
    /// }
    /// assert_eq!(i, 3);
    /// ```
    fn enumeratorize<M, A>(self, method: M, args: A) -> Enumerator
    where
        M: IntoSymbol,
        A: ArgList,
    {
        let handle = Ruby::get_with(self);
        let args = args.into_arg_list_with(&handle);
        let slice = args.as_ref();
        unsafe {
            Enumerator::from_rb_value_unchecked(rb_enumeratorize_with_size(
                self.as_rb_value(),
                method.into_symbol_with(&handle).as_rb_value(),
                slice.len() as c_int,
                slice.as_ptr() as *const VALUE,
                None,
            ))
        }
    }
}

unsafe impl private::ReprValue for Value {}

impl ReprValue for Value {}

#[derive(Clone, Copy, Eq, Hash, PartialEq)]
#[repr(transparent)]
pub(crate) struct NonZeroValue(NonZeroUsize, PhantomData<ptr::NonNull<RBasic>>);

impl NonZeroValue {
    #[inline]
    pub(crate) const unsafe fn new_unchecked(val: Value) -> Self {
        Self(
            NonZeroUsize::new_unchecked(val.as_rb_value() as usize),
            PhantomData,
        )
    }

    pub(crate) const fn get(self) -> Value {
        Value::new(self.0.get() as VALUE)
    }
}

/// Protects a Ruby Value from the garbage collector.
///
/// See also [`gc::register_mark_object`](crate::gc::register_mark_object) for
/// a value that should be permanently excluded from garbage collection.
pub struct BoxValue<T>(Box<T>);

impl<T> BoxValue<T>
where
    T: ReprValue,
{
    /// Create a new `BoxValue`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, gc, value::BoxValue, RString, Value};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// # #[inline(never)]
    /// fn box_value() -> BoxValue<RString> {
    ///     BoxValue::new(RString::new("foo"))
    /// }
    ///
    /// # // get the Value in a different stack frame and copy it to a BoxValue
    /// # // test is invalid if this is done in this function.
    /// let boxed = box_value();
    ///
    /// # // make some garbage
    /// # eval::<Value>(r#"1024.times.map {|i| "test#{i}"}"#).unwrap();
    /// // run garbage collector
    /// gc::start();
    ///
    /// # // try and use value
    /// // boxed is still useable
    /// let result: String = eval!(r#"foo + "bar""#, foo = boxed).unwrap();
    ///
    /// assert_eq!(result, "foobar");
    ///
    /// # // didn't segfault? we passed!
    /// ```
    pub fn new(val: T) -> Self {
        let mut boxed = Box::new(val);
        unsafe { rb_gc_register_address(boxed.as_mut() as *mut _ as *mut VALUE) };
        Self(boxed)
    }
}

impl<T> Drop for BoxValue<T> {
    fn drop(&mut self) {
        unsafe {
            rb_gc_unregister_address(self.0.as_mut() as *mut _ as *mut VALUE);
        }
    }
}

impl<T> AsRef<T> for BoxValue<T> {
    fn as_ref(&self) -> &T {
        &self.0
    }
}

impl<T> AsMut<T> for BoxValue<T> {
    fn as_mut(&mut self) -> &mut T {
        &mut self.0
    }
}

impl<T> Deref for BoxValue<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> DerefMut for BoxValue<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T> fmt::Display for BoxValue<T>
where
    T: ReprValue,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.as_value().to_s_infallible() })
    }
}

impl<T> fmt::Debug for BoxValue<T>
where
    T: ReprValue,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_value().inspect())
    }
}

impl<T> IntoValue for BoxValue<T>
where
    T: ReprValue,
{
    fn into_value_with(self, _: &Ruby) -> Value {
        self.as_value()
    }
}

unsafe impl<T> IntoValueFromNative for BoxValue<T> where T: ReprValue {}

#[allow(missing_docs)]
impl Ruby {
    #[inline]
    pub fn qfalse(&self) -> Qfalse {
        self.unwrap_opaque(QFALSE)
    }
}

/// Ruby's `false` value.
///
/// See [`QFALSE`] to obtain a value of this type.
///
/// See the [`ReprValue`] trait for additional methods available on this type.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Qfalse(Value);

/// Ruby's `false` value.
pub const QFALSE: Opaque<Qfalse> = Opaque(Qfalse::new());

impl Qfalse {
    /// Create a new `Qfalse`.
    #[inline]
    const fn new() -> Self {
        Qfalse(Value::new(ruby_special_consts::RUBY_Qfalse as VALUE))
    }

    /// Return `Some(Qfalse)` if `val` is a `Qfalse`, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, value::Qfalse};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(Qfalse::from_value(eval("false").unwrap()).is_some());
    /// assert!(Qfalse::from_value(eval("0").unwrap()).is_none());
    /// ```
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        val.is_false().then(Self::new)
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

impl IntoValue for Qfalse {
    fn into_value_with(self, _: &Ruby) -> Value {
        self.0
    }
}

unsafe impl private::ReprValue for Qfalse {}

impl ReprValue for Qfalse {}

impl TryConvert for Qfalse {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Self::from_value(val).ok_or_else(|| {
            Error::new(
                Ruby::get_with(val).exception_type_error(),
                format!("no implicit conversion of {} into FalseClass", unsafe {
                    val.classname()
                },),
            )
        })
    }
}
impl TryConvertOwned for Qfalse {}

#[allow(missing_docs)]
impl Ruby {
    #[inline]
    pub fn qnil(&self) -> Qnil {
        self.unwrap_opaque(QNIL)
    }
}

/// Ruby's `nil` value.
///
/// See [`QNIL`] to obtain a value of this type.
///
/// See the [`ReprValue`] trait for additional methods available on this type.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Qnil(NonZeroValue);

/// Ruby's `nil` value.
pub const QNIL: Opaque<Qnil> = Opaque(Qnil::new());

impl Qnil {
    /// Create a new `Qnil`.
    #[inline]
    const fn new() -> Self {
        unsafe {
            Self(NonZeroValue::new_unchecked(Value::new(
                ruby_special_consts::RUBY_Qnil as VALUE,
            )))
        }
    }

    /// Return `Some(Qnil)` if `val` is a `Qnil`, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, value::Qnil};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(Qnil::from_value(eval("nil").unwrap()).is_some());
    /// assert!(Qnil::from_value(eval("0").unwrap()).is_none());
    /// ```
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        val.is_nil().then(Self::new)
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

impl IntoValue for Qnil {
    fn into_value_with(self, _: &Ruby) -> Value {
        self.0.get()
    }
}

impl IntoValue for () {
    fn into_value_with(self, handle: &Ruby) -> Value {
        handle.qnil().as_value()
    }
}

unsafe impl IntoValueFromNative for () {}

impl<T> IntoValue for Option<T>
where
    T: IntoValue,
{
    fn into_value_with(self, handle: &Ruby) -> Value {
        match self {
            Some(t) => handle.into_value(t),
            None => handle.qnil().as_value(),
        }
    }
}

unsafe impl<T> IntoValueFromNative for Option<T> where T: IntoValueFromNative {}

unsafe impl private::ReprValue for Qnil {}

impl ReprValue for Qnil {}

impl TryConvert for Qnil {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Self::from_value(val).ok_or_else(|| {
            Error::new(
                Ruby::get_with(val).exception_type_error(),
                format!("no implicit conversion of {} into NilClass", unsafe {
                    val.classname()
                },),
            )
        })
    }
}
impl TryConvertOwned for Qnil {}

#[allow(missing_docs)]
impl Ruby {
    #[inline]
    pub fn qtrue(&self) -> Qtrue {
        self.unwrap_opaque(QTRUE)
    }
}

/// Ruby's `true` value.
///
/// See [`QTRUE`] to obtain a value of this type.
///
/// See the [`ReprValue`] trait for additional methods available on this type.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Qtrue(NonZeroValue);

/// Ruby's `true` value.
pub const QTRUE: Opaque<Qtrue> = Opaque(Qtrue::new());

impl Qtrue {
    /// Create a new `Qtrue`.
    #[inline]
    const fn new() -> Self {
        unsafe {
            Self(NonZeroValue::new_unchecked(Value::new(
                ruby_special_consts::RUBY_Qtrue as VALUE,
            )))
        }
    }

    /// Return `Some(Qtrue)` if `val` is a `Qtrue`, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, value::Qtrue};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(Qtrue::from_value(eval("true").unwrap()).is_some());
    /// assert!(Qtrue::from_value(eval("1").unwrap()).is_none());
    /// ```
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        val.is_true().then(Self::new)
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

impl IntoValue for Qtrue {
    fn into_value_with(self, _: &Ruby) -> Value {
        self.0.get()
    }
}

impl IntoValue for bool {
    fn into_value_with(self, handle: &Ruby) -> Value {
        if self {
            QTRUE.into_value_with(handle)
        } else {
            QFALSE.into_value_with(handle)
        }
    }
}

unsafe impl IntoValueFromNative for bool {}

unsafe impl private::ReprValue for Qtrue {}

impl ReprValue for Qtrue {}

impl TryConvert for Qtrue {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Self::from_value(val).ok_or_else(|| {
            Error::new(
                Ruby::get_with(val).exception_type_error(),
                format!("no implicit conversion of {} into TrueClass", unsafe {
                    val.classname()
                },),
            )
        })
    }
}
impl TryConvertOwned for Qtrue {}

/// A placeholder value that represents an undefined value. Not exposed to
/// Ruby level code.
///
/// See [`QUNDEF`] to obtain a value of this type.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Qundef(NonZeroValue);

/// A placeholder value that represents an undefined value. Not exposed to
/// Ruby level code.
pub const QUNDEF: Qundef = Qundef::new();

impl Qundef {
    /// Create a new `Qundef`.
    #[inline]
    const fn new() -> Self {
        unsafe {
            Self(NonZeroValue::new_unchecked(Value::new(
                ruby_special_consts::RUBY_Qundef as VALUE,
            )))
        }
    }

    /// Return `Some(Qundef)` if `val` is a `Qundef`, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, value::Qundef};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// // nil is not undef
    /// assert!(Qundef::from_value(eval("nil").unwrap()).is_none());
    /// ```
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        val.is_undef().then(Self::new)
    }

    /// Return `self` as a [`Value`].
    ///
    /// # Safety
    ///
    /// It is not a good idea to return this to Ruby code, bad things will
    /// happen. There are only a handful of places in Ruby's API where it is
    /// appropriate to pass a [`Value`] created from `Qundef` (hence this
    /// method, rather than implementing [`IntoValue`]).
    #[inline]
    pub unsafe fn as_value(self) -> Value {
        self.0.get()
    }

    #[doc(hidden)]
    #[deprecated(since = "0.6.0", note = "please use `as_value` instead")]
    pub unsafe fn to_value(self) -> Value {
        self.as_value()
    }
}

#[allow(missing_docs)]
impl Ruby {
    #[inline]
    pub fn fixnum_from_i64(&self, n: i64) -> Result<Fixnum, RBignum> {
        Fixnum::from_i64_impl(n)
            .ok_or_else(|| unsafe { RBignum::from_rb_value_unchecked(rb_ll2inum(n)) })
    }

    #[inline]
    pub fn fixnum_from_u64(&self, n: u64) -> Result<Fixnum, RBignum> {
        Fixnum::from_i64_impl(i64::try_from(n).unwrap_or(i64::MAX))
            .ok_or_else(|| unsafe { RBignum::from_rb_value_unchecked(rb_ull2inum(n)) })
    }
}

/// A Value known to be a fixnum, Ruby's internal representation of small
/// integers.
///
/// See also [`Integer`].
///
/// See the [`ReprValue`] trait for additional methods available on this type.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Fixnum(NonZeroValue);

impl Fixnum {
    /// Return `Some(Fixnum)` if `val` is a `Fixnum`, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Fixnum};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(Fixnum::from_value(eval("0").unwrap()).is_some());
    /// // too big
    /// assert!(Fixnum::from_value(eval("9223372036854775807").unwrap()).is_none());
    /// // not an int
    /// assert!(Fixnum::from_value(eval("1.23").unwrap()).is_none());
    /// ```
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

    #[inline]
    pub(crate) fn from_i64_impl(n: i64) -> Option<Self> {
        #[allow(clippy::useless_conversion)] // not useless when c_long != i64
        (c_ulong::try_from(n)
            .map(|n| n < RUBY_FIXNUM_MAX + 1)
            .unwrap_or(false)
            && c_long::try_from(n)
                .map(|n| n >= RUBY_FIXNUM_MIN)
                .unwrap_or(false))
        .then(|| unsafe {
            let x = transmute::<_, usize>(n as isize);
            Self::from_rb_value_unchecked(x.wrapping_add(x.wrapping_add(1)) as VALUE)
        })
    }

    /// Create a new `Fixnum` from an `i64.`
    ///
    /// Returns `Ok(Fixnum)` if `n` is in range for `Fixnum`, otherwise returns
    /// `Err(RBignum)`.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Fixnum};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(Fixnum::from_i64(0).is_ok());
    /// // too big
    /// assert!(Fixnum::from_i64(4611686018427387904).is_err());
    /// assert!(Fixnum::from_i64(-4611686018427387905).is_err());
    /// ```
    #[cfg(feature = "friendly-api")]
    #[inline]
    pub fn from_i64(n: i64) -> Result<Self, RBignum> {
        get_ruby!().fixnum_from_i64(n)
    }

    /// Create a new `Fixnum` from a `u64.`
    ///
    /// Returns `Ok(Fixnum)` if `n` is in range for `Fixnum`, otherwise returns
    /// `Err(RBignum)`.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Fixnum};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(Fixnum::from_u64(0).is_ok());
    /// // too big
    /// assert!(Fixnum::from_u64(4611686018427387904).is_err());
    /// ```
    #[cfg(feature = "friendly-api")]
    #[inline]
    pub fn from_u64(n: u64) -> Result<Self, RBignum> {
        get_ruby!().fixnum_from_u64(n)
    }

    fn is_negative(self) -> bool {
        unsafe { transmute::<_, isize>(self.0) < 0 }
    }

    /// Convert `self` to an `i8`. Returns `Err` if `self` is out of range for
    /// `i8`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Fixnum};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert_eq!(eval::<Fixnum>("127").unwrap().to_i8().unwrap(), 127);
    /// assert!(eval::<Fixnum>("128").unwrap().to_i8().is_err());
    /// assert_eq!(eval::<Fixnum>("-128").unwrap().to_i8().unwrap(), -128);
    /// assert!(eval::<Fixnum>("-129").unwrap().to_i8().is_err());
    /// ```
    #[inline]
    pub fn to_i8(self) -> Result<i8, Error> {
        let res = self.to_isize();
        if res > i8::MAX as isize || res < i8::MIN as isize {
            return Err(Error::new(
                Ruby::get_with(self).exception_range_error(),
                "fixnum too big to convert into `i8`",
            ));
        }
        Ok(res as i8)
    }

    /// Convert `self` to an `i16`. Returns `Err` if `self` is out of range for
    /// `i16`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Fixnum};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert_eq!(eval::<Fixnum>("32767").unwrap().to_i16().unwrap(), 32767);
    /// assert!(eval::<Fixnum>("32768").unwrap().to_i16().is_err());
    /// assert_eq!(eval::<Fixnum>("-32768").unwrap().to_i16().unwrap(), -32768);
    /// assert!(eval::<Fixnum>("-32769").unwrap().to_i16().is_err());
    /// ```
    #[inline]
    pub fn to_i16(self) -> Result<i16, Error> {
        let res = self.to_isize();
        if res > i16::MAX as isize || res < i16::MIN as isize {
            return Err(Error::new(
                Ruby::get_with(self).exception_range_error(),
                "fixnum too big to convert into `i16`",
            ));
        }
        Ok(res as i16)
    }

    /// Convert `self` to an `i32`. Returns `Err` if `self` is out of range for
    /// `i32`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Fixnum};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// # #[cfg(not(windows))]
    /// # {
    /// assert_eq!(eval::<Fixnum>("2147483647").unwrap().to_i32().unwrap(), 2147483647);
    /// assert!(eval::<Fixnum>("2147483648").unwrap().to_i32().is_err());
    /// assert_eq!(eval::<Fixnum>("-2147483648").unwrap().to_i32().unwrap(), -2147483648);
    /// assert!(eval::<Fixnum>("-2147483649").unwrap().to_i32().is_err());
    /// # }
    /// ```
    #[inline]
    pub fn to_i32(self) -> Result<i32, Error> {
        let res = self.to_isize();
        if res > i32::MAX as isize || res < i32::MIN as isize {
            return Err(Error::new(
                Ruby::get_with(self).exception_range_error(),
                "fixnum too big to convert into `i32`",
            ));
        }
        Ok(res as i32)
    }

    /// Convert `self` to an `i64`. This is infallible as `i64` can represent a
    /// larger range than `Fixnum`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Fixnum};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// # #[cfg(not(windows))]
    /// assert_eq!(eval::<Fixnum>("4611686018427387903").unwrap().to_i64(), 4611686018427387903);
    /// # #[cfg(not(windows))]
    /// assert_eq!(eval::<Fixnum>("-4611686018427387904").unwrap().to_i64(), -4611686018427387904);
    /// ```
    #[inline]
    pub fn to_i64(self) -> i64 {
        self.to_isize() as i64
    }

    /// Convert `self` to an `isize`. Returns `Err` if `self` is out of range
    /// for `isize`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Fixnum};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// # #[cfg(not(windows))]
    /// assert_eq!(eval::<Fixnum>("4611686018427387903").unwrap().to_isize(), 4611686018427387903);
    /// # #[cfg(not(windows))]
    /// assert_eq!(eval::<Fixnum>("-4611686018427387904").unwrap().to_isize(), -4611686018427387904);
    /// ```
    #[inline]
    pub fn to_isize(self) -> isize {
        unsafe { transmute::<_, isize>(self) >> 1 }
    }

    /// Convert `self` to a `u8`. Returns `Err` if `self` is negative or out of
    /// range for `u8`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Fixnum};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert_eq!(eval::<Fixnum>("255").unwrap().to_u8().unwrap(), 255);
    /// assert!(eval::<Fixnum>("256").unwrap().to_u8().is_err());
    /// assert!(eval::<Fixnum>("-1").unwrap().to_u8().is_err());
    /// ```
    #[inline]
    pub fn to_u8(self) -> Result<u8, Error> {
        let handle = Ruby::get_with(self);
        if self.is_negative() {
            return Err(Error::new(
                handle.exception_range_error(),
                "can't convert negative integer to unsigned",
            ));
        }
        let res = self.to_isize();
        if res > u8::MAX as isize {
            return Err(Error::new(
                handle.exception_range_error(),
                "fixnum too big to convert into `u8`",
            ));
        }
        Ok(res as u8)
    }

    /// Convert `self` to a `u16`. Returns `Err` if `self` is negative or out
    /// of range for `u16`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Fixnum};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert_eq!(eval::<Fixnum>("65535").unwrap().to_u16().unwrap(), 65535);
    /// assert!(eval::<Fixnum>("65536").unwrap().to_u16().is_err());
    /// assert!(eval::<Fixnum>("-1").unwrap().to_u16().is_err());
    /// ```
    #[inline]
    pub fn to_u16(self) -> Result<u16, Error> {
        let handle = Ruby::get_with(self);
        if self.is_negative() {
            return Err(Error::new(
                handle.exception_range_error(),
                "can't convert negative integer to unsigned",
            ));
        }
        let res = self.to_isize();
        if res > u16::MAX as isize {
            return Err(Error::new(
                handle.exception_range_error(),
                "fixnum too big to convert into `u16`",
            ));
        }
        Ok(res as u16)
    }

    /// Convert `self` to a `u32`. Returns `Err` if `self` is negative or out
    /// of range for `u32`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Fixnum};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// # #[cfg(not(windows))]
    /// # {
    /// assert_eq!(eval::<Fixnum>("4294967295").unwrap().to_u32().unwrap(), 4294967295);
    /// assert!(eval::<Fixnum>("4294967296").unwrap().to_u32().is_err());
    /// # }
    /// assert!(eval::<Fixnum>("-1").unwrap().to_u32().is_err());
    /// ```
    #[inline]
    pub fn to_u32(self) -> Result<u32, Error> {
        let handle = Ruby::get_with(self);
        if self.is_negative() {
            return Err(Error::new(
                handle.exception_range_error(),
                "can't convert negative integer to unsigned",
            ));
        }
        let res = self.to_isize();
        if res > u32::MAX as isize {
            return Err(Error::new(
                handle.exception_range_error(),
                "fixnum too big to convert into `u32`",
            ));
        }
        Ok(res as u32)
    }

    /// Convert `self` to a `u64`. Returns `Err` if `self` is negative.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Fixnum};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// # #[cfg(not(windows))]
    /// assert_eq!(eval::<Fixnum>("4611686018427387903").unwrap().to_u64().unwrap(), 4611686018427387903);
    /// assert!(eval::<Fixnum>("-1").unwrap().to_u64().is_err());
    /// ```
    #[inline]
    pub fn to_u64(self) -> Result<u64, Error> {
        if self.is_negative() {
            return Err(Error::new(
                Ruby::get_with(self).exception_range_error(),
                "can't convert negative integer to unsigned",
            ));
        }
        Ok(self.to_isize() as u64)
    }

    /// Convert `self` to a `usize`. Returns `Err` if `self` is negative or out
    /// of range for `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Fixnum};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// # #[cfg(not(windows))]
    /// assert_eq!(eval::<Fixnum>("4611686018427387903").unwrap().to_usize().unwrap(), 4611686018427387903);
    /// assert!(eval::<Fixnum>("-1").unwrap().to_usize().is_err());
    /// ```
    #[inline]
    pub fn to_usize(self) -> Result<usize, Error> {
        if self.is_negative() {
            return Err(Error::new(
                Ruby::get_with(self).exception_range_error(),
                "can't convert negative integer to unsigned",
            ));
        }
        Ok(self.to_isize() as usize)
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

impl IntoValue for Fixnum {
    fn into_value_with(self, _: &Ruby) -> Value {
        self.0.get()
    }
}

unsafe impl private::ReprValue for Fixnum {}

impl Numeric for Fixnum {}

impl ReprValue for Fixnum {}

impl TryConvert for Fixnum {
    fn try_convert(val: Value) -> Result<Self, Error> {
        match Integer::try_convert(val)?.integer_type() {
            IntegerType::Fixnum(fix) => Ok(fix),
            IntegerType::Bignum(_) => Err(Error::new(
                Ruby::get_with(val).exception_range_error(),
                "integer too big for fixnum",
            )),
        }
    }
}
impl TryConvertOwned for Fixnum {}

#[allow(missing_docs)]
impl Ruby {
    #[inline]
    pub fn sym_new<T>(&self, name: T) -> StaticSymbol
    where
        T: IntoId,
    {
        name.into_id_with(self).into()
    }

    pub fn check_symbol(&self, name: &str) -> Option<StaticSymbol> {
        unsafe {
            let res = Value::new(rb_check_symbol_cstr(
                name.as_ptr() as *mut c_char,
                name.len() as c_long,
                self.utf8_encoding().as_ptr(),
            ));
            (!res.is_nil()).then(|| StaticSymbol::from_rb_value_unchecked(res.as_rb_value()))
        }
    }
}

/// A static Ruby symbol that will live for the life of the program and never
/// be garbage collected.
///
/// See also [`Symbol`].
///
/// See the [`ReprValue`] trait for additional methods available on this type.
#[derive(Clone, Copy, Eq, Hash, PartialEq)]
#[repr(transparent)]
pub struct StaticSymbol(NonZeroValue);

impl StaticSymbol {
    /// Return `Some(StaticSymbol)` if `val` is a `StaticSymbol`, `None`
    /// otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, StaticSymbol};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(StaticSymbol::from_value(eval(":foo").unwrap()).is_some());
    /// assert!(StaticSymbol::from_value(eval(r#""bar""#).unwrap()).is_none());
    /// assert!(StaticSymbol::from_value(eval(r#""baz".to_sym"#).unwrap()).is_none());
    /// ```
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        fn is_static_or_permanent_symbol(val: Value) -> bool {
            if val.is_static_symbol() {
                return true;
            }
            debug_assert_value!(val);
            if val.rb_type() != ruby_value_type::RUBY_T_SYMBOL {
                return false;
            }
            let mut p = val.as_rb_value();
            unsafe { rb_check_id(&mut p as *mut _) != 0 }
        }
        unsafe {
            is_static_or_permanent_symbol(val).then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        Self(NonZeroValue::new_unchecked(Value::new(val)))
    }

    /// Create a new StaticSymbol.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread.
    ///
    /// # Examples
    /// ```
    /// use magnus::{eval, StaticSymbol};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let sym = StaticSymbol::new("example");
    /// let result: bool = eval!(":example == sym", sym).unwrap();
    /// assert!(result);
    /// ```
    #[cfg(feature = "friendly-api")]
    #[inline]
    pub fn new<T>(name: T) -> Self
    where
        T: IntoId,
    {
        get_ruby!().sym_new(name)
    }

    /// Return the `Id` for `name`, if one exists.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, StaticSymbol};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(StaticSymbol::check("example").is_none());
    /// eval::<StaticSymbol>(":example").unwrap();
    /// assert!(StaticSymbol::check("example").is_some());
    /// ```
    #[cfg(feature = "friendly-api")]
    #[inline]
    pub fn check(name: &str) -> Option<Self> {
        get_ruby!().check_symbol(name)
    }

    /// Return the symbol as a static string reference.
    ///
    /// May error if the name is not valid utf-8.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::StaticSymbol;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let sym = StaticSymbol::new("example");
    /// assert_eq!(sym.name().unwrap(), "example");
    /// ```
    pub fn name(self) -> Result<&'static str, Error> {
        Id::from(self).name()
    }
}

impl Borrow<Symbol> for StaticSymbol {
    fn borrow(&self) -> &Symbol {
        unsafe { &*(self as *const Self as *const Symbol) }
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

impl EncodingCapable for StaticSymbol {}

impl From<Id> for StaticSymbol {
    fn from(id: Id) -> Self {
        unsafe { Self::from_rb_value_unchecked(rb_id2sym(id.as_rb_id())) }
    }
}

impl IntoValue for StaticSymbol {
    fn into_value_with(self, _: &Ruby) -> Value {
        self.0.get()
    }
}

impl PartialEq<Id> for StaticSymbol {
    fn eq(&self, other: &Id) -> bool {
        self.into_id_with(&Ruby::get_with(*self)) == *other
    }
}

impl PartialEq<OpaqueId> for StaticSymbol {
    fn eq(&self, other: &OpaqueId) -> bool {
        OpaqueId::from(*self) == *other
    }
}

impl PartialEq<LazyId> for StaticSymbol {
    /// # Panics
    ///
    /// Panics if the first call is from a non-Ruby thread. The `LazyId` will
    /// then be *poisoned* and all future use of it will panic.
    fn eq(&self, other: &LazyId) -> bool {
        OpaqueId::from(*self) == *other
    }
}

impl PartialEq<Symbol> for StaticSymbol {
    fn eq(&self, other: &Symbol) -> bool {
        other.as_static().map(|o| *self == o).unwrap_or(false)
    }
}

unsafe impl private::ReprValue for StaticSymbol {}

impl ReprValue for StaticSymbol {}

impl TryConvert for StaticSymbol {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Symbol::try_convert(val).map(|s| s.to_static())
    }
}
impl TryConvertOwned for StaticSymbol {}

#[allow(missing_docs)]
impl Ruby {
    pub fn intern(&self, name: &str) -> Id {
        Id::from_rb_id(unsafe {
            rb_intern3(
                name.as_ptr() as *const c_char,
                name.len() as c_long,
                self.utf8_encoding().as_ptr(),
            )
        })
    }

    pub fn check_id(&self, name: &str) -> Option<Id> {
        let res = unsafe {
            rb_check_id_cstr(
                name.as_ptr() as *mut c_char,
                name.len() as c_long,
                self.utf8_encoding().as_ptr(),
            )
        };
        (res != 0).then(|| Id::from_rb_id(res))
    }
}

/// The internal value of a Ruby symbol.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[repr(transparent)]
pub struct Id(ID, PhantomData<*mut u8>);

impl Id {
    /// Create a new `Id` for `name`.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::value::Id;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let id = Id::new("example");
    /// assert_eq!(id.name().unwrap(), "example");
    /// ```
    #[cfg(feature = "friendly-api")]
    pub fn new<T>(name: T) -> Self
    where
        T: AsRef<str>,
    {
        get_ruby!().intern(name.as_ref())
    }

    pub(crate) fn from_rb_id(id: ID) -> Self {
        Self(id, PhantomData)
    }

    pub(crate) fn as_rb_id(self) -> ID {
        self.0
    }

    /// Return the `Id` for `name`, if one exists.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{value::Id, StaticSymbol};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(Id::check("example").is_none());
    /// StaticSymbol::new("example");
    /// assert!(Id::check("example").is_some());
    /// ```
    #[cfg(feature = "friendly-api")]
    #[inline]
    pub fn check(name: &str) -> Option<Self> {
        get_ruby!().check_id(name)
    }

    /// Return the symbol name associated with this Id as a static string
    /// reference.
    ///
    /// May error if the name is not valid utf-8.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::value::Id;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let id = Id::new("example");
    /// assert_eq!(id.name().unwrap(), "example");
    /// ```
    pub fn name(self) -> Result<&'static str, Error> {
        unsafe {
            let ptr = rb_id2name(self.as_rb_id());
            let cstr = CStr::from_ptr(ptr);
            cstr.to_str().map_err(|e| {
                Error::new(
                    Ruby::get_unchecked().exception_encoding_error(),
                    e.to_string(),
                )
            })
        }
    }
}

impl Borrow<OpaqueId> for Id {
    fn borrow(&self) -> &OpaqueId {
        unsafe { &*(self as *const Self as *const OpaqueId) }
    }
}

/// Conversions from Rust types into [`Id`].
pub trait IntoId: Sized {
    /// Convert `self` into [`Id`].
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread.
    ///
    #[cfg(feature = "friendly-api")]
    #[inline]
    fn into_id(self) -> Id {
        self.into_id_with(&get_ruby!())
    }

    /// Convert `self` into [`Id`].
    ///
    /// # Safety
    ///
    /// This method should only be called from a Ruby thread.
    unsafe fn into_id_unchecked(self) -> Id {
        self.into_id_with(&Ruby::get_unchecked())
    }

    /// Convert `self` into [`Id`].
    fn into_id_with(self, handle: &Ruby) -> Id;
}

impl IntoId for Id {
    fn into_id_with(self, _: &Ruby) -> Id {
        self
    }
}

impl IntoId for &str {
    fn into_id_with(self, handle: &Ruby) -> Id {
        handle.intern(self)
    }
}

impl IntoId for String {
    fn into_id_with(self, handle: &Ruby) -> Id {
        self.as_str().into_id_with(handle)
    }
}

impl IntoId for StaticSymbol {
    fn into_id_with(self, handle: &Ruby) -> Id {
        self.into_symbol_with(handle).into_id_with(handle)
    }
}

impl From<StaticSymbol> for Id {
    fn from(sym: StaticSymbol) -> Self {
        sym.into_id_with(&Ruby::get_with(sym))
    }
}

impl IntoId for Symbol {
    fn into_id_with(self, _: &Ruby) -> Id {
        if self.is_static_symbol() {
            Id::from_rb_id(self.as_rb_value() >> ruby_special_consts::RUBY_SPECIAL_SHIFT as VALUE)
        } else {
            Id::from_rb_id(unsafe { rb_sym2id(self.as_rb_value()) })
        }
    }
}

impl IntoValue for Id {
    fn into_value_with(self, handle: &Ruby) -> Value {
        StaticSymbol::from(self).into_value_with(handle)
    }
}

impl From<Symbol> for Id {
    fn from(sym: Symbol) -> Self {
        sym.into_id_with(&Ruby::get_with(sym))
    }
}

impl PartialEq<OpaqueId> for Id {
    fn eq(&self, other: &OpaqueId) -> bool {
        self.0 == other.0
    }
}

impl PartialEq<LazyId> for Id {
    fn eq(&self, other: &LazyId) -> bool {
        self.0 == (*other).0
    }
}

impl PartialEq<StaticSymbol> for Id {
    fn eq(&self, other: &StaticSymbol) -> bool {
        *self == other.into_id_with(&Ruby::get_with(*other))
    }
}

impl PartialEq<Symbol> for Id {
    fn eq(&self, other: &Symbol) -> bool {
        other.as_static().map(|o| *self == o).unwrap_or(false)
    }
}

/// A wrapper to make a Ruby [`Id`] [`Send`] + [`Sync`].
///
/// [`Id`] is not [`Send`] or [`Sync`] as it provides a way to call some of
/// Ruby's APIs, which are not safe to call from a non-Ruby thread.
///
/// [`Id`] is safe to send between Ruby threads, but Rust's trait system
/// currently can not model this detail.
///
/// To resolve this, the `OpaqueId` type makes an [`Id`] [`Send`] + [`Sync`]
/// by removing the ability use it with any Ruby APIs.
///
/// [`IntoId`] and [`IntoSymbol`] can be used to convert an `OpaqueId` back
/// into a type that can be used with Ruby's APIs. These traits can only be
/// used from a Ruby thread.
///
/// `OpaqueId` implements [`Eq`]/[`PartialEq`] and [`Hash`], so can be used as
/// a key or id on non-Ruby threads, or in data structures that must be
/// [`Send`] or [`Sync`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[repr(transparent)]
pub struct OpaqueId(ID);

impl From<Id> for OpaqueId {
    fn from(id: Id) -> Self {
        Self(id.0)
    }
}

impl From<StaticSymbol> for OpaqueId {
    fn from(sym: StaticSymbol) -> Self {
        sym.into_id_with(&Ruby::get_with(sym)).into()
    }
}

impl From<Symbol> for OpaqueId {
    fn from(sym: Symbol) -> Self {
        sym.into_id_with(&Ruby::get_with(sym)).into()
    }
}

impl IntoId for OpaqueId {
    fn into_id_with(self, _: &Ruby) -> Id {
        Id::from_rb_id(self.0)
    }
}

impl IntoSymbol for OpaqueId {
    fn into_symbol_with(self, handle: &Ruby) -> Symbol {
        self.into_id_with(handle).into_symbol_with(handle)
    }
}

impl IntoValue for OpaqueId {
    fn into_value_with(self, handle: &Ruby) -> Value {
        self.into_symbol_with(handle).into_value_with(handle)
    }
}

impl PartialEq<Id> for OpaqueId {
    fn eq(&self, other: &Id) -> bool {
        *self == Self::from(*other)
    }
}

impl PartialEq<LazyId> for OpaqueId {
    fn eq(&self, other: &LazyId) -> bool {
        *self == Self::from(**other)
    }
}

impl PartialEq<StaticSymbol> for OpaqueId {
    fn eq(&self, other: &StaticSymbol) -> bool {
        *self == other.into_id_with(&Ruby::get_with(*other))
    }
}

impl PartialEq<Symbol> for OpaqueId {
    fn eq(&self, other: &Symbol) -> bool {
        other.as_static().map(|o| *self == o).unwrap_or(false)
    }
}

/// An [`Id`] that can be assigned to a `static` and [`Deref`]s to [`OpaqueId`].
pub struct LazyId {
    init: Once,
    inner: UnsafeCell<LazyInner>,
}

union LazyInner {
    name: &'static str,
    value: OpaqueId,
}

impl LazyId {
    /// Create a new `LazyId`.
    pub const fn new(name: &'static str) -> Self {
        Self {
            init: Once::new(),
            inner: UnsafeCell::new(LazyInner { name }),
        }
    }

    /// Force evaluation of a `LazyId`.
    ///
    /// # Panics
    ///
    /// Panics if the `LazyId` is *poisoned*. See [`LazyId::get`].
    pub fn force(this: &Self, handle: &Ruby) {
        Self::get_with(this, handle);
    }

    /// Get an [`OpaqueId`] from a `LazyId`.
    ///
    /// # Panics
    ///
    /// Panics if the first call is from a non-Ruby thread. The `LazyId` will
    /// then be *poisoned* and all future use of it will panic.
    pub fn get(this: &Self) -> OpaqueId {
        *this.deref()
    }

    /// Get a [`Id`] from a `LazyId`.
    ///
    /// # Panics
    ///
    /// Panics if the `LazyId` is *poisoned*. See [`LazyId::get`].
    pub fn get_with(this: &Self, handle: &Ruby) -> Id {
        unsafe {
            this.init.call_once(|| {
                let inner = this.inner.get();
                (*inner).value = handle.intern((*inner).name).into();
            });
            (*this.inner.get()).value.into_id_with(handle)
        }
    }

    /// Get an [`OpaqueId`] from a `LazyId`, if it has already been evaluated.
    ///
    /// This function will not call Ruby and will not initialise the inner
    /// `OpaqueId`. If the `LazyId` has not yet been initialised, returns
    /// `None`.
    ///
    /// This function will not panic, if the `LazyId` is *poisoned* it will
    /// return `None`.
    pub fn try_get(this: &Self) -> Option<OpaqueId> {
        unsafe { this.init.is_completed().then(|| (*this.inner.get()).value) }
    }
}

unsafe impl Send for LazyId {}
unsafe impl Sync for LazyId {}

impl fmt::Debug for LazyId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        #[allow(non_camel_case_types)]
        #[derive(Debug)]
        struct uninit();

        f.debug_tuple("LazyId")
            .field(
                Self::try_get(self)
                    .as_ref()
                    .map(|v| v as &dyn fmt::Debug)
                    .unwrap_or(&uninit()),
            )
            .finish()
    }
}

impl Deref for LazyId {
    type Target = OpaqueId;

    /// # Panics
    ///
    /// Panics if the first call is from a non-Ruby thread. This `LazyId` will
    /// then be *poisoned* and all future use of it will panic.
    fn deref(&self) -> &Self::Target {
        unsafe {
            self.init.call_once(|| {
                let inner = self.inner.get();
                (*inner).value = Ruby::get().unwrap().intern((*inner).name).into();
            });
            &(*self.inner.get()).value
        }
    }
}

impl Hash for LazyId {
    /// # Panics
    ///
    /// Panics if the first call is from a non-Ruby thread. This `LazyId` will
    /// then be *poisoned* and all future use of it will panic.
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.deref().hash(state);
    }
}

impl PartialEq for LazyId {
    /// # Panics
    ///
    /// Panics if the first call is from a non-Ruby thread. This `LazyId` will
    /// then be *poisoned* and all future use of it will panic.
    fn eq(&self, other: &Self) -> bool {
        self.deref() == other.deref()
    }
}
impl Eq for LazyId {}

impl PartialEq<Id> for LazyId {
    /// # Panics
    ///
    /// Panics if the first call is from a non-Ruby thread. This `LazyId` will
    /// then be *poisoned* and all future use of it will panic.
    fn eq(&self, other: &Id) -> bool {
        *self.deref() == *other
    }
}

impl PartialEq<StaticSymbol> for LazyId {
    /// # Panics
    ///
    /// Panics if the first call is from a non-Ruby thread. This `LazyId` will
    /// then be *poisoned* and all future use of it will panic.
    fn eq(&self, other: &StaticSymbol) -> bool {
        *self == other.into_id_with(&Ruby::get_with(*other))
    }
}

impl PartialEq<Symbol> for LazyId {
    /// # Panics
    ///
    /// Panics if the first call is from a non-Ruby thread. This `LazyId` will
    /// then be *poisoned* and all future use of it will panic.
    fn eq(&self, other: &Symbol) -> bool {
        other.as_static().map(|o| *self == o).unwrap_or(false)
    }
}
