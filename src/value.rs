//! Types for working with Ruby's VALUE type, representing all objects, and 'immediate' values such as Fixnum.

#[cfg(ruby_use_flonum)]
mod flonum;

use std::{
    borrow::Cow,
    convert::TryFrom,
    ffi::CStr,
    fmt,
    mem::transmute,
    num::NonZeroUsize,
    ops::{Deref, DerefMut},
    os::raw::{c_char, c_int, c_long, c_ulong},
    ptr,
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
    class::{self, RClass},
    encoding::{EncodingCapable, RbEncoding},
    enumerator::Enumerator,
    error::{protect, Error},
    exception,
    integer::{Integer, IntegerType},
    into_value::{ArgList, IntoValue, IntoValueFromNative},
    method::{Block, BlockReturn},
    module::Module,
    numeric::Numeric,
    r_bignum::RBignum,
    r_string::RString,
    ruby_handle::RubyHandle,
    symbol::{IntoSymbol, Symbol},
    try_convert::{TryConvert, TryConvertOwned},
};

/// Debug assertation that the Value hasn't been garbage collected.
///
// This isn't infallible, if the original object was gc'd and that slot
// reused already this won't panic like it should, but we're trying our
// best here.
#[doc(hidden)]
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
            ::rb_sys::ruby_value_type::RUBY_T_NONE | ::rb_sys::ruby_value_type::RUBY_T_ZOMBIE => {
                panic!("Attempting to access garbage collected Object")
            }
            #[cfg(ruby_gte_2_7)]
            ::rb_sys::ruby_value_type::RUBY_T_MOVED => {
                panic!("Attempting to access garbage collected Object")
            }
            _ => (),
        };
    };
}

/// Ruby's `VALUE` type, which can represent any Ruby object.
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

    /// Returns whether `self` is an 'immediate' value.
    ///
    /// 'immediate' values are encoded directly into the `Value` and require
    /// no additional lookup. They will never be garbage collected.
    ///
    /// non-immediate values are pointers to other memory holding the data for
    /// the object.
    #[inline]
    pub(crate) fn is_immediate(self) -> bool {
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

    /// Returns whether `self` is Ruby's `nil` value.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Value};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(eval::<Value>("nil").unwrap().is_nil());
    /// assert!(!eval::<Value>("Object.new").unwrap().is_nil());
    /// assert!(!eval::<Value>("0").unwrap().is_nil());
    /// assert!(!eval::<Value>("[]").unwrap().is_nil());
    /// ```
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
    pub(crate) fn is_flonum(self) -> bool {
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
    /// use magnus::{Integer, RArray};
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
    /// use magnus::{eval, Value};
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
    /// assert!(a.equal(&b).is_err());
    /// ```
    pub fn equal<T>(self, other: T) -> Result<bool, Error>
    where
        T: Deref<Target = Value>,
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
    /// or some built-in types, then calling the `#==` method will be skipped.
    ///
    /// Returns `Err` if `#eql?` raises.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Integer, RArray};
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
    /// use magnus::{eval, Value};
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
    /// assert!(a.eql(&b).is_err());
    /// ```
    pub fn eql<T>(self, other: T) -> Result<bool, Error>
    where
        T: Deref<Target = Value>,
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
    /// use magnus::RString;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(RString::new("test").hash().unwrap()
    ///     .equal(RString::new("test").hash().unwrap())
    ///     .unwrap());
    /// ```
    pub fn hash(self) -> Result<Integer, Error> {
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
    /// use magnus::{eval, Value};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert_eq!(eval::<Value>("true").unwrap().class().inspect(), "TrueClass");
    /// assert_eq!(eval::<Value>("[1,2,3]").unwrap().class().inspect(), "Array");
    /// ```
    pub fn class(self) -> RClass {
        unsafe {
            match self.r_basic() {
                Some(r_basic) => RClass::from_rb_value_unchecked(r_basic.as_ref().klass),
                None => {
                    if self.is_false() {
                        class::false_class()
                    } else if self.is_nil() {
                        class::nil_class()
                    } else if self.is_true() {
                        class::true_class()
                    } else if self.is_undef() {
                        panic!("undef does not have a class")
                    } else if self.is_fixnum() {
                        class::integer()
                    } else if self.is_static_symbol() {
                        class::symbol()
                    } else if self.is_flonum() {
                        class::float()
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

    /// Returns whether `self` is 'frozen'.
    ///
    /// Ruby prevents modifying frozen objects.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Value};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(eval::<Value>(":foo").unwrap().is_frozen());
    /// assert!(eval::<Value>("42").unwrap().is_frozen());
    /// assert!(!eval::<Value>("[]").unwrap().is_frozen());
    /// ```
    pub fn is_frozen(self) -> bool {
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
    /// use magnus::{eval, Error, Value};
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
    pub fn check_frozen(self) -> Result<(), Error> {
        if self.is_frozen() {
            Err(Error::new(
                exception::frozen_error(),
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
    /// use magnus::{eval, RArray};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = RArray::new();
    /// assert!(!ary.is_frozen());
    /// ary.freeze();
    /// assert!(ary.is_frozen());
    /// ```
    pub fn freeze(self) {
        unsafe { rb_obj_freeze(self.as_rb_value()) };
    }

    /// Convert `self` to a `bool`, following Ruby's rules of `false` and `nil`
    /// as boolean `false` and everything else boolean `true`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Value};
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
    #[inline]
    pub fn to_bool(self) -> bool {
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
    /// use magnus::{eval, RArray};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let values = eval::<RArray>(r#"["foo", 1, :bar]"#).unwrap();
    /// let result: String = values.funcall("join", (" & ",)).unwrap();
    /// assert_eq!(result, "foo & 1 & bar");
    /// ```
    pub fn funcall<M, A, T>(self, method: M, args: A) -> Result<T, Error>
    where
        M: IntoId,
        A: ArgList,
        T: TryConvert,
    {
        unsafe {
            let id = method.into_id_unchecked();
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

    /// Call the public method named `method` on `self` with `args`.
    ///
    /// Returns `Ok(T)` if the method returns without error and the return
    /// value converts to a `T`, or returns `Err` if the method raises or the
    /// conversion fails.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Error, RObject, Symbol};
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
    pub fn funcall_public<M, A, T>(self, method: M, args: A) -> Result<T, Error>
    where
        M: IntoId,
        A: ArgList,
        T: TryConvert,
    {
        unsafe {
            let id = method.into_id_unchecked();
            let args = args.into_arg_list();
            let slice = args.as_ref();
            protect(|| {
                Value::new(rb_funcallv_public(
                    self.as_rb_value(),
                    id.as_rb_id(),
                    slice.len() as c_int,
                    slice.as_ptr() as *const VALUE,
                ))
            })
            .and_then(|v| v.try_convert())
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
    /// use magnus::{Float, Integer, RString};
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
    pub fn check_funcall<M, A, T>(self, method: M, args: A) -> Option<Result<T, Error>>
    where
        M: IntoId,
        A: ArgList,
        T: TryConvert,
    {
        let id = unsafe { method.into_id_unchecked() };
        let args = args.into_arg_list();
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
                Ok(v) => Some(v.try_convert()),
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
    /// use magnus::{eval, block::Proc, RArray, Value};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let values = eval::<RArray>(r#"["foo", 1, :bar]"#).unwrap();
    /// let block = Proc::new(|args, _block| args.first().unwrap().to_r_string());
    /// let _: Value = values.funcall_with_block("map!", (), block).unwrap();
    /// assert_eq!(values.to_vec::<String>().unwrap(), vec!["foo", "1", "bar"]);
    /// ```
    pub fn funcall_with_block<M, A, T>(self, method: M, args: A, block: Proc) -> Result<T, Error>
    where
        M: IntoId,
        A: ArgList,
        T: TryConvert,
    {
        unsafe {
            let id = method.into_id_unchecked();
            let args = args.into_arg_list();
            let slice = args.as_ref();
            protect(|| {
                Value::new(rb_funcall_with_block(
                    self.as_rb_value(),
                    id.as_rb_id(),
                    slice.len() as c_int,
                    slice.as_ptr() as *const VALUE,
                    block.as_rb_value(),
                ))
            })
            .and_then(|v| v.try_convert())
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
    /// use magnus::{eval, RArray, Value};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let values = eval::<RArray>(r#"["foo", 1, :bar]"#).unwrap();
    /// let _: Value = values.block_call("map!", (), |args, _block| args.first().unwrap().to_r_string()).unwrap();
    /// assert_eq!(values.to_vec::<String>().unwrap(), vec!["foo", "1", "bar"]);
    /// ```
    pub fn block_call<M, A, R, T>(
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
            Block::new(func)
                .call_handle_error(argc, argv as *const Value, Value::new(blockarg))
                .as_rb_value()
        }

        let id = unsafe { method.into_id_unchecked() };
        let args = args.into_arg_list();
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
        .and_then(|v| v.try_convert())
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
    /// use magnus::RString;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let s = RString::new("example");
    /// assert!(s.respond_to("to_str", false).unwrap());
    /// assert!(!s.respond_to("puts", false).unwrap());
    /// assert!(s.respond_to("puts", true).unwrap());
    /// assert!(!s.respond_to("non_existant", false).unwrap());
    /// assert!(!s.respond_to("non_existant", true).unwrap());
    /// ```
    pub fn respond_to<M>(self, method: M, include_private: bool) -> Result<bool, Error>
    where
        M: IntoId,
    {
        let id = unsafe { method.into_id_unchecked() };
        let mut res = false;
        protect(|| {
            unsafe {
                res =
                    rb_obj_respond_to(self.as_rb_value(), id.as_rb_id(), include_private as c_int)
                        != 0;
            }
            QNIL
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
    /// use magnus::{eval, class, Value};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let value = eval::<Value>("[]").unwrap();
    /// assert!(value.to_r_string().unwrap().is_kind_of(class::string()));
    /// ```
    pub fn to_r_string(self) -> Result<RString, Error> {
        match RString::from_value(self) {
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
    /// use magnus::{eval, QTRUE};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let value = QTRUE;
    /// // safe as we neve give Ruby a chance to free the string.
    /// let s = unsafe { value.to_s() }.unwrap().into_owned();
    /// assert_eq!(s, "true");
    /// ```
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

    /// Convert `self` to a string. If an error is encountered returns a
    /// generic string (usually the object's class name).
    ///
    /// # Safety
    ///
    /// This may return a direct view of memory owned and managed by Ruby. Ruby
    /// may modify or free the memory backing the returned str, the caller must
    /// ensure this does not happen.
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

    /// Convert `self` to its Ruby debug representation.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Symbol, QNIL};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert_eq!(QNIL.inspect(), "nil");
    /// assert_eq!(Symbol::new("foo").inspect(), ":foo");
    /// ```
    pub fn inspect(self) -> String {
        unsafe {
            let s = protect(|| RString::from_rb_value_unchecked(rb_inspect(self.as_rb_value())))
                .unwrap_or_else(|_| {
                    RString::from_rb_value_unchecked(rb_any_to_s(self.as_rb_value()))
                });
            s.conv_enc(RbEncoding::utf8())
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
    /// use magnus::{eval, RHash};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let value = RHash::new();
    /// // safe as we never give Ruby a chance to free the string.
    /// let s = unsafe { value.classname() }.into_owned();
    /// assert_eq!(s, "Hash");
    /// ```
    pub unsafe fn classname(&self) -> Cow<str> {
        let ptr = rb_obj_classname(self.as_rb_value());
        let cstr = CStr::from_ptr(ptr);
        cstr.to_string_lossy()
    }

    /// Returns whether or not `self` is an instance of `class`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{class, eval, Value};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let value = eval::<Value>("[]").unwrap();
    /// assert!(value.is_kind_of(class::array()));
    /// ```
    pub fn is_kind_of<T>(self, class: T) -> bool
    where
        T: Deref<Target = Value> + Module,
    {
        unsafe { Value::new(rb_obj_is_kind_of(self.as_rb_value(), class.as_rb_value())).to_bool() }
    }

    /// Generate an [`Enumerator`] from `method` on `self`, passing `args` to
    /// `method`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{class, eval, r_string};
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
    pub fn enumeratorize<M, A>(self, method: M, args: A) -> Enumerator
    where
        M: IntoSymbol,
        A: ArgList,
    {
        let args = args.into_arg_list();
        let slice = args.as_ref();
        unsafe {
            Enumerator::from_rb_value_unchecked(rb_enumeratorize_with_size(
                self.as_rb_value(),
                method.into_symbol_unchecked().as_rb_value(),
                slice.len() as c_int,
                slice.as_ptr() as *const VALUE,
                None,
            ))
        }
    }

    /// Convert `self` to the Rust type `T`.
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
    #[inline]
    pub fn try_convert<T>(self) -> Result<T, Error>
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

impl IntoValue for Value {
    fn into_value_with(self, _: &RubyHandle) -> Value {
        self
    }
}

impl IntoValue for i8 {
    fn into_value_with(self, handle: &RubyHandle) -> Value {
        handle.integer_from_i64(self as i64).into()
    }
}

unsafe impl IntoValueFromNative for i8 {}

impl From<i8> for Value {
    fn from(value: i8) -> Self {
        value.into_value()
    }
}

impl IntoValue for i16 {
    fn into_value_with(self, handle: &RubyHandle) -> Value {
        handle.integer_from_i64(self as i64).into()
    }
}

unsafe impl IntoValueFromNative for i16 {}

impl From<i16> for Value {
    fn from(value: i16) -> Self {
        value.into_value()
    }
}

impl IntoValue for i32 {
    fn into_value_with(self, handle: &RubyHandle) -> Value {
        handle.integer_from_i64(self as i64).into()
    }
}

unsafe impl IntoValueFromNative for i32 {}

impl From<i32> for Value {
    fn from(value: i32) -> Self {
        value.into_value()
    }
}

impl IntoValue for i64 {
    fn into_value_with(self, handle: &RubyHandle) -> Value {
        handle.integer_from_i64(self).into()
    }
}

unsafe impl IntoValueFromNative for i64 {}

impl From<i64> for Value {
    fn from(value: i64) -> Self {
        value.into_value()
    }
}

impl IntoValue for isize {
    fn into_value_with(self, handle: &RubyHandle) -> Value {
        handle.integer_from_i64(self as i64).into()
    }
}

unsafe impl IntoValueFromNative for isize {}

impl From<isize> for Value {
    fn from(value: isize) -> Self {
        value.into_value()
    }
}

impl IntoValue for u8 {
    fn into_value_with(self, handle: &RubyHandle) -> Value {
        handle.integer_from_u64(self as u64).into()
    }
}

unsafe impl IntoValueFromNative for u8 {}

impl From<u8> for Value {
    fn from(value: u8) -> Self {
        value.into_value()
    }
}

impl IntoValue for u16 {
    fn into_value_with(self, handle: &RubyHandle) -> Value {
        handle.integer_from_u64(self as u64).into()
    }
}

unsafe impl IntoValueFromNative for u16 {}

impl From<u16> for Value {
    fn from(value: u16) -> Self {
        value.into_value()
    }
}

impl IntoValue for u32 {
    fn into_value_with(self, handle: &RubyHandle) -> Value {
        handle.integer_from_u64(self as u64).into()
    }
}

unsafe impl IntoValueFromNative for u32 {}

impl From<u32> for Value {
    fn from(value: u32) -> Self {
        value.into_value()
    }
}

impl IntoValue for u64 {
    fn into_value_with(self, handle: &RubyHandle) -> Value {
        handle.integer_from_u64(self).into()
    }
}

unsafe impl IntoValueFromNative for u64 {}

impl From<u64> for Value {
    fn from(value: u64) -> Self {
        value.into_value()
    }
}

impl IntoValue for usize {
    fn into_value_with(self, handle: &RubyHandle) -> Value {
        handle.integer_from_u64(self as u64).into()
    }
}

unsafe impl IntoValueFromNative for usize {}

impl From<usize> for Value {
    fn from(value: usize) -> Self {
        value.into_value()
    }
}

impl IntoValue for f32 {
    fn into_value_with(self, handle: &RubyHandle) -> Value {
        handle.float_from_f64(self as f64).into()
    }
}

unsafe impl IntoValueFromNative for f32 {}

impl From<f32> for Value {
    fn from(value: f32) -> Self {
        value.into_value()
    }
}

impl IntoValue for f64 {
    fn into_value_with(self, handle: &RubyHandle) -> Value {
        handle.float_from_f64(self).into()
    }
}

unsafe impl IntoValueFromNative for f64 {}

impl From<f64> for Value {
    fn from(value: f64) -> Self {
        value.into_value()
    }
}

impl TryConvert for Value {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Ok(val)
    }
}

pub(crate) mod private {
    use super::*;

    /// Marker trait for types that have the same representation as [`Value`].
    ///
    /// Types that are `ReprValue` can be safely transmuted to Value.
    ///
    /// # Safety
    ///
    /// This trait should only be implemented for types that a guaranteed to
    /// have the same layout as [`Value`] and have come from the Ruby VM.
    pub unsafe trait ReprValue: Copy {
        /// Convert `self` to a [`Value`].
        ///
        /// Usually types that implement this trait will also implement
        /// `Deref<Target = Value>`. You should prefer `*data` over
        /// `data.to_value()`.
        ///
        /// This method is for use cases where we effectively want
        /// `transmute::<_, Value>(data)`.
        fn to_value(self) -> Value;

        /// Convert `val` to a `Self`.
        ///
        /// # Safety
        ///
        /// This should only be used when `val` is known to uphold all the
        // invariants of `Self`. It is recommended not to use this method.
        unsafe fn from_value_unchecked(val: Value) -> Self;
    }
}

/// Marker trait for types that have the same representation as [`Value`].
///
/// Types that are `ReprValue` can be safely transmuted to Value.
pub trait ReprValue: private::ReprValue {}

unsafe impl private::ReprValue for Value {
    fn to_value(self) -> Value {
        self
    }

    unsafe fn from_value_unchecked(val: Value) -> Self {
        val
    }
}

impl ReprValue for Value {}

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

/// Protects a Ruby Value from the garbage collector.
///
/// See also [`gc::register_mark_object`](crate::gc::register_mark_object) for
/// a value that should be permanently excluded from garbage collection.
///
/// All [`Value`] methods should be available on this type through [`Deref`],
/// but some may be missed by this documentation.
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
        write!(f, "{}", unsafe { self.to_value().to_s_infallible() })
    }
}

impl<T> fmt::Debug for BoxValue<T>
where
    T: ReprValue,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_value().inspect())
    }
}

impl<T> IntoValue for BoxValue<T>
where
    T: ReprValue,
{
    fn into_value_with(self, _: &RubyHandle) -> Value {
        self.to_value()
    }
}

unsafe impl<T> IntoValueFromNative for BoxValue<T> where T: ReprValue {}

impl<T> From<BoxValue<T>> for Value
where
    T: ReprValue,
{
    fn from(val: BoxValue<T>) -> Self {
        val.to_value()
    }
}

/// Ruby's `false` value.
///
/// See [`QFALSE`] to obtain a value of this type.
///
/// All [`Value`] methods should be available on this type through [`Deref`],
/// but some may be missed by this documentation.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Qfalse(Value);

/// Ruby's `false` value.
pub const QFALSE: Qfalse = Qfalse::new();

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

impl Deref for Qfalse {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        &self.0
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
    fn into_value_with(self, _: &RubyHandle) -> Value {
        *self
    }
}

impl From<Qfalse> for Value {
    fn from(val: Qfalse) -> Self {
        *val
    }
}

unsafe impl private::ReprValue for Qfalse {
    fn to_value(self) -> Value {
        *self
    }

    unsafe fn from_value_unchecked(val: Value) -> Self {
        Self(val)
    }
}

impl ReprValue for Qfalse {}

impl TryConvert for Qfalse {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Self::from_value(val).ok_or_else(|| {
            Error::new(
                exception::type_error(),
                format!("no implicit conversion of {} into FalseClass", unsafe {
                    val.classname()
                },),
            )
        })
    }
}
impl TryConvertOwned for Qfalse {}

/// Ruby's `nil` value.
///
/// See [`QNIL`] to obtain a value of this type.
///
/// All [`Value`] methods should be available on this type through [`Deref`],
/// but some may be missed by this documentation.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Qnil(NonZeroValue);

/// Ruby's `nil` value.
pub const QNIL: Qnil = Qnil::new();

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

impl IntoValue for Qnil {
    fn into_value_with(self, _: &RubyHandle) -> Value {
        *self
    }
}

impl From<Qnil> for Value {
    fn from(val: Qnil) -> Self {
        *val
    }
}

impl IntoValue for () {
    fn into_value_with(self, _: &RubyHandle) -> Value {
        QNIL.into()
    }
}

unsafe impl IntoValueFromNative for () {}

impl From<()> for Value {
    fn from(val: ()) -> Self {
        val.into_value()
    }
}

impl<T> IntoValue for Option<T>
where
    T: IntoValue,
{
    fn into_value_with(self, handle: &RubyHandle) -> Value {
        match self {
            Some(t) => handle.into_value(t),
            None => handle.into_value(QNIL),
        }
    }
}

unsafe impl<T> IntoValueFromNative for Option<T> where T: IntoValueFromNative {}

unsafe impl private::ReprValue for Qnil {
    fn to_value(self) -> Value {
        *self
    }

    unsafe fn from_value_unchecked(val: Value) -> Self {
        Self(NonZeroValue::new_unchecked(val))
    }
}

impl ReprValue for Qnil {}

impl TryConvert for Qnil {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Self::from_value(val).ok_or_else(|| {
            Error::new(
                exception::type_error(),
                format!("no implicit conversion of {} into NilClass", unsafe {
                    val.classname()
                },),
            )
        })
    }
}
impl TryConvertOwned for Qnil {}

/// Ruby's `true` value.
///
/// See [`QTRUE`] to obtain a value of this type.
///
/// All [`Value`] methods should be available on this type through [`Deref`],
/// but some may be missed by this documentation.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Qtrue(NonZeroValue);

/// Ruby's `true` value.
pub const QTRUE: Qtrue = Qtrue::new();

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

impl IntoValue for Qtrue {
    fn into_value_with(self, _: &RubyHandle) -> Value {
        *self
    }
}

impl From<Qtrue> for Value {
    fn from(val: Qtrue) -> Self {
        *val
    }
}

impl IntoValue for bool {
    fn into_value_with(self, _: &RubyHandle) -> Value {
        if self {
            QTRUE.into()
        } else {
            QFALSE.into()
        }
    }
}

unsafe impl IntoValueFromNative for bool {}

impl From<bool> for Value {
    fn from(val: bool) -> Self {
        val.into_value()
    }
}

unsafe impl private::ReprValue for Qtrue {
    fn to_value(self) -> Value {
        *self
    }

    unsafe fn from_value_unchecked(val: Value) -> Self {
        Self(NonZeroValue::new_unchecked(val))
    }
}

impl ReprValue for Qtrue {}

impl TryConvert for Qtrue {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Self::from_value(val).ok_or_else(|| {
            Error::new(
                exception::type_error(),
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
    /// method, rather than implimenting [`IntoValue`]).
    #[inline]
    pub unsafe fn to_value(self) -> Value {
        self.0.get()
    }
}

impl RubyHandle {
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
/// All [`Value`] methods should be available on this type through [`Deref`],
/// but some may be missed by this documentation.
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
                exception::range_error(),
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
                exception::range_error(),
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
                exception::range_error(),
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
        if self.is_negative() {
            return Err(Error::new(
                exception::range_error(),
                "can't convert negative integer to unsigned",
            ));
        }
        let res = self.to_isize();
        if res > u8::MAX as isize {
            return Err(Error::new(
                exception::range_error(),
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
        if self.is_negative() {
            return Err(Error::new(
                exception::range_error(),
                "can't convert negative integer to unsigned",
            ));
        }
        let res = self.to_isize();
        if res > u16::MAX as isize {
            return Err(Error::new(
                exception::range_error(),
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
        if self.is_negative() {
            return Err(Error::new(
                exception::range_error(),
                "can't convert negative integer to unsigned",
            ));
        }
        let res = self.to_isize();
        if res > u32::MAX as isize {
            return Err(Error::new(
                exception::range_error(),
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
                exception::range_error(),
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
                exception::range_error(),
                "can't convert negative integer to unsigned",
            ));
        }
        Ok(self.to_isize() as usize)
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

impl IntoValue for Fixnum {
    fn into_value_with(self, _: &RubyHandle) -> Value {
        *self
    }
}

impl From<Fixnum> for Value {
    fn from(val: Fixnum) -> Self {
        *val
    }
}

unsafe impl private::ReprValue for Fixnum {
    fn to_value(self) -> Value {
        *self
    }

    unsafe fn from_value_unchecked(val: Value) -> Self {
        Self(NonZeroValue::new_unchecked(val))
    }
}

impl Numeric for Fixnum {}

impl ReprValue for Fixnum {}

impl TryConvert for Fixnum {
    fn try_convert(val: Value) -> Result<Self, Error> {
        match val.try_convert::<Integer>()?.integer_type() {
            IntegerType::Fixnum(fix) => Ok(fix),
            IntegerType::Bignum(_) => Err(Error::new(
                exception::range_error(),
                "integer too big for fixnum",
            )),
        }
    }
}
impl TryConvertOwned for Fixnum {}

impl RubyHandle {
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
                RbEncoding::utf8().as_ptr(),
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
/// All [`Value`] methods should be available on this type through [`Deref`],
/// but some may be missed by this documentation.
#[derive(Clone, Copy)]
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

impl EncodingCapable for StaticSymbol {}

impl From<Id> for StaticSymbol {
    fn from(id: Id) -> Self {
        unsafe { Self::from_rb_value_unchecked(rb_id2sym(id.as_rb_id())) }
    }
}

impl IntoValue for StaticSymbol {
    fn into_value_with(self, _: &RubyHandle) -> Value {
        *self
    }
}

impl From<StaticSymbol> for Value {
    fn from(val: StaticSymbol) -> Self {
        *val
    }
}

unsafe impl private::ReprValue for StaticSymbol {
    fn to_value(self) -> Value {
        *self
    }

    unsafe fn from_value_unchecked(val: Value) -> Self {
        Self(NonZeroValue::new_unchecked(val))
    }
}

impl ReprValue for StaticSymbol {}

impl TryConvert for StaticSymbol {
    fn try_convert(val: Value) -> Result<Self, Error> {
        val.try_convert::<Symbol>().map(|s| s.to_static())
    }
}
impl TryConvertOwned for StaticSymbol {}

impl RubyHandle {
    pub fn check_id(&self, name: &str) -> Option<Id> {
        let res = unsafe {
            rb_check_id_cstr(
                name.as_ptr() as *mut c_char,
                name.len() as c_long,
                RbEncoding::utf8().as_ptr(),
            )
        };
        (res != 0).then(|| Id::from_rb_id(res))
    }
}

/// The internal value of a Ruby symbol.
#[derive(Clone, Copy, Debug, PartialEq)]
#[repr(transparent)]
pub struct Id(ID);

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
    pub fn new<T>(name: T) -> Self
    where
        T: AsRef<str>,
    {
        name.as_ref().into_id()
    }

    pub(crate) fn from_rb_id(id: ID) -> Self {
        Self(id)
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
            cstr.to_str()
                .map_err(|e| Error::new(exception::encoding_error(), e.to_string()))
        }
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
        self.into_id_with(&RubyHandle::get_unchecked())
    }

    /// Convert `self` into [`Id`].
    fn into_id_with(self, handle: &RubyHandle) -> Id;
}

impl IntoId for Id {
    fn into_id_with(self, _: &RubyHandle) -> Id {
        self
    }
}

impl IntoId for &str {
    fn into_id_with(self, handle: &RubyHandle) -> Id {
        Id::from_rb_id(unsafe {
            rb_intern3(
                self.as_ptr() as *const c_char,
                self.len() as c_long,
                handle.utf8_encoding().as_ptr(),
            )
        })
    }
}

impl IntoId for String {
    fn into_id_with(self, handle: &RubyHandle) -> Id {
        self.as_str().into_id_with(handle)
    }
}

impl IntoId for StaticSymbol {
    fn into_id_with(self, _: &RubyHandle) -> Id {
        Id::from_rb_id(unsafe { rb_sym2id(self.as_rb_value()) })
    }
}

impl From<StaticSymbol> for Id {
    fn from(sym: StaticSymbol) -> Self {
        unsafe { sym.into_id_unchecked() }
    }
}

impl IntoId for Symbol {
    fn into_id_with(self, _: &RubyHandle) -> Id {
        Id::from_rb_id(unsafe { rb_sym2id(self.as_rb_value()) })
    }
}

impl From<Symbol> for Id {
    fn from(sym: Symbol) -> Self {
        unsafe { sym.into_id_unchecked() }
    }
}
