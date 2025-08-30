//! Types and functions for working with Ruby's Fiber class.

use std::{ffi::c_int, fmt, mem::size_of, slice};

#[cfg(ruby_lt_3_2)]
use rb_sys::rb_fiber_new;
#[cfg(ruby_gte_3_2)]
use rb_sys::rb_fiber_new_storage;
use rb_sys::{
    VALUE, rb_data_typed_object_wrap, rb_fiber_alive_p, rb_fiber_current, rb_fiber_raise,
    rb_fiber_resume_kw, rb_fiber_transfer_kw, rb_fiber_yield_kw, rb_obj_is_fiber,
};

#[cfg(any(ruby_gte_3_2, docsrs))]
use crate::r_hash::RHash;
use crate::{
    api::Ruby,
    block::Proc,
    error::{Error, protect},
    exception::Exception,
    gc,
    into_value::{ArgList, IntoValue, kw_splat},
    method::{Block, BlockReturn},
    object::Object,
    r_typed_data::RTypedData,
    try_convert::TryConvert,
    typed_data::{DataType, DataTypeBuilder, DataTypeFunctions},
    value::{
        QUNDEF, ReprValue, Value,
        private::{self, ReprValue as _},
    },
};

/// # `Fiber`
///
/// Functions to create and work with Ruby `Fiber`s.
///
/// See also the [`Fiber`] type.
impl Ruby {
    /// Create a Ruby Fiber.
    ///
    /// As `func` is a function pointer, only functions and closures that do
    /// not capture any variables are permitted. For more flexibility (at the
    /// cost of allocating) see [`fiber_new_from_fn`](Ruby::fiber_new_from_fn).
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby, Value, prelude::*, rb_assert};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let fib = ruby.fiber_new(Default::default(), |ruby, args, _block| {
    ///         let mut a = u64::try_convert(*args.get(0).unwrap())?;
    ///         let mut b = u64::try_convert(*args.get(1).unwrap())?;
    ///         while let Some(c) = a.checked_add(b) {
    ///             let _: Value = ruby.fiber_yield((c,))?;
    ///             a = b;
    ///             b = c;
    ///         }
    ///         Ok(())
    ///     })?;
    ///
    ///     rb_assert!(ruby, "fib.resume(0, 1) == 1", fib);
    ///     rb_assert!(ruby, "fib.resume == 2", fib);
    ///     rb_assert!(ruby, "fib.resume == 3", fib);
    ///     rb_assert!(ruby, "fib.resume == 5", fib);
    ///     rb_assert!(ruby, "fib.resume == 8", fib);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn fiber_new<R>(
        &self,
        storage: Storage,
        func: fn(&Ruby, &[Value], Option<Proc>) -> R,
    ) -> Result<Fiber, Error>
    where
        R: BlockReturn,
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
            unsafe {
                let func = std::mem::transmute::<VALUE, fn(&Ruby, &[Value], Option<Proc>) -> R>(
                    callback_arg,
                );
                func.call_handle_error(argc, argv as *const Value, Value::new(blockarg))
                    .as_rb_value()
            }
        }

        let call_func =
            call::<R> as unsafe extern "C" fn(VALUE, VALUE, c_int, *const VALUE, VALUE) -> VALUE;

        unsafe {
            // VALUE is defined as u64/u32, so clippy thinks it's not
            // pointer-sized and wants us to cast to usize, but it doesn't know
            // the definition of VALUE changes based on pointer size
            #[allow(clippy::fn_to_numeric_cast)]
            protect(|| {
                #[cfg(ruby_gte_3_2)]
                let value =
                    rb_fiber_new_storage(Some(call_func), func as VALUE, storage.as_rb_value());
                #[cfg(ruby_lt_3_2)]
                let value = rb_fiber_new(Some(call_func), func as VALUE);
                Fiber::from_rb_value_unchecked(value)
            })
        }
    }

    /// Create a Ruby Fiber.
    ///
    /// See also [`fiber_new`](Ruby::fiber_new), which is more efficient when
    /// `func` is a function or closure that does not capture any variables.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby, Value, rb_assert};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let mut a = 0_u64;
    ///     let mut b = 1_u64;
    ///
    ///     let fib = ruby.fiber_new_from_fn(Default::default(), move |ruby, _args, _block| {
    ///         while let Some(c) = a.checked_add(b) {
    ///             let _: Value = ruby.fiber_yield((c,))?;
    ///             a = b;
    ///             b = c;
    ///         }
    ///         Ok(())
    ///     })?;
    ///
    ///     rb_assert!(ruby, "fib.resume == 1", fib);
    ///     rb_assert!(ruby, "fib.resume == 2", fib);
    ///     rb_assert!(ruby, "fib.resume == 3", fib);
    ///     rb_assert!(ruby, "fib.resume == 5", fib);
    ///     rb_assert!(ruby, "fib.resume == 8", fib);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn fiber_new_from_fn<F, R>(&self, storage: Storage, func: F) -> Result<Fiber, Error>
    where
        F: 'static + Send + FnOnce(&Ruby, &[Value], Option<Proc>) -> R,
        R: BlockReturn,
    {
        unsafe extern "C" fn call<F, R>(
            _yielded_arg: VALUE,
            callback_arg: VALUE,
            argc: c_int,
            argv: *const VALUE,
            blockarg: VALUE,
        ) -> VALUE
        where
            F: FnOnce(&Ruby, &[Value], Option<Proc>) -> R,
            R: BlockReturn,
        {
            unsafe {
                let closure = (*(callback_arg as *mut Option<F>)).take().unwrap();
                closure
                    .call_handle_error(argc, argv as *const Value, Value::new(blockarg))
                    .as_rb_value()
            }
        }

        let (closure, keepalive) = wrap_closure(func);
        let call_func =
            call::<F, R> as unsafe extern "C" fn(VALUE, VALUE, c_int, *const VALUE, VALUE) -> VALUE;

        protect(|| {
            #[cfg(ruby_gte_3_2)]
            let fiber = unsafe {
                Fiber::from_rb_value_unchecked(rb_fiber_new_storage(
                    Some(call_func),
                    closure as VALUE,
                    storage.as_rb_value(),
                ))
            };
            #[cfg(ruby_lt_3_2)]
            let fiber = unsafe {
                Fiber::from_rb_value_unchecked(rb_fiber_new(Some(call_func), closure as VALUE))
            };
            // ivar without @ prefix is invisible from Ruby
            fiber.ivar_set("__rust_closure", keepalive).unwrap();
            fiber
        })
    }

    /// Return the currently executing Fiber.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby, rb_assert};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let fiber = ruby.fiber_current();
    ///
    ///     rb_assert!(ruby, "fiber.is_a?(Fiber)", fiber);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn fiber_current(&self) -> Fiber {
        unsafe { Fiber::from_rb_value_unchecked(rb_fiber_current()) }
    }

    /// Transfer execution back to where the current Fiber was resumed.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby, Value, rb_assert, value::Opaque};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let ary = ruby.ary_new();
    ///     let send_array = Opaque::from(ary);
    ///
    ///     let fiber = ruby.fiber_new_from_fn(Default::default(), move |ruby, _args, _block| {
    ///         let ary = ruby.get_inner(send_array);
    ///         ary.push(1)?;
    ///         let _: Value = ruby.fiber_yield(())?;
    ///         ary.push(2)?;
    ///         let _: Value = ruby.fiber_yield(())?;
    ///         ary.push(3)?;
    ///         let _: Value = ruby.fiber_yield(())?;
    ///         Ok(())
    ///     })?;
    ///
    ///     ary.push("a")?;
    ///     let _: Value = fiber.resume(())?;
    ///     ary.push("b")?;
    ///     let _: Value = fiber.resume(())?;
    ///     ary.push("c")?;
    ///     let _: Value = fiber.resume(())?;
    ///
    ///     rb_assert!(ruby, r#"ary == ["a", 1, "b", 2, "c", 3]"#, ary);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn fiber_yield<A, T>(&self, args: A) -> Result<T, Error>
    where
        A: ArgList,
        T: TryConvert,
    {
        let kw_splat = kw_splat(&args);
        let args = args.into_arg_list_with(self);
        let slice = args.as_ref();
        unsafe {
            protect(|| {
                Value::new(rb_fiber_yield_kw(
                    slice.len() as c_int,
                    slice.as_ptr() as *const VALUE,
                    kw_splat as c_int,
                ))
            })
            .and_then(TryConvert::try_convert)
        }
    }
}

/// Wrapper type for a Value known to be an instance of Ruby's Fiber class.
///
/// See the [`ReprValue`] and [`Object`] traits for additional methods
/// available on this type. See [`Ruby`](Ruby#fiber) for methods to create a
/// `Fiber` and [`Ruby::fiber_yield`].
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Fiber(RTypedData);

impl Fiber {
    /// Return `Some(Fiber)` if `val` is a `Fiber`, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::eval;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(magnus::Fiber::from_value(eval("Fiber.new {1 + 2}").unwrap()).is_some());
    /// assert!(magnus::Fiber::from_value(eval("Thread.new {1 + 2}").unwrap()).is_none());
    /// assert!(magnus::Fiber::from_value(eval("Proc.new {1 + 2}").unwrap()).is_none());
    /// ```
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            Value::new(rb_obj_is_fiber(val.as_rb_value()))
                .to_bool()
                .then(|| Self::from_rb_value_unchecked(val.as_rb_value()))
        }
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        unsafe { Self(RTypedData::from_rb_value_unchecked(val)) }
    }

    /// Return `true` if `self` can be resumed, `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby, Value};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let fiber = ruby.fiber_new(Default::default(), move |ruby, _args, _block| {
    ///         let _: Value = ruby.fiber_yield((1,))?;
    ///         let _: Value = ruby.fiber_yield((3,))?;
    ///         Ok(5)
    ///     })?;
    ///
    ///     assert!(fiber.is_alive());
    ///     assert_eq!(fiber.resume::<_, u64>(())?, 1);
    ///     assert!(fiber.is_alive());
    ///     assert_eq!(fiber.resume::<_, u64>(())?, 3);
    ///     assert!(fiber.is_alive());
    ///     assert_eq!(fiber.resume::<_, u64>(())?, 5);
    ///     assert!(!fiber.is_alive());
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn is_alive(self) -> bool {
        unsafe { Value::new(rb_fiber_alive_p(self.as_rb_value())).to_bool() }
    }

    /// Resume the execution of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby, Value, prelude::*};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let fib = ruby.fiber_new(Default::default(), |ruby, args, _block| {
    ///         let mut a = u64::try_convert(*args.get(0).unwrap())?;
    ///         let mut b = u64::try_convert(*args.get(1).unwrap())?;
    ///         while let Some(c) = a.checked_add(b) {
    ///             let _: Value = ruby.fiber_yield((c,))?;
    ///             a = b;
    ///             b = c;
    ///         }
    ///         Ok(())
    ///     })?;
    ///
    ///     assert_eq!(fib.resume::<_, u64>((0, 1))?, 1);
    ///     assert_eq!(fib.resume::<_, u64>(())?, 2);
    ///     assert_eq!(fib.resume::<_, u64>(())?, 3);
    ///     assert_eq!(fib.resume::<_, u64>(())?, 5);
    ///     assert_eq!(fib.resume::<_, u64>(())?, 8);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn resume<A, T>(self, args: A) -> Result<T, Error>
    where
        A: ArgList,
        T: TryConvert,
    {
        let kw_splat = kw_splat(&args);
        let args = args.into_arg_list_with(&Ruby::get_with(self));
        let slice = args.as_ref();
        unsafe {
            protect(|| {
                Value::new(rb_fiber_resume_kw(
                    self.as_rb_value(),
                    slice.len() as c_int,
                    slice.as_ptr() as *const VALUE,
                    kw_splat as c_int,
                ))
            })
            .and_then(TryConvert::try_convert)
        }
    }

    /// Transfer control to another Fiber.
    ///
    /// `transfer` is an alternate API to
    /// [`resume`](Fiber::resume)/[`yield`](Ruby::fiber_yield). The two APIs
    /// can not be mixed, a Fiber muse use *either* `transfer` or
    /// `resume`/`yield` to pass control.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Fiber, Ruby, TryConvert, Value};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let fib = ruby.fiber_new(Default::default(), |_ruby, args, _block| {
    ///         let root = Fiber::try_convert(*args.get(0).unwrap())?;
    ///         let mut a = u64::try_convert(*args.get(1).unwrap())?;
    ///         let mut b = u64::try_convert(*args.get(2).unwrap())?;
    ///         while let Some(c) = a.checked_add(b) {
    ///             let _: Value = root.transfer((c,))?;
    ///             a = b;
    ///             b = c;
    ///         }
    ///         Ok(())
    ///     })?;
    ///
    ///     assert_eq!(fib.transfer::<_, u64>((ruby.fiber_current(), 0, 1))?, 1);
    ///     assert_eq!(fib.transfer::<_, u64>(())?, 2);
    ///     assert_eq!(fib.transfer::<_, u64>(())?, 3);
    ///     assert_eq!(fib.transfer::<_, u64>(())?, 5);
    ///     assert_eq!(fib.transfer::<_, u64>(())?, 8);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn transfer<A, T>(self, args: A) -> Result<T, Error>
    where
        A: ArgList,
        T: TryConvert,
    {
        let kw_splat = kw_splat(&args);
        let args = args.into_arg_list_with(&Ruby::get_with(self));
        let slice = args.as_ref();
        unsafe {
            protect(|| {
                Value::new(rb_fiber_transfer_kw(
                    self.as_rb_value(),
                    slice.len() as c_int,
                    slice.as_ptr() as *const VALUE,
                    kw_splat as c_int,
                ))
            })
            .and_then(TryConvert::try_convert)
        }
    }

    /// Resume the execution of `self`, raising the exception `e`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby, Value, prelude::*};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let fiber = ruby.fiber_new(Default::default(), move |ruby, _args, _block| {
    ///         assert!(ruby.fiber_yield::<_, Value>(()).is_err());
    ///     })?;
    ///
    ///     let _: Value = fiber.resume(())?;
    ///     let _: Value = fiber.raise(ruby.exception_runtime_error().new_instance(("oh no!",))?)?;
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn raise<T>(self, e: Exception) -> Result<T, Error>
    where
        T: TryConvert,
    {
        unsafe {
            protect(|| {
                #[cfg(ruby_lte_3_4)]
                let e = &e.as_rb_value() as *const VALUE;
                #[cfg(ruby_gt_3_4)]
                let e = &mut e.as_rb_value() as *mut VALUE;
                Value::new(rb_fiber_raise(self.as_rb_value(), 1, e))
            })
            .and_then(TryConvert::try_convert)
        }
    }
}

impl fmt::Display for Fiber {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for Fiber {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl IntoValue for Fiber {
    #[inline]
    fn into_value_with(self, _: &Ruby) -> Value {
        self.0.as_value()
    }
}

impl Object for Fiber {}

unsafe impl private::ReprValue for Fiber {}

impl ReprValue for Fiber {}

impl TryConvert for Fiber {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Self::from_value(val).ok_or_else(|| {
            Error::new(
                Ruby::get_with(val).exception_type_error(),
                format!("no implicit conversion of {} into Fiber", unsafe {
                    val.classname()
                },),
            )
        })
    }
}

/// Options for initialising Fiber-local storage.
pub enum Storage {
    /// Inherit the storage from the current Fiber.
    Inherit,
    /// Initialise a new empty storage when needed.
    #[cfg(any(ruby_gte_3_2, docsrs))]
    #[cfg_attr(docsrs, doc(cfg(ruby_gte_3_2)))]
    Lazy,
    /// Use the given Hash as the Fiber's storage.
    #[cfg(any(ruby_gte_3_2, docsrs))]
    #[cfg_attr(docsrs, doc(cfg(ruby_gte_3_2)))]
    Use(RHash),
}

#[cfg(ruby_gte_3_2)]
impl Storage {
    unsafe fn as_rb_value(&self) -> VALUE {
        unsafe {
            #[cfg(ruby_gte_3_2)]
            let ruby = Ruby::get_unchecked();
            match self {
                Self::Inherit => QUNDEF.as_value().as_rb_value(),
                #[cfg(ruby_gte_3_2)]
                Self::Lazy => ruby.qnil().as_rb_value(),
                #[cfg(ruby_gte_3_2)]
                Self::Use(hash) => hash.as_rb_value(),
            }
        }
    }
}

impl Default for Storage {
    fn default() -> Self {
        Self::Inherit
    }
}

fn wrap_closure<F, R>(func: F) -> (*mut Option<F>, Value)
where
    F: FnOnce(&Ruby, &[Value], Option<Proc>) -> R,
    R: BlockReturn,
{
    struct Closure<F>(Option<F>, DataType);
    unsafe impl<F> Send for Closure<F> {}
    impl<F> DataTypeFunctions for Closure<F> {
        fn mark(&self, marker: &gc::Marker) {
            // Attempt to mark any Ruby values captured in a closure.
            // Rust's closures are structs that contain all the values they
            // have captured. This reads that struct as a slice of VALUEs and
            // calls rb_gc_mark_locations which calls gc_mark_maybe which
            // marks VALUEs and ignores non-VALUEs
            marker.mark_slice(unsafe {
                slice::from_raw_parts(
                    &self.0 as *const _ as *const Value,
                    size_of::<F>() / size_of::<Value>(),
                )
            });
        }
    }

    let data_type = DataTypeBuilder::<Closure<F>>::new(c"rust closure")
        .free_immediately()
        .mark()
        .build();

    let boxed = Box::new(Closure(Some(func), data_type));
    let ptr = Box::into_raw(boxed);
    let value = unsafe {
        Value::new(rb_data_typed_object_wrap(
            0, // using 0 for the class will hide the object from ObjectSpace
            ptr as *mut _,
            (*ptr).1.as_rb_data_type() as *const _,
        ))
    };
    unsafe { (&mut (*ptr).0 as *mut Option<F>, value) }
}
