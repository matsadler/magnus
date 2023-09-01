use std::{fmt, mem::size_of, os::raw::c_int, slice};

#[cfg(ruby_lt_3_2)]
use rb_sys::rb_fiber_new;
#[cfg(ruby_gte_3_2)]
use rb_sys::rb_fiber_new_storage;
use rb_sys::{
    rb_data_typed_object_wrap, rb_fiber_alive_p, rb_fiber_current, rb_fiber_resume_kw,
    rb_fiber_yield_kw, VALUE,
};
#[cfg(ruby_gte_3_1)]
use rb_sys::{rb_fiber_raise, rb_fiber_transfer_kw, rb_obj_is_fiber};

#[cfg(ruby_lt_3_1)]
use crate::class::RClass;
#[cfg(ruby_gte_3_1)]
use crate::exception::Exception;
#[cfg(any(ruby_gte_3_2, docsrs))]
use crate::r_hash::RHash;
use crate::{
    api::Ruby,
    block::Proc,
    data_type_builder,
    error::{protect, Error},
    gc,
    into_value::{kw_splat, ArgList, IntoValue},
    method::{Block, BlockReturn},
    object::Object,
    r_typed_data::RTypedData,
    try_convert::TryConvert,
    typed_data::{DataType, DataTypeFunctions},
    value::{
        private::{self, ReprValue as _},
        ReprValue, Value, QUNDEF,
    },
};

impl Ruby {
    /// # Examples
    ///
    /// ```
    /// use magnus::{prelude::*, rb_assert, Error, Ruby, Value};
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
    ///     # #[cfg(ruby_gte_3_1)]
    ///     # {
    ///     rb_assert!(ruby, "fib.resume(0, 1) == 1", fib);
    ///     rb_assert!(ruby, "fib.resume == 2", fib);
    ///     rb_assert!(ruby, "fib.resume == 3", fib);
    ///     rb_assert!(ruby, "fib.resume == 5", fib);
    ///     rb_assert!(ruby, "fib.resume == 8", fib);
    ///     # }
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
            let func =
                std::mem::transmute::<VALUE, fn(&Ruby, &[Value], Option<Proc>) -> R>(callback_arg);
            func.call_handle_error(argc, argv as *const Value, Value::new(blockarg))
                .as_rb_value()
        }

        let call_func =
            call::<R> as unsafe extern "C" fn(VALUE, VALUE, c_int, *const VALUE, VALUE) -> VALUE;

        unsafe {
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

    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby, Value};
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
    ///     # #[cfg(ruby_gte_3_1)]
    ///     # {
    ///     rb_assert!(ruby, "fib.resume == 1", fib);
    ///     rb_assert!(ruby, "fib.resume == 2", fib);
    ///     rb_assert!(ruby, "fib.resume == 3", fib);
    ///     rb_assert!(ruby, "fib.resume == 5", fib);
    ///     rb_assert!(ruby, "fib.resume == 8", fib);
    ///     # }
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
            let closure = (*(callback_arg as *mut Option<F>)).take().unwrap();
            closure
                .call_handle_error(argc, argv as *const Value, Value::new(blockarg))
                .as_rb_value()
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

    pub fn fiber_current(&self) -> Fiber {
        unsafe { Fiber::from_rb_value_unchecked(rb_fiber_current()) }
    }

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

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Fiber(RTypedData);

impl Fiber {
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        #[cfg(ruby_lt_3_1)]
        let fiber = {
            let fiber_class: RClass = Ruby::get_with(val)
                .class_object()
                .funcall("const_get", ("Fiber",))
                .ok()?;
            RTypedData::from_value(val)
                .filter(|_| val.is_kind_of(fiber_class))
                .map(Self)
        };
        #[cfg(ruby_gte_3_1)]
        let fiber = unsafe {
            Value::new(rb_obj_is_fiber(val.as_rb_value()))
                .to_bool()
                .then(|| Self::from_rb_value_unchecked(val.as_rb_value()))
        };
        fiber
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        Self(RTypedData::from_rb_value_unchecked(val))
    }

    pub fn is_alive(self) -> bool {
        unsafe { Value::new(rb_fiber_alive_p(self.as_rb_value())).to_bool() }
    }

    /// # Examples
    ///
    /// ```
    /// use magnus::{prelude::*, Error, Ruby, Value};
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
    ///     # #[cfg(ruby_gte_3_1)]
    ///     # {
    ///     assert_eq!(fib.resume::<_, u64>((0, 1))?, 1);
    ///     assert_eq!(fib.resume::<_, u64>(())?, 2);
    ///     assert_eq!(fib.resume::<_, u64>(())?, 3);
    ///     assert_eq!(fib.resume::<_, u64>(())?, 5);
    ///     assert_eq!(fib.resume::<_, u64>(())?, 8);
    ///     # }
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

    #[cfg(any(ruby_gte_3_1, docsrs))]
    #[cfg_attr(docsrs, doc(cfg(ruby_gte_3_1)))]
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

    #[cfg(any(ruby_gte_3_1, docsrs))]
    #[cfg_attr(docsrs, doc(cfg(ruby_gte_3_1)))]
    pub fn raise<T>(self, e: Exception) -> Result<T, Error>
    where
        T: TryConvert,
    {
        unsafe {
            protect(|| {
                Value::new(rb_fiber_raise(
                    self.as_rb_value(),
                    1,
                    &e.as_rb_value() as *const VALUE,
                ))
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

pub enum Storage {
    Inherit,
    #[cfg(any(ruby_gte_3_2, docsrs))]
    #[cfg_attr(docsrs, doc(cfg(ruby_gte_3_2)))]
    Lazy,
    #[cfg(any(ruby_gte_3_2, docsrs))]
    #[cfg_attr(docsrs, doc(cfg(ruby_gte_3_2)))]
    Use(RHash),
}

#[cfg(ruby_gte_3_2)]
impl Storage {
    unsafe fn as_rb_value(&self) -> VALUE {
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

    let data_type = data_type_builder!(Closure<F>, "rust closure")
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
