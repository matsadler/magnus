use std::{ffi::c_void, fmt, mem::size_of, slice};

use rb_sys::{
    rb_data_typed_object_wrap, rb_thread_create, rb_thread_current, rb_thread_main,
    rb_thread_schedule, VALUE,
};

use crate::{
    api::Ruby,
    data_type_builder,
    error::{protect, Error},
    gc,
    into_value::IntoValue,
    method::{BlockReturn, Thread as _},
    object::Object,
    r_typed_data::RTypedData,
    try_convert::TryConvert,
    typed_data::{DataType, DataTypeFunctions},
    value::{
        private::{self, ReprValue as _},
        ReprValue, Value,
    },
};

/// # `Thread`
///
/// Functions that can be used to create Ruby `Thread`s.
///
/// See also the [`Thread`] type.
impl Ruby {
    /// Create a Ruby thread.
    ///
    /// As `func` is a function pointer, only functions and closures that do
    /// not capture any variables are permitted. For more flexibility (at the
    /// cost of allocating) see
    /// [`thread_create_from_fn`](Ruby::thread_create_from_fn).
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let t = ruby.thread_create(|_ruby| 1 + 2);
    ///     rb_assert!("t.value == 3", t);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn thread_create<R>(&self, func: fn(&Ruby) -> R) -> Thread
    where
        R: BlockReturn,
    {
        unsafe extern "C" fn call<R>(arg: *mut c_void) -> VALUE
        where
            R: BlockReturn,
        {
            let func = std::mem::transmute::<*mut c_void, fn(&Ruby) -> R>(arg);
            func.call_handle_error().as_rb_value()
        }

        let call_func = call::<R> as unsafe extern "C" fn(arg: *mut c_void) -> VALUE;

        unsafe {
            protect(|| {
                Thread::from_rb_value_unchecked(rb_thread_create(
                    Some(call_func),
                    func as *mut c_void,
                ))
            })
            .unwrap()
        }
    }

    /// Create a Ruby thread.
    ///
    /// See also [`thread_create`](Ruby::thread_create), which is more
    /// efficient when `func` is a function or closure that does not
    /// capture any variables.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let i = 1;
    ///     let t = ruby.thread_create_from_fn(move |_ruby| i + 2);
    ///     rb_assert!("t.value == 3", t);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn thread_create_from_fn<F, R>(&self, func: F) -> Thread
    where
        F: 'static + Send + FnOnce(&Ruby) -> R,
        R: BlockReturn,
    {
        unsafe extern "C" fn call<F, R>(arg: *mut c_void) -> VALUE
        where
            F: FnOnce(&Ruby) -> R,
            R: BlockReturn,
        {
            let closure = (*(arg as *mut Option<F>)).take().unwrap();
            closure.call_handle_error().as_rb_value()
        }

        let (closure, keepalive) = wrap_closure(func);
        let call_func = call::<F, R> as unsafe extern "C" fn(arg: *mut c_void) -> VALUE;

        let t = unsafe {
            protect(|| {
                Thread::from_rb_value_unchecked(rb_thread_create(
                    Some(call_func),
                    closure as *mut c_void,
                ))
            })
            .unwrap()
        };
        // ivar without @ prefix is invisible from Ruby
        t.ivar_set("__rust_closure", keepalive).unwrap();
        t
    }

    /// Return the currently executing thread.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{prelude::*, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let t = ruby.thread_current();
    ///     t.is_kind_of(ruby.class_thread());
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn thread_current(&self) -> Thread {
        unsafe { Thread::from_rb_value_unchecked(rb_thread_current()) }
    }

    /// Return the 'main' thread.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{prelude::*, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let t = ruby.thread_main();
    ///     t.is_kind_of(ruby.class_thread());
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn thread_main(&self) -> Thread {
        unsafe { Thread::from_rb_value_unchecked(rb_thread_main()) }
    }

    /// Attempt to schedule another thread.
    ///
    /// This function blocks until the current thread is re-scheduled.
    pub fn thread_schedule(&self) {
        unsafe { rb_thread_schedule() };
    }
}

/// Wrapper type for a Value known to be an instance of Ruby's Thread class.
///
/// See the [`ReprValue`] and [`Object`] traits for additional methods
/// available on this type. See [`Ruby`](Ruby#thread) for methods to create a
/// `Thread`.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Thread(RTypedData);

impl Thread {
    /// Return `Some(Thread)` if `val` is an `Thread`, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::eval;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(magnus::Thread::from_value(eval("Thread.new {1 + 2}").unwrap()).is_some());
    /// assert!(magnus::Thread::from_value(eval("Proc.new {1 + 2}").unwrap()).is_none());
    /// ```
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        RTypedData::from_value(val)
            .filter(|_| val.is_kind_of(Ruby::get_with(val).class_thread()))
            .map(Self)
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        Self(RTypedData::from_rb_value_unchecked(val))
    }
}

impl fmt::Display for Thread {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for Thread {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl IntoValue for Thread {
    #[inline]
    fn into_value_with(self, _: &Ruby) -> Value {
        self.0.as_value()
    }
}

impl Object for Thread {}

unsafe impl private::ReprValue for Thread {}

impl ReprValue for Thread {}

impl TryConvert for Thread {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Self::from_value(val).ok_or_else(|| {
            Error::new(
                Ruby::get_with(val).exception_type_error(),
                format!("no implicit conversion of {} into Thread", unsafe {
                    val.classname()
                },),
            )
        })
    }
}

/// Wrap a closure in a Ruby object with no class.
///
/// This effectivly makes the closure's lifetime managed by Ruby. It will be
/// dropped when the returned `Value` is garbage collected.
fn wrap_closure<F, R>(func: F) -> (*mut Option<F>, Value)
where
    F: FnOnce(&Ruby) -> R,
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
