use std::{ffi::c_void, fmt};

use rb_sys::{rb_thread_create, VALUE};

use crate::{
    api::Ruby,
    error::{protect, Error},
    into_value::IntoValue,
    method::{BlockReturn, Thread as _},
    object::Object,
    r_typed_data::RTypedData,
    try_convert::TryConvert,
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
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let t = ruby.thread_create(|| 1 + 2);
    ///     rb_assert!("t.value == 3", t);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn thread_create<R>(&self, func: fn() -> R) -> Thread
    where
        R: BlockReturn,
    {
        unsafe extern "C" fn call<R>(arg: *mut c_void) -> VALUE
        where
            R: BlockReturn,
        {
            let func = std::mem::transmute::<*mut c_void, fn() -> R>(arg);
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
