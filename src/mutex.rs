//! Types for working with Ruby mutexes.

use std::{fmt, time::Duration};

use rb_sys::{
    rb_mutex_lock, rb_mutex_locked_p, rb_mutex_new, rb_mutex_sleep, rb_mutex_synchronize,
    rb_mutex_trylock, rb_mutex_unlock, VALUE,
};

use crate::{
    class::RClass,
    error::{protect, Error},
    into_value::IntoValue,
    method::{BlockReturn, Synchronize},
    object::Object,
    r_typed_data::RTypedData,
    try_convert::TryConvert,
    value::{
        private::{self, ReprValue as _},
        ReprValue, Value,
    },
    Ruby,
};

/// # `Mutex`
///
/// Functions that can be used to create Ruby `Mutex`s.
///
/// See also the [`Mutex`] type.
impl Ruby {
    /// Create a Ruby Mutex.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let lock = ruby.mutex_new();
    ///     assert!(!lock.is_locked());
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn mutex_new(&self) -> Mutex {
        unsafe { Mutex::from_rb_value_unchecked(rb_mutex_new()) }
    }
}

/// Wrapper type for a Value known to be an instance of Ruby's Mutex class.
///
/// See the [`ReprValue`] and [`Object`] traits for additional methods
/// available on this type. See [`Ruby`](Ruby#mutex) for methods to create a
/// `Mutex`.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Mutex(RTypedData);

impl Mutex {
    /// Return `Some(Mutex)` if `val` is a `Mutex`, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::eval;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(magnus::Mutex::from_value(eval("Mutex.new").unwrap()).is_some());
    /// assert!(magnus::Mutex::from_value(eval("true").unwrap()).is_none());
    /// ```
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        let mutex_class: RClass = Ruby::get_with(val)
            .class_object()
            .funcall("const_get", ("Mutex",))
            .ok()?;
        RTypedData::from_value(val)
            .filter(|_| val.is_kind_of(mutex_class))
            .map(Self)
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        Self(RTypedData::from_rb_value_unchecked(val))
    }

    /// Returns whether any threads currently hold the lock.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let lock = ruby.mutex_new();
    ///     assert!(!lock.is_locked());
    ///
    ///     lock.lock()?;
    ///     assert!(lock.is_locked());
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn is_locked(self) -> bool {
        unsafe { Value::new(rb_mutex_locked_p(self.as_rb_value())).to_bool() }
    }

    /// Attempts to acquire the lock.
    ///
    /// This method does not block. Returns true if the lock can be acquired,
    /// false otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let lock = ruby.mutex_new();
    ///
    ///     assert!(lock.trylock());
    ///     assert!(lock.is_locked());
    ///
    ///     assert!(!lock.trylock());
    ///     assert!(lock.is_locked());
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn trylock(self) -> bool {
        unsafe { Value::new(rb_mutex_trylock(self.as_rb_value())).to_bool() }
    }

    /// Acquires the lock.
    ///
    /// This method will block the current thread until the lock can be
    /// acquired. Returns `Err` on deadlock.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let lock = ruby.mutex_new();
    ///
    ///     lock.lock()?;
    ///     assert!(lock.is_locked());
    ///
    ///     assert!(lock.lock().is_err());
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn lock(self) -> Result<(), Error> {
        protect(|| unsafe { Value::new(rb_mutex_lock(self.as_rb_value())) })?;
        Ok(())
    }

    /// Release the lock.
    ///
    /// Returns `Err` if the current thread does not own the lock.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let lock = ruby.mutex_new();
    ///     lock.lock()?;
    ///     assert!(lock.is_locked());
    ///
    ///     lock.unlock()?;
    ///     assert!(!lock.is_locked());
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn unlock(self) -> Result<(), Error> {
        protect(|| unsafe { Value::new(rb_mutex_unlock(self.as_rb_value())) })?;
        Ok(())
    }

    /// Release the lock for `timeout`, reaquiring it on wakeup.
    ///
    /// Returns `Err` if the current thread does not own the lock.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::time::Duration;
    ///
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let lock = ruby.mutex_new();
    ///     lock.lock()?;
    ///     lock.sleep(Some(Duration::from_millis(10)))?;
    ///     lock.unlock()?;
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn sleep(self, timeout: Option<Duration>) -> Result<(), Error> {
        let ruby = Ruby::get_with(self);
        protect(|| unsafe {
            Value::new(rb_mutex_sleep(
                self.as_rb_value(),
                ruby.into_value(timeout.map(|d| d.as_secs_f64()))
                    .as_rb_value(),
            ))
        })?;
        Ok(())
    }

    /// Acquires the lock, runs `func`, then releases the lock.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby, Value};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let lock = ruby.mutex_new();
    ///     let mut i = 0;
    ///     let _: Value = lock.synchronize(|| i += 1)?;
    ///     assert_eq!(1, i);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn synchronize<F, R, T>(self, func: F) -> Result<T, Error>
    where
        F: FnOnce() -> R,
        R: BlockReturn,
        T: TryConvert,
    {
        unsafe extern "C" fn call<F, R>(arg: VALUE) -> VALUE
        where
            F: FnOnce() -> R,
            R: BlockReturn,
        {
            let closure = (*(arg as *mut Option<F>)).take().unwrap();
            closure.call_handle_error().as_rb_value()
        }

        protect(|| unsafe {
            let mut some_func = Some(func);
            let closure = &mut some_func as *mut Option<F> as VALUE;
            Value::new(rb_mutex_synchronize(
                self.as_rb_value(),
                Some(call::<F, R>),
                closure,
            ))
        })
        .and_then(TryConvert::try_convert)
    }
}

impl fmt::Display for Mutex {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for Mutex {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl IntoValue for Mutex {
    #[inline]
    fn into_value_with(self, _: &Ruby) -> Value {
        self.0.as_value()
    }
}

impl Object for Mutex {}

unsafe impl private::ReprValue for Mutex {}

impl ReprValue for Mutex {}

impl TryConvert for Mutex {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Self::from_value(val).ok_or_else(|| {
            Error::new(
                Ruby::get_with(val).exception_type_error(),
                format!("no implicit conversion of {} into Mutex", unsafe {
                    val.classname()
                },),
            )
        })
    }
}
