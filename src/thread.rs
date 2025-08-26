use std::{fmt, mem::size_of, os::raw::c_void, slice, time::Duration};

#[allow(deprecated)]
use rb_sys::rb_thread_fd_close;
use rb_sys::{
    VALUE, rb_data_typed_object_wrap, rb_thread_alone, rb_thread_check_ints, rb_thread_create,
    rb_thread_current, rb_thread_fd_writable, rb_thread_interrupted, rb_thread_kill,
    rb_thread_local_aref, rb_thread_local_aset, rb_thread_main, rb_thread_run, rb_thread_schedule,
    rb_thread_sleep_deadly, rb_thread_sleep_forever, rb_thread_wait_fd, rb_thread_wait_for,
    rb_thread_wakeup, rb_thread_wakeup_alive, timeval,
};

use crate::{
    api::Ruby,
    data_type_builder,
    error::{Error, protect},
    gc,
    into_value::IntoValue,
    method::{BlockReturn, Thread as _},
    object::Object,
    r_file::fd::AsRawFd,
    r_typed_data::RTypedData,
    try_convert::TryConvert,
    typed_data::{DataType, DataTypeFunctions},
    value::{
        IntoId, ReprValue, Value,
        private::{self, ReprValue as _},
    },
};

/// # `Thread`
///
/// Functions to create and work with Ruby `Thread`s.
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
    /// use magnus::{Error, Ruby, rb_assert};
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
            unsafe {
                let func = std::mem::transmute::<*mut c_void, fn(&Ruby) -> R>(arg);
                func.call_handle_error().as_rb_value()
            }
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
    /// use magnus::{Error, Ruby, rb_assert};
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
            unsafe {
                let closure = (*(arg as *mut Option<F>)).take().unwrap();
                closure.call_handle_error().as_rb_value()
            }
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
    /// use magnus::{Error, Ruby, prelude::*};
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
    /// use magnus::{Error, Ruby, prelude::*};
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

    /// Blocks until the given file descriptor is readable.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(unix)]
    /// # {
    /// use std::{
    ///     io::{Read, Write},
    ///     net::Shutdown,
    ///     os::unix::net::UnixStream,
    /// };
    ///
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let (mut a, mut b) = UnixStream::pair().unwrap();
    ///     a.write_all(b"hello, world!").unwrap();
    ///     a.shutdown(Shutdown::Both).unwrap();
    ///
    ///     b.set_nonblocking(true).unwrap();
    ///     ruby.thread_wait_fd(&b)?;
    ///
    ///     let mut s = String::new();
    ///     b.read_to_string(&mut s).unwrap();
    ///     assert_eq!(s, "hello, world!");
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// # }
    /// ```
    pub fn thread_wait_fd<T>(&self, fd: &T) -> Result<(), Error>
    where
        T: AsRawFd,
    {
        let fd = fd.as_raw_fd();
        protect(|| {
            unsafe { rb_thread_wait_fd(fd) };
            self.qnil()
        })?;
        Ok(())
    }

    /// Blocks until the given file descriptor is writable.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(unix)]
    /// # {
    /// use std::{
    ///     io::{Read, Write},
    ///     net::Shutdown,
    ///     os::unix::net::UnixStream,
    /// };
    ///
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let (mut a, mut b) = UnixStream::pair().unwrap();
    ///
    ///     a.set_nonblocking(true).unwrap();
    ///     ruby.thread_fd_writable(&a)?;
    ///     a.write_all(b"hello, world!").unwrap();
    ///     a.shutdown(Shutdown::Both).unwrap();
    ///
    ///     let mut s = String::new();
    ///     b.read_to_string(&mut s).unwrap();
    ///     assert_eq!(s, "hello, world!");
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// # }
    /// ```
    pub fn thread_fd_writable<T>(&self, fd: &T) -> Result<(), Error>
    where
        T: AsRawFd,
    {
        let fd = fd.as_raw_fd();
        protect(|| {
            unsafe { rb_thread_fd_writable(fd) };
            self.qnil()
        })?;
        Ok(())
    }

    /// Schedules any Ruby threads waiting on `fd`, notifying them that `fd`
    /// has been closed.
    ///
    /// Blocks until all threads waiting on `fd` have woken up.
    #[deprecated(note = "No-op as of Ruby 3.5")]
    pub fn thread_fd_close<T>(&self, fd: &T) -> Result<(), Error>
    where
        T: AsRawFd,
    {
        let fd = fd.as_raw_fd();
        protect(|| {
            unsafe {
                #[allow(deprecated)]
                rb_thread_fd_close(fd)
            };
            self.qnil()
        })?;
        Ok(())
    }

    /// Checks if the current thread is the only thread currently alive.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::time::Duration;
    ///
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     assert!(ruby.thread_alone());
    ///
    ///     ruby.thread_create_from_fn(|ruby| ruby.thread_sleep(Duration::from_secs(1)));
    ///
    ///     assert!(!ruby.thread_alone());
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn thread_alone(&self) -> bool {
        unsafe { rb_thread_alone() != 0 }
    }

    /// Blocks for the given period of time.
    ///
    /// Returns an error if sleep is interrupted by a signal.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::time::{Duration, Instant};
    ///
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let now = Instant::now();
    ///     ruby.thread_sleep(Duration::from_millis(100))?;
    ///     let elapsed = now.elapsed();
    ///     assert!(elapsed.as_millis() > 90);
    ///     assert!(elapsed.as_secs() < 1);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn thread_sleep(&self, duration: Duration) -> Result<(), Error> {
        let t = timeval {
            tv_sec: duration.as_secs() as _,
            tv_usec: duration.subsec_micros() as _,
        };
        protect(|| {
            unsafe { rb_thread_wait_for(t) };
            self.qnil()
        })?;
        Ok(())
    }

    /// Blocks indefinitely.
    ///
    /// Returns an error if sleep is interrupted by a signal.
    pub fn thread_sleep_forever(&self) -> Result<(), Error> {
        protect(|| {
            unsafe { rb_thread_sleep_forever() };
            self.qnil()
        })?;
        Ok(())
    }

    /// Blocks indefinitely.
    ///
    /// The  thread  calling  this function is considered "dead" when Ruby's
    /// deadlock checker is triggered.
    /// See also [`thread_sleep_forever`](Ruby::thread_sleep_forever).
    ///
    /// Returns an error if sleep is interrupted by a signal.
    pub fn thread_sleep_deadly(&self) -> Result<(), Error> {
        protect(|| {
            unsafe { rb_thread_sleep_deadly() };
            self.qnil()
        })?;
        Ok(())
    }

    /// Stop the current thread.
    ///
    /// The thread can later be woken up, see [`Thread::wakeup`].
    ///
    /// Returns an error if stopping the current thread would deadlock.
    pub fn thread_stop(&self) -> Result<(), Error> {
        protect(|| {
            unsafe { rb_thread_sleep_forever() };
            self.qnil()
        })?;
        Ok(())
    }

    /// Check for, and run, pending interrupts.
    ///
    /// While Ruby is running a native extension function (such as one written
    /// in Rust with Magnus) it can't process interrupts (e.g. signals or
    /// `Thread#raise` called from another thread). Periodically calling this
    /// function in any long running function will check for *and run* any
    /// queued interrupts. This will allow your long running function to be
    /// interrupted with say ctrl-c or `Timeout::timeout`.
    ///
    /// If any interrupt raises an error it will be returned as `Err`.
    ///
    /// Calling this function may execute code on another thread.
    pub fn thread_check_ints(&self) -> Result<(), Error> {
        protect(|| {
            unsafe { rb_thread_check_ints() };
            self.qnil()
        })?;
        Ok(())
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
    /// Return `Some(Thread)` if `val` is a `Thread`, `None` otherwise.
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
        unsafe { Self(RTypedData::from_rb_value_unchecked(val)) }
    }

    /// Mark `self` as eligible for scheduling.
    ///
    /// See also [`Thread::wakeup_alive`] and [`Thread::run`].
    ///
    /// The thread is not scheduled immediately, simply marked as available.
    /// The thread may also remain blocked on IO.
    ///
    /// Returns an error `self` is dead.
    pub fn wakeup(self) -> Result<(), Error> {
        let ruby = Ruby::get_with(self);
        protect(|| {
            unsafe { rb_thread_wakeup(self.as_rb_value()) };
            ruby.qnil()
        })?;
        Ok(())
    }

    /// Mark `self` as eligible for scheduling.
    ///
    /// See also [`Thread::wakeup`] and [`Thread::run`].
    ///
    /// The thread is not scheduled immediately, simply marked as available.
    /// The thread may also remain blocked on IO.
    pub fn wakeup_alive(self) {
        unsafe { rb_thread_wakeup_alive(self.as_rb_value()) };
    }

    /// Mark `self` as eligible for scheduling and invoke the thread schedular.
    ///
    /// See also [`Thread::wakeup`] and [`Thread::wakeup_alive`].
    ///
    /// There is no guarantee that `self` will be the next thread scheduled.
    ///
    /// Returns an error `self` is dead.
    pub fn run(self) -> Result<(), Error> {
        let ruby = Ruby::get_with(self);
        protect(|| {
            unsafe { rb_thread_run(self.as_rb_value()) };
            ruby.qnil()
        })?;
        Ok(())
    }

    /// Terminates `self`.
    ///
    /// Returns an error if the `self` is the current or main thread, returning
    /// this error to Ruby will end the process.
    pub fn kill(self) -> Result<(), Error> {
        let ruby = Ruby::get_with(self);
        protect(|| {
            unsafe { rb_thread_kill(self.as_rb_value()) };
            ruby.qnil()
        })?;
        Ok(())
    }

    /// Get the value for `key` from the Fiber-local storage of the Fiber
    /// currently executing on the thread `self`.
    ///
    /// When Fibers were added to Ruby this method became Fiber-local. If only
    /// a single Fiber is run on a thread then this acts exactly like
    /// thread-local storage. Ruby's C API does not expose true thread local
    /// storage.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let current = ruby.thread_current();
    ///     let val: Option<String> = current.local_aref("example")?;
    ///     assert!(val.is_none());
    ///
    ///     let other = ruby.thread_create(|ruby| {
    ///         ruby.thread_stop()?;
    ///
    ///         let val: String = ruby.thread_current().local_aref("example")?;
    ///         assert_eq!(val, "test");
    ///
    ///         Ok(())
    ///     });
    ///
    ///     current.local_aset("example", "foo")?;
    ///     other.local_aset("example", "test")?;
    ///
    ///     let val: String = current.local_aref("example")?;
    ///     assert_eq!(val, "foo");
    ///
    ///     other.run()?;
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn local_aref<I, T>(self, key: I) -> Result<T, Error>
    where
        I: IntoId,
        T: TryConvert,
    {
        T::try_convert(Value::new(unsafe {
            rb_thread_local_aref(
                self.as_rb_value(),
                key.into_id_with(&Ruby::get_with(self)).as_rb_id(),
            )
        }))
    }

    /// Set the value for `key` from the Fiber-local storage of the Fiber
    /// currently executing on the thread `self`.
    ///
    /// Returns `Err` if `self` is frozen.
    ///
    /// When Fibers were added to Ruby this method became Fiber-local. If only
    /// a single Fiber is run on a thread then this acts exactly like
    /// thread-local storage. Ruby's C API does not expose true thread local
    /// storage.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let current = ruby.thread_current();
    ///     let val: Option<String> = current.local_aref("example")?;
    ///     assert!(val.is_none());
    ///
    ///     let other = ruby.thread_create(|ruby| {
    ///         ruby.thread_stop()?;
    ///
    ///         let val: String = ruby.thread_current().local_aref("example")?;
    ///         assert_eq!(val, "test");
    ///
    ///         Ok(())
    ///     });
    ///
    ///     current.local_aset("example", "foo")?;
    ///     other.local_aset("example", "test")?;
    ///
    ///     let val: String = current.local_aref("example")?;
    ///     assert_eq!(val, "foo");
    ///
    ///     other.run()?;
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn local_aset<I, T>(self, key: I, val: T) -> Result<(), Error>
    where
        I: IntoId,
        T: IntoValue,
    {
        let ruby = Ruby::get_with(self);
        let key = key.into_id_with(&ruby);
        let val = val.into_value_with(&ruby);
        protect(|| {
            unsafe { rb_thread_local_aset(self.as_rb_value(), key.as_rb_id(), val.as_rb_value()) };
            ruby.qnil()
        })?;
        Ok(())
    }

    /// Check if `self` has been interrupted.
    ///
    /// Returns true if the thread was interrupted, false otherwise. This can
    /// be used to detect spurious wakeups.
    pub fn interrupted(self) -> bool {
        unsafe { rb_thread_interrupted(self.as_rb_value()) != 0 }
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
/// This effectively makes the closure's lifetime managed by Ruby. It will be
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
