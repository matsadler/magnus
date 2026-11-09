//! Types and functions for working with Ruby's GVL (Global VM Lock).
//!
//! See also [`Ruby::nogvl`].

use std::{
    any::Any,
    ffi::{c_int, c_void},
    marker::PhantomData,
    panic::{AssertUnwindSafe, catch_unwind, resume_unwind},
    ptr,
};

#[cfg(ruby_gte_3_4)]
use rb_sys::RB_NOGVL_OFFLOAD_SAFE;
use rb_sys::{RB_NOGVL_INTR_FAIL, RB_NOGVL_UBF_ASYNC_SAFE, rb_nogvl, rb_thread_call_with_gvl};

use crate::{
    api::Ruby,
    error::{Error, OpaqueError, protect},
};

/// # `GVL`
///
/// Functions to work with the Ruby GVL (Global VM Lock).
impl Ruby {
    /// Run `func` in parallel with other Ruby threads.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::{
    ///     sync::atomic::{AtomicBool, Ordering},
    ///     time::Duration,
    /// };
    ///
    /// use magnus::{Error, Ruby, gvl::GvlHandle};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     // switching to ~1 second may make it easier to play with this example
    ///     const INTERVAL: Duration = Duration::from_millis(100);
    ///
    ///     static RUBY_THREAD_CALLED: AtomicBool = AtomicBool::new(false);
    ///     static NOGVL_CALLED: AtomicBool = AtomicBool::new(false);
    ///
    ///     ruby.thread_create(|ruby| {
    ///         ruby.thread_sleep(INTERVAL * 5)?;
    ///         RUBY_THREAD_CALLED.store(true, Ordering::Relaxed);
    ///         Ok(())
    ///     });
    ///
    ///     let result = ruby.nogvl(|| {
    ///         NOGVL_CALLED.store(true, Ordering::Relaxed);
    ///         std::thread::sleep(INTERVAL * 10);
    ///         assert!(RUBY_THREAD_CALLED.load(Ordering::Relaxed));
    ///     });
    ///     assert!(NOGVL_CALLED.load(Ordering::Relaxed));
    ///     result
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    ///
    /// ```
    /// use std::{
    ///     sync::atomic::{AtomicBool, Ordering},
    ///     time::Duration,
    /// };
    ///
    /// use magnus::{Error, Ruby, Value, error::OpaqueError, gvl::NoGvl};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     // switching to `from_secs` may make it easier to play with this example
    ///     const INTERVAL: Duration = Duration::from_millis(1);
    ///
    ///     // example of a non-erroring interrupt
    ///     // change terminal window size to trigger
    ///     # #[cfg(unix)]
    ///     let _: Value = ruby.eval("trap('WINCH') {puts 'hi'}")?;
    ///     // INT (sent with ctrl-c) is a good example of a erroring interrupt,
    ///     // generating `SystemExit`.
    ///
    ///     ruby.thread_create(|ruby| {
    ///         ruby.thread_sleep(INTERVAL * 4)?;
    ///         println!("hi from thread");
    ///         Ok(())
    ///     });
    ///
    ///     let interrupt = AtomicBool::new(false);
    ///     let result = ruby.nogvl(
    ///         NoGvl::new(|gvl| {
    ///             for i in 0..6 {
    ///                 if interrupt.load(Ordering::Acquire) {
    ///                     // give Ruby a chance to run interrupts.
    ///                     // return `Err` if one generated an error (e.g. `SystemExit`)
    ///                     gvl.call_with_gvl(|ruby| ruby.thread_check_ints().map_err(Into::into))?;
    ///                     // reset the flag if we didn't return
    ///                     interrupt.store(false, Ordering::Release);
    ///                 }
    ///                 if i == 3 {
    ///                     gvl.call_with_gvl(|ruby| {
    ///                         let _: Value = ruby.eval("puts 'hi from ruby'")?;
    ///                         Ok(())
    ///                     })?;
    ///                 }
    ///                 println!("{i}");
    ///                 std::thread::sleep(INTERVAL);
    ///             }
    ///
    ///             Ok(())
    ///         })
    ///         .unblock(|| interrupt.store(true, Ordering::Relaxed))
    ///         .ubf_async_safe()
    ///         .offload_safe(),
    ///     );
    ///     result
    ///         .map(|r| r.map_err(|e| OpaqueError::into_error_with(e, &ruby)))
    ///         .and_then(|e| e)
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn nogvl<F>(&self, func: F) -> F::Output
    where
        F: CallWithoutGvl,
    {
        func.call(self)
    }

    fn nogvl_impl<F, U, T>(
        &self,
        func: F,
        unblock: Option<U>,
        flags: NoGvlFlags,
    ) -> Result<Option<T>, Error>
    where
        F: Send + FnOnce(&GvlHandle) -> T,
        U: Send + FnMut(),
    {
        struct Data<F, T> {
            closure: Option<F>,
            result: Option<T>,
            panic: Option<Box<dyn Any + Send>>,
        }
        struct UbData<U> {
            closure: U,
            panic: Option<Box<dyn Any + Send>>,
        }

        unsafe extern "C" fn call<F, T>(data: *mut c_void) -> *mut c_void
        where
            F: Send + FnOnce(&GvlHandle) -> T,
        {
            unsafe {
                let data = &mut *(data as *mut Data<F, T>);
                if let Err(e) = catch_unwind(AssertUnwindSafe(|| {
                    data.result = Some((data.closure.take().unwrap())(&GvlHandle(PhantomData)));
                })) {
                    data.panic = Some(e);
                };
                ptr::null_mut()
            }
        }

        unsafe extern "C" fn call_unblock<U>(data: *mut c_void)
        where
            U: Send + FnMut(),
        {
            unsafe {
                let data = &mut *(data as *mut UbData<U>);
                if data.panic.is_some() {
                    return;
                }
                if let Err(e) = catch_unwind(AssertUnwindSafe(|| (data.closure)())) {
                    data.panic = Some(e);
                }
            }
        }

        let mut data = Data {
            closure: Some(func),
            result: None,
            panic: None,
        };
        let mut ub_data = unblock.map(|closure| UbData {
            closure,
            panic: None,
        });
        let res = unsafe {
            protect(|| {
                rb_nogvl(
                    Some(call::<F, T>),
                    &mut data as *mut Data<F, T> as *mut c_void,
                    ub_data.is_some().then_some(call_unblock::<U>),
                    ub_data
                        .as_mut()
                        .map(|u| u as *mut UbData<U> as *mut c_void)
                        .unwrap_or(ptr::null_mut()),
                    flags.0,
                );
                self.qnil()
            })
        };
        if let Some(e) = data.panic {
            resume_unwind(e);
        }
        if let Some(e) = ub_data.as_mut().and_then(|d| d.panic.take()) {
            resume_unwind(e);
        }
        res.map(|_| data.result)
    }
}

mod private {
    pub trait CallWithoutGvl {}
}

pub trait CallWithoutGvl: private::CallWithoutGvl {
    type Output;

    fn call(self, ruby: &Ruby) -> Self::Output;
}

#[must_use]
pub struct NoGvl<F, U> {
    func: F,
    unblock: Option<U>,
    flags: NoGvlFlags,
}

impl<F, T> NoGvl<F, fn()>
where
    F: Send + FnOnce(&GvlHandle) -> T,
{
    #[inline]
    pub fn new(func: F) -> Self {
        Self {
            func,
            unblock: None,
            flags: NoGvlFlags::new(),
        }
    }
}

impl<F, U> NoGvl<F, U> {
    #[inline]
    fn set_intr_fail(&mut self) {
        self.flags = self.flags.intr_fail();
    }

    #[inline]
    fn set_ubf_async_safe(&mut self) {
        self.flags = self.flags.ubf_async_safe();
    }

    #[inline]
    fn set_offload_safe(&mut self) {
        self.flags = self.flags.offload_safe();
    }

    #[inline]
    pub fn unblock<V>(self, unblock: V) -> NoGvl<F, V> {
        NoGvl {
            func: self.func,
            unblock: Some(unblock),
            flags: self.flags,
        }
    }

    #[inline]
    pub fn intr_fail(mut self) -> NoGvlIntrFail<F, U> {
        self.set_intr_fail();
        NoGvlIntrFail(self)
    }

    #[inline]
    pub fn ubf_async_safe(mut self) -> Self {
        self.set_ubf_async_safe();
        self
    }

    #[inline]
    pub fn offload_safe(mut self) -> NoGvlOffload<F, U> {
        self.set_offload_safe();
        NoGvlOffload(self)
    }
}

impl<F, U> private::CallWithoutGvl for NoGvl<F, U> {}

impl<F, U, T> CallWithoutGvl for NoGvl<F, U>
where
    F: Send + FnOnce(&GvlHandle) -> T,
    U: Send + FnMut(),
{
    type Output = Result<T, Error>;

    #[inline]
    fn call(self, ruby: &Ruby) -> Self::Output {
        ruby.nogvl_impl(self.func, self.unblock, self.flags)
            .map(|o| o.expect("func to have been called"))
    }
}

#[must_use]
pub struct NoGvlIntrFail<F, U>(NoGvl<F, U>);

impl<F, U> NoGvlIntrFail<F, U> {
    #[inline]
    pub fn unblock<V>(self, unblock: V) -> NoGvlIntrFail<F, V> {
        NoGvlIntrFail(self.0.unblock(unblock))
    }

    #[inline]
    pub fn ubf_async_safe(mut self) -> Self {
        self.0.set_ubf_async_safe();
        self
    }

    #[inline]
    pub fn offload_safe(mut self) -> NoGvlIntrFailOffload<F, U> {
        self.0.set_offload_safe();
        NoGvlIntrFailOffload(self.0)
    }
}

impl<F, U> private::CallWithoutGvl for NoGvlIntrFail<F, U> {}

impl<F, U, T> CallWithoutGvl for NoGvlIntrFail<F, U>
where
    F: Send + FnOnce(&GvlHandle) -> T,
    U: Send + FnMut(),
{
    type Output = Option<T>;

    #[inline]
    fn call(self, ruby: &Ruby) -> Self::Output {
        ruby.nogvl_impl(self.0.func, self.0.unblock, self.0.flags)
            .expect("no error without interrupts")
    }
}

#[must_use]
pub struct NoGvlOffload<F, U>(NoGvl<F, U>);

impl<F, U> NoGvlOffload<F, U> {
    #[inline]
    pub fn unblock<V>(self, unblock: V) -> NoGvlOffload<F, V> {
        NoGvlOffload(self.0.unblock(unblock))
    }

    #[inline]
    pub fn intr_fail(mut self) -> NoGvlIntrFailOffload<F, U> {
        self.0.set_intr_fail();
        NoGvlIntrFailOffload(self.0)
    }

    #[inline]
    pub fn ubf_async_safe(mut self) -> Self {
        self.0.set_ubf_async_safe();
        self
    }
}

impl<F, U> private::CallWithoutGvl for NoGvlOffload<F, U> {}

impl<F, U, T> CallWithoutGvl for NoGvlOffload<F, U>
where
    F: Send + FnOnce(&GvlHandle) -> T,
    U: Send + FnMut(),
{
    type Output = Result<T, Error>;

    #[inline]
    fn call(self, ruby: &Ruby) -> Self::Output {
        ruby.nogvl_impl(self.0.func, self.0.unblock, self.0.flags)
            .map(|o| o.expect("func to have been called"))
    }
}

#[must_use]
pub struct NoGvlIntrFailOffload<F, U>(NoGvl<F, U>);

impl<F, U> NoGvlIntrFailOffload<F, U> {
    #[inline]
    pub fn unblock<V>(self, unblock: V) -> NoGvlIntrFailOffload<F, V> {
        NoGvlIntrFailOffload(self.0.unblock(unblock))
    }

    #[inline]
    pub fn ubf_async_safe(mut self) -> Self {
        self.0.set_ubf_async_safe();
        self
    }
}

impl<F, U> private::CallWithoutGvl for NoGvlIntrFailOffload<F, U> {}

impl<F, U, T> CallWithoutGvl for NoGvlIntrFailOffload<F, U>
where
    F: Send + FnOnce(&GvlHandle) -> T,
    U: Send + FnMut(),
{
    type Output = Result<Option<T>, Error>;

    #[inline]
    fn call(self, ruby: &Ruby) -> Self::Output {
        ruby.nogvl_impl(self.0.func, self.0.unblock, self.0.flags)
    }
}

impl<F, T> private::CallWithoutGvl for F where F: Send + FnOnce() -> T {}

impl<F, T> CallWithoutGvl for F
where
    F: Send + FnOnce() -> T,
{
    type Output = Result<T, Error>;

    #[inline]
    fn call(self, ruby: &Ruby) -> Self::Output {
        NoGvl::new(|_| self()).call(ruby)
    }
}

/// A handle to reacquire the GVL from within [`Ruby::nogvl`].
pub struct GvlHandle(PhantomData<*mut ()>);

impl GvlHandle {
    /// Reacquire the GVL from within [`Ruby::nogvl`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::sync::atomic::{AtomicBool, Ordering};
    /// use std::time::Duration;
    ///
    /// use magnus::{Error, Ruby, Value, error::OpaqueError, gvl::NoGvl};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     // switching to `from_secs` may make it easier to play with this example
    ///     const INTERVAL: Duration = Duration::from_millis(1);
    ///     # static NOGVL_CALLED: AtomicBool = AtomicBool::new(false);
    ///     # static WITH_GVL_CALLED: AtomicBool = AtomicBool::new(false);
    ///
    ///     let result = ruby.nogvl(NoGvl::new(|gvl| {
    ///             # NOGVL_CALLED.store(true, Ordering::Relaxed);
    ///         // do some work with GVL released
    ///         std::thread::sleep(INTERVAL);
    ///
    ///         // reacquire GVL
    ///         gvl.call_with_gvl(|ruby| {
    ///                 # WITH_GVL_CALLED.store(true, Ordering::Relaxed);
    ///             let _: Value = ruby.eval("puts 'hi from ruby'")?;
    ///             Ok(())
    ///         })?;
    ///
    ///         // do some work with gvl released
    ///         std::thread::sleep(INTERVAL);
    ///
    ///         Ok(())
    ///     }));
    ///     # assert!(NOGVL_CALLED.load(Ordering::Relaxed));
    ///     # assert!(WITH_GVL_CALLED.load(Ordering::Relaxed));
    ///     result
    ///         .map(|r| r.map_err(|e| OpaqueError::into_error_with(e, &ruby)))
    ///         .and_then(|e| e)
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn call_with_gvl<F, T>(&self, func: F) -> Result<T, OpaqueError>
    where
        F: Send + FnOnce(&Ruby) -> Result<T, OpaqueError>,
        T: Send,
    {
        struct Data<F, T> {
            closure: Option<F>,
            result: Option<Result<T, OpaqueError>>,
            panic: Option<Box<dyn Any + Send>>,
        }

        unsafe extern "C" fn call<F, T>(data: *mut c_void) -> *mut c_void
        where
            F: Send + FnOnce(&Ruby) -> Result<T, OpaqueError>,
            T: Send,
        {
            unsafe {
                let data = &mut *(data as *mut Data<F, T>);
                if let Err(e) = catch_unwind(AssertUnwindSafe(|| {
                    data.result = Some((data.closure.take().unwrap())(&Ruby::get_unchecked()));
                })) {
                    data.panic = Some(e);
                };
                ptr::null_mut()
            }
        }

        let mut data = Data {
            closure: Some(func),
            result: None,
            panic: None,
        };

        unsafe {
            rb_thread_call_with_gvl(
                Some(call::<F, T>),
                &mut data as *mut Data<F, T> as *mut c_void,
            );
        }

        if let Some(e) = data.panic {
            resume_unwind(e);
        }
        data.result.unwrap()
    }
}

/// Flags for [`Ruby::nogvl`].
#[derive(Clone, Copy, Default)]
struct NoGvlFlags(c_int);

impl NoGvlFlags {
    /// Create a new `NoGvlFlags` with no flags set.
    pub const fn new() -> Self {
        Self(0)
    }

    /// Set the `INTR_FAIL` flag.
    ///
    /// Prevents [`Ruby::nogvl`] from checking interrupts. In the case of a
    /// pending interrupt `nogvl` will return `Ok(None)` without running your
    /// function. The post-function interrupt check will be skipped entirely.
    ///
    /// This allows for retrieving the results of the `nogvl` function before
    /// checking for interrupts.
    ///
    /// If supplying this to [`Ruby::nogvl`] then [`Ruby::thread_check_ints`]
    /// should be called manually once your `nogvl` function has finished.
    pub const fn intr_fail(self) -> Self {
        Self(self.0 | RB_NOGVL_INTR_FAIL as c_int)
    }

    /// Set the `UBF_ASYNC_SAFE` flag.
    ///
    /// Indicates that the unblocking function passed to [`Ruby::nogvl`] is
    /// async-signal-safe.
    pub const fn ubf_async_safe(self) -> Self {
        Self(self.0 | RB_NOGVL_UBF_ASYNC_SAFE as c_int)
    }

    /// Set the `OFFLOAD_SAFE` flag.
    ///
    /// Allows the function passed to [`Ruby::nogvl`] to be offloaded to a
    /// background thread.
    pub const fn offload_safe(self) -> Self {
        let val = self.0;
        #[cfg(ruby_gte_3_4)]
        let val = val | RB_NOGVL_OFFLOAD_SAFE as c_int;
        Self(val)
    }
}
