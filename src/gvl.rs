//! Types and functions for working with Ruby's GVL (Global VM Lock).
//!
//! See also [`Ruby::nogvl`].
//!
//! # Why release the GVL?
//!
//! When Ruby runs a native function (be it Rust, C, or other native code) it
//! will hold the Global VM Lock (GVL) while that function is executing. This
//! blocks other Ruby threads from running.
//!
//! Releasing the GVL will allow a native function to run in parallel with
//! other Ruby threads, however it will lose the ability to call any Ruby APIs.
//!
//! If you have a long running pure Rust function, regardless of whether it is
//! blocking on IO or computation it likely make sense to run it without the
//! GVL to allow other Ruby threads to run.
//!
//! While it is possible to reacquire the GVL within a non-GVL function there
//! is a cost to releasing and reacquiring the GVL and for shorter running
//! functions or those that require frequent calls to Ruby APIs it may be
//! faster to never release the GVL.
//!
//! # Interrupts
//!
//! While a native function is running Ruby can not process interrupts such as
//! `Signal::trap` or `Thread#raise`. This is still the case when the GVL is
//! released. The impact of this on Ruby's [`nogvl`](Ruby::nogvl) API is
//! twofold, firstly Ruby will check for interrupts before and after running a
//! function without the GVL; second, an 'unblocking' function can be supplied
//! alongside the function to run without the GVL to signal to the non-GVL
//! function that it should end early or reacquire the GVL to process
//! interrupts.
//!
//! The exact behaviour of the pre and post-function check for interrupts can
//! be configured with the [`intr_fail`](NoGvl::intr_fail) flag.
//!
//! Interrupts will include things like a signal being sent to shut down an
//! application, if interrupts are not processed the application will not shut
//! down.
//!
//! # Unblocking
//!
//! To ensure a timely response to interrupts an unblocking function should be
//! set for any non-GVL function that is expected to run long enough to cause
//! a noticeable delay. The exact threshold for this will depend on your (or
//! your users') use case, but a good rule of thumb is anything that is
//! expected to run longer than a second.
//!
//! The unblocking function is run without the GVL and may not return an error.
//! Typically it will simply set a flag for the non-GVL function to know it has
//! been interrupted.
//!
//! ```no_run
//! use std::{
//!     sync::atomic::{AtomicBool, Ordering},
//!     time::Duration,
//! };
//!
//! use magnus::{Error, Ruby};
//!
//! fn example(ruby: &Ruby) -> Result<(), Error> {
//!     let interrupt = AtomicBool::new(false);
//!     ruby.nogvl(|_| {
//!         loop {
//!             if interrupt.load(Ordering::Acquire) {
//!                 break;
//!             }
//!             std::thread::sleep(Duration::from_millis(100));
//!         }
//!     })
//!     .unblock(|| interrupt.store(true, Ordering::Relaxed))
//!     .ubf_async_safe()
//!     .call()
//! }
//! # Ruby::init(example).unwrap()
//! ```
//!
//! Note that not all interrupts are a request to exit, and not all interrupts
//! will generate an error, if your non-GVL function will not be resumed later
//! or you only wish to return when the interrupt does generate and error then
//! you can check like so:
//!
//! ```no_run
//! # use magnus::error::OpaqueError;
//! # use std::sync::atomic::{AtomicBool, Ordering};
//! #
//! # let ruby = unsafe { magnus::embed::init() };
//! # let interrupt = AtomicBool::new(false);
//! # ruby.nogvl(|gvl| {
//! if interrupt.load(Ordering::Acquire) {
//!     // give Ruby a chance to run interrupts.
//!     // return `Err` if one generated an error (e.g. `SystemExit`)
//!     gvl.call_with_gvl(|ruby| ruby.thread_check_ints().map_err(Into::into))?;
//!     // otherwise reset the flag if we didn't return
//!     interrupt.store(false, Ordering::Release);
//! };
//! # Ok(())
//! # })
//! # .unblock(|| interrupt.store(true, Ordering::Relaxed))
//! # .ubf_async_safe()
//! # .call()
//! # .map(|r| r.map_err(|e| OpaqueError::into_error_with(e, &ruby)))
//! # .and_then(|e| e)
//! # .unwrap()
//! ```
//!
//! # `Send` bounds
//!
//! Ruby values must not be accessed within the non-GVL function. However
//! Rust's type system isn't quite expressive enough to model this, so Magnus
//! goes for the next best thing which is a [`Send`] bound on the non-GVL
//! function. As Ruby values and the [`Ruby`] type which gives access to Ruby
//! APIs are not [`Send`] they can not be used inside the GVL function.
//!
//! While this serves the purpose of preventing use of Ruby APIs within the
//! non-GVL function it is not strictly accurate as (unless the
//! [`offload_safe`](NoGvl::offload_safe) flag is set) it is run on the same
//! thread it is called on, and should permit non-[`Send`] Rust types to be
//! used within the non-GVL function.
//!
//! To work around this the [`UnsafeSend`] type is provided to smuggle
//! non-[`Send`] types into a non-GVL function. You must manually verify this
//! is safe to do so. If the non-GVL function is configured with the
//! [`offload_safe`](NoGvl::offload_safe) flag the function may be run on
//! another thread and [`Send`] bound is a hard requirement.
//!
//! The [`call_with_gvl`](GvlHandle::call_with_gvl) function shares the
//! [`Send`] bound so that it may not mutate a variable to contain a `Ruby`
//! value and has an additional [`Send`] bound on its return type so it may not
//! return a Ruby value to the non-GVL function. Like the non-GVL function the
//! `call_with_gvl` function is run on the same thread it is called on, so this
//! [`Send`] bound is not strictly accurate.
//!
//! # Reacquiring the GVL
//!
//! The function given to [`Ruby::nogvl`] is provided with a
//! [`&GvlHandle`](GvlHandle) argument that can be used to reacquire the GVL.
//! There is a cost to releasing and reacquiring the GVL and for shorter running
//! functions or those that require frequent calls to Ruby APIs it may be
//! faster to never release the GVL.
//!
//! For cases where the `&GvlHandle` can not be passed through to where it's
//! needed [`call_with_gvl`] and [`call_with_gvl_unchecked`] are available.
//! [`GvlHandle::call_with_gvl`] should be preferred where possible as it
//! avoids the additional checks that it's on a Ruby thread that
//! [`call_with_gvl`] performs.

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
    gvl_state::GvlState,
};

/// # `GVL`
///
/// Functions to work with the Ruby GVL (Global VM Lock).
impl Ruby {
    /// Run `func` in parallel with other Ruby threads.
    ///
    /// Returns a [`NoGvl`] builder type which can be used to set an unblocking
    /// function and set flags. [`NoGvl::call`] must be called to run `func`.
    ///
    /// See the [module-level documentation](crate::gvl) for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::{
    ///     sync::atomic::{AtomicBool, Ordering},
    ///     time::Duration,
    /// };
    ///
    /// use magnus::{Error, Ruby, Value, error::OpaqueError};
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
    ///     let result = ruby
    ///         .nogvl(|gvl| {
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
    ///         .offload_safe()
    ///         .call();
    ///     result
    ///         .map(|r| r.map_err(|e| OpaqueError::into_error_with(e, &ruby)))
    ///         .and_then(|e| e)
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn nogvl<F, T>(&self, func: F) -> NoGvl<'_, F, ()>
    where
        F: Send + FnOnce(&GvlHandle) -> T,
    {
        NoGvl::new(self, func)
    }

    /// Run `func` in parallel with other Ruby threads.
    ///
    /// This method is provided for the simple use case of running a function
    /// without the GVL while not needing a [`GvlHandle`] to require the GVL,
    /// not providing an unblocking function, and not setting nogvl flags. It
    /// is equivalent to `ruby.nogvl(|_| (func)()).call()`.
    ///
    /// See also [`nogvl`](Ruby::nogvl).
    ///
    /// # Examples
    ///
    /// ```
    /// use std::{
    ///     sync::{
    ///         Arc,
    ///         atomic::{AtomicBool, Ordering},
    ///     },
    ///     time::Duration,
    /// };
    ///
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     // switching to ~1 second may make it easier to play with this example
    ///     const INTERVAL: Duration = Duration::from_millis(100);
    ///
    ///     let ruby_thread_called = Arc::new(AtomicBool::new(false));
    ///     let thread_called = ruby_thread_called.clone();
    ///
    ///     ruby.thread_create_from_fn(move |ruby| {
    ///         ruby.thread_sleep(INTERVAL * 5)?;
    ///         thread_called.store(true, Ordering::Relaxed);
    ///         Ok(())
    ///     });
    ///
    ///     let nogvl_called: AtomicBool = AtomicBool::new(false);
    ///     let result = ruby.call_without_gvl(|| {
    ///         nogvl_called.store(true, Ordering::Relaxed);
    ///         std::thread::sleep(INTERVAL * 10);
    ///         assert!(ruby_thread_called.load(Ordering::Relaxed));
    ///     });
    ///     assert!(nogvl_called.load(Ordering::Relaxed));
    ///     result
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn call_without_gvl<F, T>(&self, func: F) -> Result<T, Error>
    where
        F: Send + FnOnce() -> T,
    {
        self.nogvl(|_| (func)()).call()
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

/// A builder type used to configure calling a function without the GVL.
///
/// See [`Ruby::nogvl`].
#[must_use]
pub struct NoGvl<'ruby, F, U> {
    ruby: &'ruby Ruby,
    func: F,
    unblock: U,
    flags: NoGvlFlags,
}

impl<'ruby, F, T> NoGvl<'ruby, F, ()>
where
    F: Send + FnOnce(&GvlHandle) -> T,
{
    #[inline]
    fn new(ruby: &'ruby Ruby, func: F) -> Self {
        Self {
            ruby,
            func,
            unblock: (),
            flags: NoGvlFlags::new(),
        }
    }
}

impl<'ruby, F> NoGvl<'ruby, F, ()> {
    /// Set an unblocking function to be run when an interrupt occurs.
    ///
    /// See the [module-level documentation](crate::gvl) for more details.
    ///
    /// The unblocking function may be called multiple times, if multiple
    /// interrupts occur.
    ///
    /// The unblocking function is run without the GVL so can not call Ruby
    /// APIs and may not return an error.
    ///
    /// If the unblocking function panics the panic will be propagated through
    /// [`NoGvl::call`] once the non-GVL function has finished. Once the
    /// unblocking function has panicked subsequent interrupts will not trigger
    /// the unblocking function. If both the non-GVL function and the
    /// unblocking function panic the unblocking function's panic will be lost.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::{
    ///     sync::atomic::{AtomicBool, Ordering},
    ///     time::Duration,
    /// };
    ///
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let interrupt = AtomicBool::new(false);
    ///     ruby.nogvl(|_| {
    ///         loop {
    ///             if interrupt.load(Ordering::Acquire) {
    ///                 break;
    ///             }
    ///             std::thread::sleep(Duration::from_millis(100));
    ///         }
    ///     })
    ///     .unblock(|| interrupt.store(true, Ordering::Relaxed))
    ///     .ubf_async_safe()
    ///     .call()
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn unblock<U>(self, unblock: U) -> NoGvl<'ruby, F, U>
    where
        U: Send + FnMut(),
    {
        NoGvl {
            ruby: self.ruby,
            func: self.func,
            unblock,
            flags: self.flags,
        }
    }
}

impl<'ruby, F, U> NoGvl<'ruby, F, U> {
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

    /// Set the `intr_fail` flag, skips running interrupts pre and post-non-GVL
    /// function.
    ///
    /// By default Ruby will check for and run interrupts before and after
    /// running a non-GVL function. This means the call may return an error
    /// without running the function, or return an error even though the
    /// function ran successfully.
    ///
    /// Setting `intr_fail` alters both the pre and post-function behaviour,
    /// but differently for each.
    ///
    /// With `intr_fail` set Ruby will only check for, but not run interrupts
    /// before the function. If an interrupt is pending the function will be
    /// skipped, the interrupt will not be processed, and no error generated.
    ///
    /// With `intr_fail` set the post-function check for interrupts will be
    /// skipped entirely, so a successful function will always return a
    /// successful result.
    ///
    /// This change in behaviour means the return type of [`call`](NoGvl::call)
    /// changes from `Result<T, Error>` to `Option<T>`.
    #[inline]
    pub fn intr_fail(mut self) -> NoGvlIntrFail<'ruby, F, U> {
        self.set_intr_fail();
        NoGvlIntrFail(self)
    }

    /// Set the `ubf_async_safe` flag to indicate the unblocking function is
    /// async-signal-safe.
    ///
    /// An async-signal-safe unblocking function can be run more efficiently.
    #[inline]
    pub fn ubf_async_safe(mut self) -> Self {
        self.set_ubf_async_safe();
        self
    }

    /// Set the `offload_safe` flag to allow the non-GVL function to be run on
    /// another thread.
    ///
    /// If combined with [`intr_fail`](NoGvl::intr_fail) return type of
    /// [`call`](NoGvl::call) becomes `Result<Option<T>, Error>`.
    #[inline]
    pub fn offload_safe(mut self) -> NoGvlOffload<'ruby, F, U> {
        self.set_offload_safe();
        NoGvlOffload(self)
    }
}

impl<F, U, T> NoGvl<'_, F, U>
where
    F: Send + FnOnce(&GvlHandle) -> T,
    U: Send + FnMut(),
{
    /// Run the non-GVL function.
    #[inline]
    pub fn call(self) -> Result<T, Error> {
        self.ruby
            .nogvl_impl(self.func, Some(self.unblock), self.flags)
            .map(|o| o.expect("func to have been called"))
    }
}

impl<F, T> NoGvl<'_, F, ()>
where
    F: Send + FnOnce(&GvlHandle) -> T,
{
    /// Run the non-GVL function.
    #[inline]
    pub fn call(self) -> Result<T, Error> {
        self.ruby
            .nogvl_impl(self.func, None::<fn()>, self.flags)
            .map(|o| o.expect("func to have been called"))
    }
}

/// [`NoGvl`] with the [`intr_fail`](NoGvl::intr_fail) flag set.
///
/// Setting the [`intr_fail`](NoGvl::intr_fail) flag changes the return type
/// of [`call`](NoGvl::call) so generates a new type.
#[must_use]
pub struct NoGvlIntrFail<'ruby, F, U>(NoGvl<'ruby, F, U>);

impl<'ruby, F> NoGvlIntrFail<'ruby, F, ()> {
    /// See [`NoGvl::unblock`].
    #[inline]
    pub fn unblock<U>(self, unblock: U) -> NoGvlIntrFail<'ruby, F, U>
    where
        U: Send + FnMut(),
    {
        NoGvlIntrFail(self.0.unblock(unblock))
    }
}

impl<'ruby, F, U> NoGvlIntrFail<'ruby, F, U> {
    /// See [`NoGvl::ubf_async_safe`].
    #[inline]
    pub fn ubf_async_safe(mut self) -> Self {
        self.0.set_ubf_async_safe();
        self
    }

    /// See [`NoGvl::offload_safe`].
    #[inline]
    pub fn offload_safe(mut self) -> NoGvlIntrFailOffload<'ruby, F, U> {
        self.0.set_offload_safe();
        NoGvlIntrFailOffload(self.0)
    }
}

impl<F, U, T> NoGvlIntrFail<'_, F, U>
where
    F: Send + FnOnce(&GvlHandle) -> T,
    U: Send + FnMut(),
{
    /// See [`NoGvl::call`].
    #[inline]
    pub fn call(self) -> Option<T> {
        self.0
            .ruby
            .nogvl_impl(self.0.func, Some(self.0.unblock), self.0.flags)
            .expect("no error without interrupts")
    }
}

impl<F, T> NoGvlIntrFail<'_, F, ()>
where
    F: Send + FnOnce(&GvlHandle) -> T,
{
    /// See [`NoGvl::call`].
    #[inline]
    pub fn call(self) -> Option<T> {
        self.0
            .ruby
            .nogvl_impl(self.0.func, None::<fn()>, self.0.flags)
            .expect("no error without interrupts")
    }
}

/// [`NoGvl`] with the [`offload_safe`](NoGvl::offload_safe) flag set.
///
/// Setting the [`offload_safe`](NoGvl::offload_safe) flag may change the
/// return type of [`call`](NoGvl::call) so generates a new type.
#[must_use]
pub struct NoGvlOffload<'ruby, F, U>(NoGvl<'ruby, F, U>);

impl<'ruby, F> NoGvlOffload<'ruby, F, ()> {
    /// See [`NoGvl::unblock`].
    #[inline]
    pub fn unblock<U>(self, unblock: U) -> NoGvlOffload<'ruby, F, U>
    where
        U: Send + FnMut(),
    {
        NoGvlOffload(self.0.unblock(unblock))
    }
}

impl<'ruby, F, U> NoGvlOffload<'ruby, F, U> {
    /// See [`NoGvl::intr_fail`].
    #[inline]
    pub fn intr_fail(mut self) -> NoGvlIntrFailOffload<'ruby, F, U> {
        self.0.set_intr_fail();
        NoGvlIntrFailOffload(self.0)
    }

    /// See [`NoGvl::ubf_async_safe`].
    #[inline]
    pub fn ubf_async_safe(mut self) -> Self {
        self.0.set_ubf_async_safe();
        self
    }
}

impl<F, U, T> NoGvlOffload<'_, F, U>
where
    F: Send + FnOnce(&GvlHandle) -> T,
    U: Send + FnMut(),
    T: Send,
{
    /// See [`NoGvl::call`].
    #[inline]
    pub fn call(self) -> Result<T, Error> {
        self.0
            .ruby
            .nogvl_impl(self.0.func, Some(self.0.unblock), self.0.flags)
            .map(|o| o.expect("func to have been called"))
    }
}

impl<F, T> NoGvlOffload<'_, F, ()>
where
    F: Send + FnOnce(&GvlHandle) -> T,
    T: Send,
{
    /// See [`NoGvl::call`].
    #[inline]
    pub fn call(self) -> Result<T, Error> {
        self.0
            .ruby
            .nogvl_impl(self.0.func, None::<fn()>, self.0.flags)
            .map(|o| o.expect("func to have been called"))
    }
}

/// [`NoGvl`] with both the [`intr_fail`](NoGvl::intr_fail) and
/// [`offload_safe`](NoGvl::offload_safe) flags set.
///
/// Setting the both flags changes the return type of [`call`](NoGvl::call) so
/// generates a new type.
#[must_use]
pub struct NoGvlIntrFailOffload<'ruby, F, U>(NoGvl<'ruby, F, U>);

impl<'ruby, F> NoGvlIntrFailOffload<'ruby, F, ()> {
    /// See [`NoGvl::unblock`].
    #[inline]
    pub fn unblock<U>(self, unblock: U) -> NoGvlIntrFailOffload<'ruby, F, U>
    where
        U: Send + FnMut(),
    {
        NoGvlIntrFailOffload(self.0.unblock(unblock))
    }
}

impl<F, U> NoGvlIntrFailOffload<'_, F, U> {
    /// See [`NoGvl::ubf_async_safe`].
    #[inline]
    pub fn ubf_async_safe(mut self) -> Self {
        self.0.set_ubf_async_safe();
        self
    }
}

impl<F, U, T> NoGvlIntrFailOffload<'_, F, U>
where
    F: Send + FnOnce(&GvlHandle) -> T,
    U: Send + FnMut(),
    T: Send,
{
    /// See [`NoGvl::call`].
    #[inline]
    pub fn call(self) -> Result<Option<T>, Error> {
        self.0
            .ruby
            .nogvl_impl(self.0.func, Some(self.0.unblock), self.0.flags)
    }
}

impl<F, T> NoGvlIntrFailOffload<'_, F, ()>
where
    F: Send + FnOnce(&GvlHandle) -> T,
    T: Send,
{
    /// See [`NoGvl::call`].
    #[inline]
    pub fn call(self) -> Result<Option<T>, Error> {
        self.0
            .ruby
            .nogvl_impl(self.0.func, None::<fn()>, self.0.flags)
    }
}

/// Reacquire the GVL and run the passed `func`.
///
/// Prefer `GvlHandle::call_with_gvl` or `GvlHandle::call_with_gvl_any` if
/// possible.
///
/// This function is provided for cases where it is not possible to pass
/// through the `&GvlHandle` from a [`nogvl`](Ruby::nogvl) call. This function
/// will check it its called on a Ruby thread and if the GVL is held or not,
/// the methods on [`GvlHandle`] avoid this check.
///
/// See also [`call_with_gvl_unchecked`].
///
/// If called on a non-Ruby thread returns `None`. If called when the GVL is
/// already held the passed function will be run immediately. Otherwise this
/// will block until it can acquire the GVL, then run `func`, then release the
/// GVL.
///
/// `func` and its return type have `Send` bounds to prevent Ruby values
/// leaving `func`, but `func` is in-fact run on the same thread
/// `call_with_gvl` is called on. See the
/// [module-level documentation](crate::gvl) for more details.
#[inline]
pub fn call_with_gvl<F, T>(func: F) -> Option<T>
where
    F: Send + FnOnce(&Ruby) -> T,
    T: Send,
{
    match GvlState::current() {
        GvlState::Locked => Some((func)(&unsafe { Ruby::get_unchecked() })),
        GvlState::Unlocked => Some(unsafe { call_with_gvl_unchecked(func) }),
        GvlState::NonRubyThread => None,
    }
}

/// Reacquire the GVL and run the passed `func`.
///
/// Prefer `GvlHandle::call_with_gvl` or `GvlHandle::call_with_gvl_any` if
/// possible.
///
/// This function is provided for cases where it is not possible to pass
/// through the `&GvlHandle` from a [`nogvl`](Ruby::nogvl) call. This function
/// does not check that it called on a Ruby thread and if the GVL is held or
/// not. You must ensure this function is called on a Ruby thread.
///
/// It is safe to call this with the GVL held, at the cost of a small
/// performance penalty over just calling `func` directly.
///
/// See also [`call_with_gvl`] for a safe version of this function that checks
/// it is on a Ruby thread.
///
/// `func` and its return type have `Send` bounds to prevent Ruby values
/// leaving `func`, but `func` is in-fact run on the same thread
/// `call_with_gvl_unchecked` is called on. See the
/// [module-level documentation](crate::gvl) for more details.
pub unsafe fn call_with_gvl_unchecked<F, T>(func: F) -> T
where
    F: Send + FnOnce(&Ruby) -> T,
    T: Send,
{
    struct Data<F, T> {
        closure: Option<F>,
        result: Option<T>,
        panic: Option<Box<dyn Any + Send>>,
    }

    unsafe extern "C" fn call<F, T>(data: *mut c_void) -> *mut c_void
    where
        F: Send + FnOnce(&Ruby) -> T,
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

/// A handle to reacquire the GVL from within [`Ruby::nogvl`].
pub struct GvlHandle(PhantomData<*mut ()>);

impl GvlHandle {
    /// Reacquire the GVL and run the passed `func`.
    ///
    /// This constrains the return type of `func` to `Result<T, Error>`, which
    /// is then returned as `Result<T, OpaqueError>` for ease of use and better
    /// type inference when dealing with Ruby [`Error`]s. See
    /// [`call_with_gvl_any`](GvlHandle::call_with_gvl_any) for a version of
    /// this function that does not constrain the return type.
    ///
    /// `func` and its return type have `Send` bounds to prevent Ruby values
    /// leaving `func`, but `func` is in-fact run on the same thread
    /// `call_with_gvl` is called on. See the
    /// [module-level documentation](crate::gvl) for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::sync::atomic::{AtomicBool, Ordering};
    /// use std::time::Duration;
    ///
    /// use magnus::{Error, Ruby, Value, error::OpaqueError};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     // switching to `from_secs` may make it easier to play with this example
    ///     const INTERVAL: Duration = Duration::from_millis(1);
    ///     # let nogvl_called = AtomicBool::new(false);
    ///     # let with_gvl_called = AtomicBool::new(false);
    ///
    ///     let result = ruby
    ///         .nogvl(|gvl| {
    ///             # nogvl_called.store(true, Ordering::Relaxed);
    ///             // do some work with GVL released
    ///             std::thread::sleep(INTERVAL);
    ///
    ///             // reacquire GVL
    ///             gvl.call_with_gvl(|ruby| {
    ///             # with_gvl_called.store(true, Ordering::Relaxed);
    ///                 let _: Value = ruby.eval("puts 'hi from ruby'")?;
    ///                 Ok(())
    ///             })?;
    ///
    ///             // do some work with gvl released
    ///             std::thread::sleep(INTERVAL);
    ///
    ///             Ok(())
    ///         })
    ///         .call();
    ///     # assert!(nogvl_called.load(Ordering::Relaxed));
    ///     # assert!(with_gvl_called.load(Ordering::Relaxed));
    ///     result
    ///         .map(|r| r.map_err(|e| OpaqueError::into_error_with(e, &ruby)))
    ///         .and_then(|e| e)
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn call_with_gvl<F, T>(&self, func: F) -> Result<T, OpaqueError>
    where
        F: Send + FnOnce(&Ruby) -> Result<T, Error>,
        T: Send,
    {
        self.call_with_gvl_any(|ruby| func(ruby).map_err(Into::into))
    }

    /// Reacquire the GVL and run the passed `func`.
    ///
    /// This is a version of [`call_with_gvl`](GvlHandle::call_with_gvl) that
    /// does not constrain its return value.
    /// See [`call_with_gvl`](GvlHandle::call_with_gvl) for more details.
    #[inline]
    pub fn call_with_gvl_any<F, T>(&self, func: F) -> T
    where
        F: Send + FnOnce(&Ruby) -> T,
        T: Send,
    {
        unsafe { call_with_gvl_unchecked(func) }
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

/// A wrapper that falsely claims to be [`Send`] regardless of whether the
/// contained type is.
///
/// See the [module-level documentation](crate::gvl#send-bounds) for more
/// details.
///
/// This is provided as part of [Magnus'](crate) [`gvl`][crate::gvl] module
/// specifically to work around limitations of [`Ruby::nogvl`] and
/// [`GvlHandle::call_with_gvl`]. It should not be used with any other parts of
/// Magnus, other crates, or the Rust std/core libs.
///
/// Do not take this type's existence as an encouragement to use it. It is a
/// very simple implementation and is provided so that its dangers can be
/// documented.
#[repr(transparent)]
pub struct UnsafeSend<T>(T);

unsafe impl<T> Send for UnsafeSend<T> {}

impl<T> UnsafeSend<T> {
    /// Create a new `UnsafeSend`.
    ///
    /// Note that this function is unsafe as once the value is created it is
    /// possible to move it to another thread where it could be dropped and
    /// the drop implementation for `T` run on another thread.
    ///
    /// Do no use this to transit a value through another thread back to its
    /// original thread as an error or panic in the other thread could cause it
    /// to be dropped there, potentially triggering undefined behaviour.
    ///
    /// This should only be used when it can be verified it will not be moved
    /// to another thread in the case of overly restrictive [`Send`] bounds of
    /// [`Ruby::nogvl`] and [`GvlHandle::call_with_gvl`].
    pub unsafe fn new(inner: T) -> Self {
        Self(inner)
    }

    /// Extract the value from the `UnsafeSend` container.
    ///
    /// This must be called on the same thread `self` was created on.
    pub unsafe fn into_inner(self) -> T {
        self.0
    }
}
