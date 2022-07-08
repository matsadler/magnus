//!

use {
    crate::{
        block::wrap_closure,
        error::{protect, raise, Error},
        exception::{type_error, ExceptionClass},
        integer::Integer,
        method::BlockReturn,
        object::Object,
        r_io::Rio,
        r_string::RString,
        r_thread::RThread,
        r_time::AsRawTime,
        ruby_sys::{
            pid_t, rb_fiber_alive_p, rb_fiber_current, rb_fiber_new, rb_fiber_raise,
            rb_fiber_resume, rb_fiber_scheduler_address_resolve, rb_fiber_scheduler_block,
            rb_fiber_scheduler_close, rb_fiber_scheduler_current_for_thread,
            rb_fiber_scheduler_get, rb_fiber_scheduler_io_wait,
            rb_fiber_scheduler_io_wait_readable, rb_fiber_scheduler_io_wait_writable,
            rb_fiber_scheduler_kernel_sleep, rb_fiber_scheduler_make_timeout,
            rb_fiber_scheduler_process_wait, rb_fiber_scheduler_set, rb_fiber_scheduler_unblock,
            rb_fiber_transfer, rb_fiber_yield, rb_obj_is_fiber, VALUE,
        },
        try_convert::{ArgList, TryConvert},
        value::{private, NonZeroValue, ReprValue, Value},
    },
    std::{
        fmt::{Debug, Display, Error as FError, Formatter},
        ops::Deref,
        os::raw::c_int,
        panic::{catch_unwind, AssertUnwindSafe},
        ptr::{null, null_mut},
        slice::from_raw_parts,
        time::Duration,
    },
};

/// A Value pointer to a `RFiber` struct, Ruby's internal representation of Fiber.
///
/// Fibers in Ruby, from Rust's perspective are structured `goto`s.
///
/// Calling `yield`, `resume` and `transfer` will escape to their respective jump
/// locations.
///
/// This means Rust functions may not actually finish execution.
#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct RFiber(NonZeroValue);

impl Deref for RFiber {
    type Target = Value;
    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
    }
}

impl TryConvert for RFiber {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Self::from_value(val).ok_or_else(|| {
            Error::new(
                type_error(),
                format!("no implicit conversion of {} into Fiber", unsafe {
                    val.classname()
                }),
            )
        })
    }
}

impl From<RFiber> for Value {
    fn from(f: RFiber) -> Self {
        *f
    }
}

unsafe impl private::ReprValue for RFiber {
    fn to_value(self) -> Value {
        *self
    }

    unsafe fn from_value_unchecked(val: Value) -> Self {
        Self(NonZeroValue::new_unchecked(val))
    }
}

impl ReprValue for RFiber {}

impl Object for RFiber {}

impl Display for RFiber {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FError> {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl Debug for RFiber {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FError> {
        write!(f, "{}", self.inspect())
    }
}

impl RFiber {
    /// Return `Some(RFiber)` if `val` is a `RFiber`, `None` otherwise.
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            Value::new(rb_obj_is_fiber(val.as_rb_value()))
                .to_bool()
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }
}

// Need a way to keep closure `FnOnce`
// Or else you can't run Futures inside of Fibers
// `FnOnce` can't be called unless `Box::from_raw`'d on
//
// Store keepalive to prevent GC from double freeing
struct ClosureBox<F> {
    closure: Option<F>,
}

impl RFiber {
    /// Create a new paused `RFiber`
    pub fn from_fn<F, R>(block: F) -> Self
    where
        F: 'static + FnOnce(&[Value]) -> R,
        R: BlockReturn,
    {
        unsafe extern "C" fn call<F, R>(
            _yielded_arg: VALUE,
            callback_arg: VALUE,
            argc: c_int,
            argv: *const VALUE,
            _blockarg: VALUE,
        ) -> VALUE
        where
            F: FnOnce(&[Value]) -> R,
            R: BlockReturn,
        {
            let cb = callback_arg as *mut ClosureBox<F>;
            let closure = (*cb).closure.take().expect("should contain block");
            match catch_unwind(AssertUnwindSafe(move || {
                let args = from_raw_parts(argv as *const Value, argc as usize);
                closure(args)
            }))
            .map_err(Error::from_panic)
            .and_then(R::into_block_return)
            {
                Ok(v) => v.as_rb_value(),
                Err(e) => raise(e),
            }
        }

        let (closure, keepalive) = wrap_closure(ClosureBox {
            closure: Some(block),
        });
        let call_func =
            call::<F, R> as unsafe extern "C" fn(VALUE, VALUE, c_int, *const VALUE, VALUE) -> VALUE;
        #[cfg(ruby_lt_2_7)]
        let call_func: unsafe extern "C" fn() -> VALUE = unsafe { std::mem::transmute(call_func) };

        let fiber = Self(unsafe {
            NonZeroValue::new_unchecked(Value::new(rb_fiber_new(Some(call_func), closure as VALUE)))
        });
        fiber.ivar_set("__rust_closure", keepalive).unwrap();

        fiber
    }

    /// Return thread specific current `RFiber`
    pub fn current() -> Self {
        Self(unsafe { NonZeroValue::new_unchecked(Value::new(rb_fiber_current())) })
    }

    /// Return whether self can be resumed, or transfered to not.
    pub fn alive(&self) -> bool {
        unsafe { Value::new(rb_fiber_alive_p(self.as_rb_value())) }.to_bool()
    }

    /// Yield control back to context that resumed Fiber.
    pub fn yield_now<A, R>(args: A) -> Result<R, Error>
    where
        A: ArgList,
        R: TryConvert,
    {
        let args = args.into_arg_list();
        let args = args.as_ref();
        protect(|| {
            Value::new(unsafe {
                rb_fiber_yield(args.len() as c_int, args.as_ptr() as *const VALUE)
            })
        })
        .and_then(R::try_convert)
    }

    /// Resume Fiber at last yield point, or start Fiber
    pub fn resume<A, R>(&self, args: A) -> Result<R, Error>
    where
        A: ArgList,
        R: TryConvert,
    {
        let args = args.into_arg_list();
        let args = args.as_ref();
        protect(|| {
            Value::new(unsafe {
                rb_fiber_resume(
                    self.as_rb_value(),
                    args.len() as c_int,
                    args.as_ptr() as *const _,
                )
            })
        })
        .and_then(R::try_convert)
    }

    /// Transfer execution to `RFiber`, suspending execution of `RFiber::current()`
    pub fn transfer<A, R>(&self, args: A) -> Result<R, Error>
    where
        A: ArgList,
        R: TryConvert,
    {
        let args = args.into_arg_list();
        let args = args.as_ref();
        protect(|| {
            Value::new(unsafe {
                rb_fiber_transfer(
                    self.as_rb_value(),
                    args.len() as c_int,
                    args.as_ptr() as *const _,
                )
            })
        })
        .and_then(R::try_convert)
    }

    /// Raise runtime error in `RFiber`
    pub fn raise<R>(&self) -> Result<R, Error>
    where
        R: TryConvert,
    {
        protect(|| {
            Value::new(unsafe { rb_fiber_raise(self.as_rb_value(), Default::default(), null()) })
        })
        .and_then(R::try_convert)
    }

    /// Raise runtime error in `RFiber` with message
    pub fn raise_with_message<M, R>(&self, msg: M) -> Result<R, Error>
    where
        M: Into<RString>,
        R: TryConvert,
    {
        let args = [msg.into().as_rb_value()];
        protect(|| {
            Value::new(unsafe {
                rb_fiber_raise(
                    self.as_rb_value(),
                    args.len() as c_int,
                    &args as *const VALUE,
                )
            })
        })
        .and_then(R::try_convert)
    }

    /// Raise ExnClass in `RFiber` with message
    pub fn raise_exn_with_message<C, M, R>(&self, cls: C, msg: M) -> Result<R, Error>
    where
        C: Into<ExceptionClass>,
        M: Into<RString>,
        R: TryConvert,
    {
        let args = [cls.into().as_rb_value(), msg.into().as_rb_value()];
        protect(|| {
            Value::new(unsafe {
                rb_fiber_raise(
                    self.as_rb_value(),
                    args.len() as c_int,
                    &args as *const VALUE,
                )
            })
        })
        .and_then(R::try_convert)
    }

    /// `Fiber.raise(...)`
    pub fn raise_args<A, R>(&self, args: A) -> Result<R, Error>
    where
        A: ArgList,
        R: TryConvert,
    {
        let args = args.into_arg_list();
        let args = args.as_ref();
        protect(|| {
            Value::new(unsafe {
                rb_fiber_raise(
                    self.as_rb_value(),
                    args.len() as c_int,
                    args.as_ptr() as *const VALUE,
                )
            })
        })
        .and_then(R::try_convert)
    }
}

/// `FiberScheduler` IO bitflags
pub mod io_flags {
    pub use crate::ruby_sys::{
        RB_WAITFD_IN as READABLE, RB_WAITFD_OUT as WRITABLE, RB_WAITFD_PRI as PRIORITY,
    };
}

/// A Value pointer to a ruby object that implements the `FiberScheduler` interface.
#[derive(Copy, Clone)]
pub struct OpaqueScheduler(NonZeroValue);

impl Deref for OpaqueScheduler {
    type Target = Value;
    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
    }
}

impl From<OpaqueScheduler> for Value {
    fn from(f: OpaqueScheduler) -> Self {
        *f
    }
}

impl Object for OpaqueScheduler {}

impl OpaqueScheduler {
    /// The `FiberScheduler` for current thread, if set.
    pub fn current() -> Option<OpaqueScheduler> {
        let value = Value::new(unsafe { rb_fiber_scheduler_get() });
        if value.is_nil() {
            None
        } else {
            Some(OpaqueScheduler(unsafe {
                NonZeroValue::new_unchecked(value)
            }))
        }
    }

    /// The `FiberScheduler` for thread, if set.
    pub fn for_thread(th: RThread) -> Option<OpaqueScheduler> {
        let value = Value::new(unsafe { rb_fiber_scheduler_current_for_thread(th.as_rb_value()) });
        if value.is_nil() {
            None
        } else {
            Some(OpaqueScheduler(unsafe {
                NonZeroValue::new_unchecked(value)
            }))
        }
    }

    /// Set `FiberScheduler` for current thread.
    pub fn set_current<S, R>(scheduler: S) -> Result<R, Error>
    where
        S: Into<Value>,
        R: TryConvert,
    {
        protect(|| {
            let sch = scheduler.into().as_rb_value();
            Value::new(unsafe { rb_fiber_scheduler_set(sch) })
        })?
        .try_convert()
    }

    /// Delegate to `FiberScheduler.close`.
    pub fn close<R>(&self) -> Result<R, Error>
    where
        R: TryConvert,
    {
        protect(|| Value::new(unsafe { rb_fiber_scheduler_close(self.as_rb_value()) }))
            .and_then(R::try_convert)
    }

    /// Delegate to `FiberScheduler.block`.
    pub fn block<B, R>(&self, blocker: B, timeout: Option<Duration>) -> Result<R, Error>
    where
        B: Into<Value>,
        R: TryConvert,
    {
        let time = timeout.map(|t| t.timeval()).transpose()?;
        protect(|| {
            Value::new(unsafe {
                rb_fiber_scheduler_block(
                    self.as_rb_value(),
                    blocker.into().as_rb_value(),
                    rb_fiber_scheduler_make_timeout(match time {
                        Some(mut t) => &mut t as *mut _,
                        None => null_mut(),
                    }),
                )
            })
        })
        .and_then(R::try_convert)
    }

    /// Delegate to `FiberScheduler.unblock`.
    pub fn unblock<B, F, R>(&self, blocker: B, fiber: F) -> Result<R, Error>
    where
        B: Into<Value>,
        F: Into<RFiber>,
        R: TryConvert,
    {
        protect(|| {
            Value::new(unsafe {
                rb_fiber_scheduler_unblock(
                    self.as_rb_value(),
                    blocker.into().as_rb_value(),
                    fiber.into().as_rb_value(),
                )
            })
        })
        .and_then(R::try_convert)
    }

    /// Delegate to `FiberScheduler.kernel_sleep`.
    pub fn kernel_sleep<R>(&self, duration: Option<Duration>) -> Result<R, Error>
    where
        R: TryConvert,
    {
        let time = duration.map(|d| d.timeval()).transpose()?;
        protect(|| {
            Value::new(unsafe {
                rb_fiber_scheduler_kernel_sleep(
                    self.as_rb_value(),
                    rb_fiber_scheduler_make_timeout(match time {
                        Some(mut t) => &mut t as *mut _,
                        None => null_mut(),
                    }),
                )
            })
        })
        .and_then(R::try_convert)
    }

    /// Delegate to `FiberScheduler.io_wait`.
    pub fn wait_io_events<E, R>(
        &self,
        io: Rio,
        events: E,
        timeout: Option<Duration>,
    ) -> Result<R, Error>
    where
        E: Into<Integer>,
        R: TryConvert,
    {
        let time = timeout.map(|t| t.timeval()).transpose()?;
        protect(|| {
            Value::new(unsafe {
                rb_fiber_scheduler_io_wait(
                    self.as_rb_value(),
                    io.as_rb_value(),
                    events.into().as_rb_value(),
                    rb_fiber_scheduler_make_timeout(match time {
                        Some(mut t) => &mut t as *mut _,
                        None => null_mut(),
                    }),
                )
            })
        })
        .and_then(R::try_convert)
    }

    /// Delegate to `FiberScheduler.io_wait`.
    pub fn wait_readable<R>(&self, io: Rio) -> Result<R, Error>
    where
        R: TryConvert,
    {
        protect(|| {
            Value::new(unsafe {
                rb_fiber_scheduler_io_wait_readable(self.as_rb_value(), io.as_rb_value())
            })
        })
        .and_then(R::try_convert)
    }

    /// Delegate to `FiberScheduler.io_wait`.
    pub fn wait_writable<R>(&self, io: Rio) -> Result<R, Error>
    where
        R: TryConvert,
    {
        protect(|| {
            Value::new(unsafe {
                rb_fiber_scheduler_io_wait_writable(self.as_rb_value(), io.as_rb_value())
            })
        })
        .and_then(R::try_convert)
    }

    /// Delegate to `FiberScheduler.address_resolve`.
    /// Return nil if `FiberScheduler` lacks `#address_resolve`
    pub fn address_resolve<S, R>(&self, hostname: S) -> Option<Result<R, Error>>
    where
        S: Into<RString>,
        R: TryConvert,
    {
        let val = protect(|| {
            Value::new(unsafe {
                rb_fiber_scheduler_address_resolve(
                    self.as_rb_value(),
                    hostname.into().as_rb_value(),
                )
            })
        });
        match val {
            Ok(val) => {
                if val.is_undef() {
                    None
                } else {
                    Some(val.try_convert())
                }
            }
            Err(e) => Some(Err(e)),
        }
    }

    /// Delegate to `FiberScheduler.process_wait`.
    pub fn wait_process<R>(&self, pid: pid_t, flags: c_int) -> Option<Result<R, Error>>
    where
        R: TryConvert,
    {
        let val = protect(|| {
            Value::new(unsafe { rb_fiber_scheduler_process_wait(self.as_rb_value(), pid, flags) })
        });

        match val {
            Ok(val) => {
                if val.is_undef() {
                    None
                } else {
                    Some(val.try_convert())
                }
            }
            Err(e) => Some(Err(e)),
        }
    }
}
