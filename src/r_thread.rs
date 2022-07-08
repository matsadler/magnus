//!

use {
    crate::{
        block::Proc,
        class::{thread, RClass},
        error::{protect, raise, Error},
        exception::type_error,
        method::BlockReturn,
        object::Object,
        r_time::AsRawTime,
        ruby_sys::{
            rb_thread_check_ints, rb_thread_create, rb_thread_current, rb_thread_interrupted,
            rb_thread_kill, rb_thread_local_aref, rb_thread_local_aset, rb_thread_main,
            rb_thread_run, rb_thread_schedule, rb_thread_stop, rb_thread_wait_for,
            rb_thread_wakeup, ID, VALUE,
        },
        symbol::Symbol,
        try_convert::TryConvert,
        value::{private, Id, NonZeroValue, ReprValue, Value},
    },
    std::{
        ffi::c_void,
        fmt::{Debug, Display, Error as FError, Formatter},
        ops::Deref,
        os::raw::c_uint,
        panic::{catch_unwind, AssertUnwindSafe},
        time::Duration,
    },
};

#[cfg(ruby_gte_3_0)]
use crate::ruby_sys::{
    rb_event_hook_func_t, rb_thread_add_event_hook, rb_thread_remove_event_hook,
    RUBY_EVENT_THREAD_END,
};

/// A Value pointer to a RThread struct, Ruby's internal representation of threads.
///
/// Certain functions can only be called via Ruby threads, and **not** Rust threads.
#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct RThread(NonZeroValue);

impl Deref for RThread {
    type Target = Value;
    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
    }
}

impl TryConvert for RThread {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Self::from_value(val).ok_or_else(|| {
            Error::new(
                type_error(),
                format!("no implicit conversion of {} into Thread", unsafe {
                    val.classname()
                }),
            )
        })
    }
}

impl From<RThread> for Value {
    fn from(f: RThread) -> Self {
        *f
    }
}

unsafe impl private::ReprValue for RThread {
    fn to_value(self) -> Value {
        *self
    }

    unsafe fn from_value_unchecked(val: Value) -> Self {
        Self(NonZeroValue::new_unchecked(val))
    }
}

impl ReprValue for RThread {}

impl Object for RThread {}

impl Display for RThread {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FError> {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl Debug for RThread {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FError> {
        write!(f, "{}", self.inspect())
    }
}

impl RThread {
    /// Return `Some(RThread)` if `val` is a `::Thread`, `None` otherwise.
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        if val.is_kind_of(thread()) {
            Some(Self(unsafe { NonZeroValue::new_unchecked(val) }))
        } else {
            None
        }
    }
}

impl RThread {
    /// Return current `RThread`
    pub fn current() -> Self {
        Self(unsafe { NonZeroValue::new_unchecked(Value::new(rb_thread_current())) })
    }

    /// Return `RThread` for current `::Ractor` or just the main Thread
    pub fn main() -> Self {
        Self(unsafe { NonZeroValue::new_unchecked(Value::new(rb_thread_main())) })
    }

    // # Examples
    //
    // ```
    // use {
    //   magnus::{gvl::without_gvl, r_thread::RThread},
    //   std::sync::mpsc::channel,
    // };
    //
    // let (tx, rx) = channel();
    // let _th = RThread::from_fn(move || tx.send(2).unwrap()).unwrap();
    //
    // // Since we are blocking with `rx.recv()`:
    // // You have to release GVL to allow `_th` to run.
    // let (received, cancelled) = without_gvl(move |_| rx.recv().unwrap(), None::<fn()>);
    // assert!(cancelled.is_none());
    // assert!(received.unwrap() == 2);
    // ```
    /// Create & run `RThread`.
    ///
    pub fn from_fn<F, R>(f: F) -> Result<Self, Error>
    where
        F: 'static + Send + FnOnce() -> R,
        R: BlockReturn,
    {
        unsafe extern "C" fn call<F, R>(callback: *mut c_void) -> VALUE
        where
            F: FnOnce() -> R,
            R: BlockReturn,
        {
            let closure = Box::from_raw(callback as *mut F);
            match catch_unwind(AssertUnwindSafe(closure))
                .map_err(Error::from_panic)
                .and_then(R::into_block_return)
            {
                Ok(v) => v.as_rb_value(),
                Err(e) => raise(e),
            }
        }

        let closure = Box::into_raw(Box::new(f));
        let call_func = call::<F, R> as unsafe extern "C" fn(*mut c_void) -> VALUE;

        #[cfg(ruby_lt_2_7)]
        use std::mem::transmute;
        #[cfg(ruby_lt_2_7)]
        let call_func: unsafe extern "C" fn() -> VALUE = unsafe { transmute(call_func) };

        let thread = Self(unsafe {
            NonZeroValue::new_unchecked(protect(|| {
                Value::new(rb_thread_create(Some(call_func), closure as *mut _))
            })?)
        });

        Ok(thread)
    }

    /// Checks for interrupts
    /// "call periodically" says documentation, "if your function takes a long time"
    pub fn check_interrupts() {
        unsafe { rb_thread_check_ints() }
    }

    /// Attempts to switch to another Ruby Thread for execution
    /// Blocks until GVL re-acquired
    pub fn yield_now() -> Result<(), Error> {
        protect(|| {
            unsafe { rb_thread_schedule() };
            Value::default()
        })?;
        Ok(())
    }

    /// Park current thread execution
    /// Can be resumed via `RThread.unpark`
    pub fn park() -> Result<(), Error> {
        let v = protect(|| Value::new(unsafe { rb_thread_stop() }))?;
        debug_assert!(v.is_nil());
        Ok(())
    }

    /// Sleep current Thread
    pub fn sleep(duration: Duration) -> Result<(), Error> {
        let time = duration.timeval()?;
        protect(|| {
            unsafe { rb_thread_wait_for(time) };
            Value::default()
        })?;
        Ok(())
    }
}

impl RThread {
    /// Set Fiber local storage
    ///
    /// Throw Error on Frozen Thread
    pub fn lvar_set<K, V>(&self, key: K, val: V) -> Result<(), Error>
    where
        K: Into<Id>,
        V: Into<Value>,
    {
        protect(|| {
            Value::new(unsafe {
                rb_thread_local_aset(
                    self.as_rb_value(),
                    key.into().as_rb_id(),
                    val.into().as_rb_value(),
                )
            })
        })?;
        Ok(())
    }

    /// Get Fiber local storage
    pub fn lvar_get<K, V>(&self, key: K) -> Option<Result<V, Error>>
    where
        K: Into<Id>,
        V: TryConvert,
    {
        let id = key.into();
        let val = Value::new(unsafe { rb_thread_local_aref(self.as_rb_value(), id.as_rb_id()) });
        if val.is_nil() {
            None
        } else {
            Some(val.try_convert())
        }
    }
}

impl RThread {
    /// Wake `RThread`, and call `RThread::schedule_other()`
    pub fn run(&self) -> Result<(), Error> {
        protect(|| Value::new(unsafe { rb_thread_run(self.as_rb_value()) }))?;
        Ok(())
    }

    /// Wake a parked `RThread`, return Error if `RThread` is dead.
    pub fn unpark(&self) -> Result<(), Error> {
        protect(|| Value::new(unsafe { rb_thread_wakeup(self.as_rb_value()) }))?;
        Ok(())
    }

    /// Kill `RThread`, return Error if `RThread` is current Thread.
    pub fn kill(&self) -> Result<(), Error> {
        protect(|| Value::new(unsafe { rb_thread_kill(self.as_rb_value()) }))?;
        Ok(())
    }

    /// Check if `RThread` was recently interrupted
    pub fn interrupted(&self) -> bool {
        unsafe { rb_thread_interrupted(self.as_rb_value()) != 0 }
    }
}

#[cfg(ruby_gte_3_0)]
#[allow(missing_docs)]
pub enum RubyEvents {}

type RubyEvent = c_uint;

#[cfg(ruby_gte_3_0)]
#[allow(missing_docs)]
impl RubyEvents {
    pub const THREAD_END: RubyEvent = RUBY_EVENT_THREAD_END;
}

#[cfg(ruby_gte_3_0)]
/// A token unique to `<F>` of `RThread::add_hook<F>`
#[derive(Debug, PartialEq, Eq)]
pub struct RThreadHookToken {
    ptr: rb_event_hook_func_t,
}

#[cfg(ruby_gte_3_0)]
impl RThread {
    /// Add EventHook
    ///
    /// Takes advantage of rusts's monomorphization to generate a unique `RThreadHookToken`
    pub fn add_hook<F>(&self, events: RubyEvent, mut f: F) -> RThreadHookToken
    where
        F: 'static + Send + FnMut(c_uint, Symbol, RClass, Value),
    {
        unsafe extern "C" fn on_events<F>(
            event: c_uint,
            proc: VALUE,
            _self: VALUE,
            id: ID,
            class: VALUE,
        ) {
            let block = Proc::from_rb_value_unchecked(proc);
            block
                .call::<_, Value>((event, id, class, _self))
                .expect("event hook fn should not fail");
        }

        let block = Proc::from_fn(move |argv, _| {
            debug_assert!(argv.len() == 4);
            let event = argv[0].try_convert().expect("should be event c_uint");
            let cls = RClass::from_value(argv[1]).expect("should be class");
            let sym = Symbol::from_value(argv[2]).expect("should be symbol");
            f(event, sym, cls, argv[3])
        });
        let call_func = on_events::<F> as unsafe extern "C" fn(c_uint, VALUE, VALUE, ID, VALUE);

        unsafe {
            rb_thread_add_event_hook(
                self.as_rb_value(),
                Some(call_func),
                events,
                block.as_rb_value(),
            )
        }

        RThreadHookToken {
            ptr: Some(call_func),
        }
    }

    /// Remove EventHook via Token
    pub fn remove_hook(&self, handle: RThreadHookToken) -> bool {
        let removed = unsafe { rb_thread_remove_event_hook(self.as_rb_value(), handle.ptr) };
        debug_assert!(removed == 0 || removed == 1);
        removed > 0
    }
}
