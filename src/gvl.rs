//!

use {
    crate::{
        error::Error,
        ruby_sys::{rb_thread_call_with_gvl, rb_thread_call_without_gvl},
    },
    std::{
        any::Any,
        marker::PhantomData,
        os::raw::c_void,
        panic::{catch_unwind, AssertUnwindSafe},
        ptr::null_mut,
    },
};

struct ExecutionContext<F, R> {
    closure: *mut F,
    rval: Option<R>,
}

/// Rust's panic type
pub type Panic = Box<dyn 'static + Send + Any>;

/// A `!Send` guard for invoking thread local GVL operations
pub struct GVLContext(PhantomData<*const ()>);

impl GVLContext {
    fn new() -> Self {
        Self(PhantomData)
    }
}

impl GVLContext {
    /// Reacquire GVL for the duration of funtion
    pub fn with_gvl<F, R>(&mut self, f: F) -> Result<R, Error>
    where
        F: FnOnce() -> R,
    {
        unsafe extern "C" fn call<F, R>(context: *mut c_void) -> *mut c_void
        where
            F: FnOnce() -> R,
        {
            let ctx = context as *mut ExecutionContext<F, Result<R, Error>>;
            let closure = Box::from_raw((*ctx).closure);
            let r = catch_unwind(AssertUnwindSafe(closure)).map_err(Error::from_panic);
            let prev = (*ctx).rval.replace(r);
            debug_assert!(prev.is_none());
            null_mut()
        }

        let handle = Box::into_raw(Box::new(ExecutionContext {
            closure: Box::into_raw(Box::new(f)),
            rval: None::<Result<R, Error>>,
        }));
        let call_func = call::<F, R> as unsafe extern "C" fn(*mut c_void) -> *mut c_void;

        unsafe {
            rb_thread_call_with_gvl(Some(call_func), handle as *mut _);
            Box::from_raw(handle)
                .rval
                .expect("rb_thread_call_without_gvl should have finished execution")
        }
    }
}

/// Release GVL for the duration of the closure
/// See `RThread::from_fn`'s example.
///
/// Optional `cancel` fn will execute on various thread interrupts.
/// Including signals.
///
/// Pass in `None::<fn()>` if not required.
pub fn without_gvl<F, C, FR, CR>(
    f: F,
    cancel: Option<C>,
) -> (Result<FR, Error>, Option<Result<CR, Error>>)
where
    F: FnOnce(GVLContext) -> FR,
    C: FnOnce() -> CR,
{
    unsafe extern "C" fn call<F, R>(context: *mut c_void) -> *mut c_void
    where
        F: FnOnce(GVLContext) -> R,
    {
        let ctx = context as *mut ExecutionContext<F, Result<R, Panic>>;
        let closure = Box::from_raw((*ctx).closure);
        let r = catch_unwind(AssertUnwindSafe(|| (closure)(GVLContext::new())));
        let prev = (*ctx).rval.replace(r);
        debug_assert!(prev.is_none());
        null_mut()
    }

    unsafe extern "C" fn recall<F, R>(context: *mut c_void)
    where
        F: FnOnce() -> R,
    {
        let ctx = context as *mut ExecutionContext<F, Result<R, Panic>>;
        let closure = Box::from_raw((*ctx).closure);
        let r = catch_unwind(AssertUnwindSafe(closure));
        let prev = (*ctx).rval.replace(r);
        debug_assert!(prev.is_none());
    }

    let call_handle = Box::into_raw(Box::new(ExecutionContext {
        closure: Box::into_raw(Box::new(f)),
        rval: None::<Result<FR, Panic>>,
    }));
    let recall_handle = cancel.map(|c| {
        Box::into_raw(Box::new(ExecutionContext {
            closure: Box::into_raw(Box::new(c)),
            rval: None::<Result<CR, Panic>>,
        }))
    });

    let call_func = call::<F, FR> as unsafe extern "C" fn(*mut c_void) -> *mut c_void;
    let recall_func = recall_handle.map(|_| recall::<C, CR> as unsafe extern "C" fn(*mut c_void));

    unsafe {
        rb_thread_call_without_gvl(
            Some(call_func),
            call_handle as *mut _,
            recall_func,
            match recall_handle {
                Some(handle) => handle as *mut _,
                None => null_mut(),
            },
        );

        let lhs = Box::from_raw(call_handle)
            .rval
            .expect("rb_thread_call_without_gvl should have finished execution")
            .map_err(Error::from_panic);
        let rhs = recall_handle
            .and_then(|handle| Box::from_raw(handle).rval)
            .map(|rval| rval.map_err(Error::from_panic));
        (lhs, rhs)
    }
}
