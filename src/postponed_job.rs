//! Functions for interacting with the postponed jobs API.

use crate::Ruby;

use rb_sys::rb_postponed_job_register;
use std::ffi::{c_uint, c_void};

impl Ruby {
    /// Registers a function to be executed when the Ruby VM is safe to access
    /// (i.e. inside a signal handler or during a GC run).
    ///
    /// ```rust
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// use magnus::{Ruby, Value};
    /// use magnus::postponed_job::RegistrationError;
    /// use std::sync::atomic::{AtomicUsize, Ordering};
    ///
    /// static COUNTER: AtomicUsize = AtomicUsize::new(0);
    ///
    /// let increment_counter = || {
    ///   assert!(Ruby::get().is_ok());
    ///
    ///   COUNTER.fetch_add(1, Ordering::SeqCst);
    /// };
    ///
    /// match Ruby::postponed_job_register(increment_counter) {
    ///     Err(RegistrationError::BufferFull) => println!("Postponed job queue is full!"),
    ///     Err(e) => println!("Error registering postponed job: {}", e),
    ///     Ok(()) => println!("Postponed job registered!"),
    /// };
    ///
    /// assert_eq!(0, COUNTER.load(Ordering::SeqCst));
    /// let _: Value = magnus::eval!("sleep 0.1").unwrap();
    /// assert_eq!(1, COUNTER.load(Ordering::SeqCst));
    /// ```
    pub fn postponed_job_register<F: FnOnce()>(func: F) -> Result<(), RegistrationError> {
        let flags = 0 as c_uint;
        let trampoline = trampoline::<F> as unsafe extern "C" fn(*mut c_void);
        let boxed_func = Box::new(func);
        let boxed_func_ptr = Box::into_raw(boxed_func) as *mut c_void;
        let ret_val = unsafe { rb_postponed_job_register(flags, Some(trampoline), boxed_func_ptr) };

        match ret_val {
            0 => Err(RegistrationError::BufferFull),
            1 => Ok(()),
            v => unreachable!("rb_postponed_job_register returned an unknown value: {}", v),
        }
    }
}

/// Errors which can occur when registering a postponed job. These are
/// intentionally not Ruby exceptions, since the Ruby VM is not safe to access
/// when the error occurs.
#[non_exhaustive]
#[derive(Debug)]
pub enum RegistrationError {
    /// The postponed job queue is full, so the job could not be registered.
    BufferFull,
}

impl std::fmt::Display for RegistrationError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let msg = match self {
            RegistrationError::BufferFull => "postponed job queue is full",
        };
        write!(f, "{}", msg)
    }
}

impl std::error::Error for RegistrationError {}

unsafe extern "C" fn trampoline<F: FnOnce()>(f: *mut c_void) {
    let f: Box<F> = Box::from_raw(f as *mut F);
    f();
}
