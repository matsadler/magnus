//! Functions for interacting with the postponed jobs API.

use std::ffi::c_void;

use rb_sys::rb_postponed_job_register;

/// Registers a function to be executed when the Ruby VM is safe to access
/// (i.e. inside a signal handler or during a GC run).
///
/// ```rust
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// use magnus::{debug::postponed_job_register, Value};
/// use std::sync::atomic::{AtomicUsize, Ordering};
///
/// static COUNTER: AtomicUsize = AtomicUsize::new(0);
///
/// let increment_counter = || {
///   COUNTER.fetch_add(1, Ordering::SeqCst);
/// };
///
/// match postponed_job_register(increment_counter) {
///     Ok(()) => println!("Postponed job registered!"),
///     Err(e) => println!("Failed to register postponed job: {}", e),
/// };
///
/// assert_eq!(0, COUNTER.load(Ordering::SeqCst));
/// let _: Value = magnus::eval!("Thread.pass").unwrap();
/// assert_eq!(1, COUNTER.load(Ordering::SeqCst));
/// ```
pub fn postponed_job_register<F: FnOnce()>(func: F) -> Result<(), PostponedJobError> {
    unsafe extern "C" fn trampoline<F: FnOnce()>(f: *mut c_void) {
        let f: Box<F> = Box::from_raw(f as *mut F);
        f();
    }

    let flags = 0;
    let boxed_func = Box::new(func);
    let boxed_func_ptr = Box::into_raw(boxed_func) as *mut c_void;
    let ret_val =
        unsafe { rb_postponed_job_register(flags, Some(trampoline::<F>), boxed_func_ptr) };

    match ret_val {
        0 => Err(PostponedJobError::new("job queue is full")),
        1 => Ok(()),
        v => unreachable!("rb_postponed_job_register returned an unknown value: {}", v),
    }
}

/// Errors which can occur when registering a postponed job. These are
/// intentionally not Ruby exceptions, since the Ruby VM is not safe to access
/// when the error occurs.
#[non_exhaustive]
#[derive(Debug)]
pub struct PostponedJobError {
    reason: &'static str,
}

impl PostponedJobError {
    fn new(reason: &'static str) -> Self {
        Self { reason }
    }
}

impl std::fmt::Display for PostponedJobError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.write_str(self.reason)
    }
}

impl std::error::Error for PostponedJobError {}

#[cfg(test)]
mod tests {
    use super::postponed_job_register;
    use rb_sys_test_helpers::ruby_test;
    use std::sync::atomic::{AtomicUsize, Ordering};

    #[ruby_test]
    fn test_postponed_jobs_properly_registered_with_ruby() {
        static COUNTER: AtomicUsize = AtomicUsize::new(0);

        fn register_job(i: usize) {
            postponed_job_register(move || {
                crate::Ruby::get().expect("should be able to get Ruby VM");
                COUNTER.fetch_add(i, Ordering::SeqCst);
            })
            .expect("should be able to register job");
        }

        #[cfg(not(windows))]
        (0..10)
            .map(|i| std::thread::spawn(move || register_job(i)))
            .for_each(|t| t.join().unwrap());

        // The Windows implementation of `postponed_job_register` has thread safety issues
        #[cfg(windows)]
        (0..10).for_each(|i| register_job(i));

        assert_eq!(0, COUNTER.load(Ordering::SeqCst));
        let _: crate::Value = crate::eval!("Thread.pass").unwrap();
        assert_eq!(45, COUNTER.load(Ordering::SeqCst));
        let _: crate::Value = crate::eval!("Thread.pass").unwrap();
        assert_eq!(45, COUNTER.load(Ordering::SeqCst));
    }

    #[ruby_test]
    fn test_postponed_job_handles_registration_errors() {
        use super::postponed_job_register;

        let max_jobs = 1000;

        static COUNTER: AtomicUsize = AtomicUsize::new(0);

        // Fill up the postponed job queue
        for _ in 0..max_jobs {
            postponed_job_register(|| {
                COUNTER.fetch_add(1, Ordering::SeqCst);
            })
            .expect("should be able to register job");
        }

        match postponed_job_register(|| {}) {
            Ok(()) => panic!("should not be able to register job"),
            Err(e) => assert_eq!(e.to_string(), "job queue is full"),
        }

        let _: crate::Value = crate::eval!("Thread.pass").unwrap();
        assert_eq!(1000, COUNTER.load(Ordering::SeqCst));

        postponed_job_register(|| {
            COUNTER.fetch_add(1, Ordering::SeqCst);
        })
        .unwrap();

        let _: crate::Value = crate::eval!("Thread.pass").unwrap();
        assert_eq!(1001, COUNTER.load(Ordering::SeqCst));
    }
}
