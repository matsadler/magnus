//!

use {
    crate::{
        error::{protect, Error},
        object::Object,
        ruby_sys::{
            rb_mutex_lock, rb_mutex_locked_p, rb_mutex_new, rb_mutex_trylock, rb_mutex_unlock,
        },
        value::{private, NonZeroValue, ReprValue, Value},
    },
    std::{
        fmt::{Debug, Display, Error as FError, Formatter},
        ops::Deref,
    },
};

/// A Value pointer to a RMutex struct, Ruby's internal representation of mutexes.
///
/// This is a lower level API where thread safety is not statically guaranteed.
#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct RMutex(NonZeroValue);

impl Deref for RMutex {
    type Target = Value;
    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
    }
}

impl From<RMutex> for Value {
    fn from(f: RMutex) -> Self {
        *f
    }
}

unsafe impl private::ReprValue for RMutex {
    fn to_value(self) -> Value {
        *self
    }

    unsafe fn from_value_unchecked(val: Value) -> Self {
        Self(NonZeroValue::new_unchecked(val))
    }
}

impl ReprValue for RMutex {}

impl Object for RMutex {}

impl Display for RMutex {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FError> {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl Debug for RMutex {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FError> {
        write!(f, "{}", self.inspect())
    }
}

impl Default for RMutex {
    fn default() -> Self {
        Self::new()
    }
}

/// Akin to `std::sync::MutexGuard`, owned by current thread
/// Drop to unlock
#[derive(Debug)]
pub struct RMutexGuard<'a> {
    mutex: &'a RMutex,
}

impl Drop for RMutexGuard<'_> {
    fn drop(&mut self) {
        unsafe {
            rb_mutex_unlock(self.mutex.as_rb_value());
        }
    }
}

impl RMutex {
    /// Create a new unlocked `RMutex`
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{r_mutex::RMutex};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let mutex = RMutex::new();
    /// assert!(!mutex.locked());
    /// ```
    pub fn new() -> Self {
        Self(unsafe { NonZeroValue::new_unchecked(Value::new(rb_mutex_new())) })
    }

    /// Return whether self is locked.
    pub fn locked(&self) -> bool {
        Value::new(unsafe { rb_mutex_locked_p(self.as_rb_value()) }).to_bool()
    }

    /// Attempts to accquire exclusive access to self without waiting.
    /// A locked Mutex can only be unlocked via the **same thread**.
    pub fn try_lock(&self) -> Option<RMutexGuard<'_>> {
        let locked = Value::new(unsafe { rb_mutex_trylock(self.as_rb_value()) }).to_bool();
        if locked {
            Some(RMutexGuard { mutex: &self })
        } else {
            None
        }
    }

    /// Waits to accquire exclusive access to self.
    /// A locked Mutex can only be unlocked via the **same thread**.
    ///
    /// Returns Error under recursive deadlock.
    pub fn lock(&self) -> Result<RMutexGuard<'_>, Error> {
        protect(|| Value::new(unsafe { rb_mutex_lock(self.as_rb_value()) }))?;
        Ok(RMutexGuard { mutex: &self })
    }
}
