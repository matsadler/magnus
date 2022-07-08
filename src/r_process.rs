//!

use {
    crate::{
        error::Error,
        object::Object,
        ruby_sys::{rb_last_status_get, rb_last_status_set, rb_waitpid},
        value::{private, NonZeroValue, ReprValue, Value},
    },
    std::{
        fmt::{Debug, Display, Error as FError, Formatter},
        ops::Deref,
        os::raw::c_int,
    },
};

pub use crate::ruby_sys::pid_t;

/// A Value pointer to a RProcessStatus struct, Ruby's internal representation of `::Process::Status`.
#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct RProcessStatus(NonZeroValue);

impl Deref for RProcessStatus {
    type Target = Value;
    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
    }
}

impl From<RProcessStatus> for Value {
    fn from(f: RProcessStatus) -> Self {
        *f
    }
}

unsafe impl private::ReprValue for RProcessStatus {
    fn to_value(self) -> Value {
        *self
    }

    unsafe fn from_value_unchecked(val: Value) -> Self {
        Self(NonZeroValue::new_unchecked(val))
    }
}

impl ReprValue for RProcessStatus {}

impl Object for RProcessStatus {}

impl Display for RProcessStatus {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FError> {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl Debug for RProcessStatus {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FError> {
        write!(f, "{}", self.inspect())
    }
}

#[allow(missing_docs)]
#[derive(PartialEq, Eq, Hash, Copy, Clone, Debug)]
pub struct CompletedProcess {
    pid: pid_t,
    status: c_int,
}

impl RProcessStatus {
    /// `$CHILD_STATUS`
    pub fn last_in_thread() -> Option<Self> {
        unsafe {
            let val = Value::new(rb_last_status_get());
            if val.is_nil() {
                None
            } else {
                Some(Self(NonZeroValue::new_unchecked(val)))
            }
        }
    }

    /// Set `$CHILD_STATUS` for thread
    pub fn set_current_thread(proc: CompletedProcess) {
        unsafe { rb_last_status_set(proc.status, proc.pid) }
    }

    /// `::Process.waitpid`
    pub fn wait_pid(pid: pid_t, flags: c_int) -> Result<CompletedProcess, Error> {
        let mut status = c_int::min_value();
        let pid = unsafe { rb_waitpid(pid, &mut status, flags) };
        debug_assert_ne!(status, c_int::min_value());
        match pid {
            -1 | 0 => Err(Error::last_os_error()),
            _ => Ok(CompletedProcess { pid, status }),
        }
    }
}
