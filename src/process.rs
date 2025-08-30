//! Types for working with processes.
//!
//! See also [`Ruby`](Ruby#process) for functions for working with processes.

#[cfg(unix)]
use std::os::unix::process::ExitStatusExt;
#[cfg(windows)]
use std::os::windows::process::ExitStatusExt;
use std::{ffi::c_int, num::NonZeroU32, process::ExitStatus, ptr::null};

use rb_sys::{rb_sys_fail, rb_waitpid};

use crate::{
    api::Ruby,
    error::{Error, protect},
};

/// # Process
///
/// Functions for working with processes.
impl Ruby {
    /// Wait for a process.
    ///
    /// This function releases Ruby's Global VM Lock (GVL), so while it will
    /// block the current thread, other Ruby threads can be scheduled.
    ///
    /// Returns the Process ID (PID) of the process waited, and its exit status.
    ///
    /// If the `NOHANG` flag is passed this function will not block, instead it
    /// will clean up an exited child process if there is one, or returns
    /// `None` if there is no exited child process.
    ///
    /// If the `UNTRACED` flag is passed, this function will also return
    /// stopped processes (e.g. that can be resumed), not only exited processes.
    /// For these stopped processes the exit status will be reported as
    /// successful, although they have not yet exited.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::process::Command;
    ///
    /// use magnus::{Error, Ruby, process::WaitTarget};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let child = Command::new("ls").spawn().unwrap();
    ///     let (pid, status) = ruby
    ///         .waitpid(WaitTarget::ChildPid(child.id()), Default::default())?
    ///         .unwrap();
    ///     assert_eq!(child.id(), pid.get());
    ///     assert!(status.success());
    ///
    ///     Ok(())
    /// }
    /// # #[cfg(unix)]
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn waitpid(
        &self,
        pid: WaitTarget,
        flags: Flags,
    ) -> Result<Option<(NonZeroU32, ExitStatus)>, Error> {
        let mut out_pid = 0;
        let mut status: c_int = 0;
        protect(|| unsafe {
            out_pid = rb_waitpid(pid.to_i32() as _, &mut status as *mut c_int, flags.0);
            if out_pid < 0 {
                rb_sys_fail(null());
            }
            self.qnil()
        })?;
        Ok(NonZeroU32::new(out_pid as u32).map(|pid| (pid, ExitStatus::from_raw(status as _))))
    }
}

#[cfg(not(any(target_os = "solaris", target_os = "illumos")))]
const WNOHANG: c_int = 0x00000001;
#[cfg(any(target_os = "solaris", target_os = "illumos"))]
const WNOHANG: c_int = 0x40;

#[cfg(not(any(target_os = "solaris", target_os = "illumos")))]
const WUNTRACED: c_int = 0x00000002;
#[cfg(any(target_os = "solaris", target_os = "illumos"))]
const WUNTRACED: c_int = 0x04;

/// Argument type for [`Ruby::waitpid`].
#[derive(Clone, Copy)]
pub enum WaitTarget {
    /// Wait for the given child process
    ChildPid(u32),
    /// Wait for any child process with the process group of the current
    /// process.
    ProcessGroup, // 0
    /// Wait for any child process.
    AnyChild, // -1
    /// Wait for any child process with the given process group.
    ChildProcessGroup(u32), // negative
}

impl WaitTarget {
    fn to_i32(self) -> i32 {
        match self {
            Self::ChildPid(pid) => pid as i32,
            Self::ProcessGroup => 0,
            Self::AnyChild => -1,
            Self::ChildProcessGroup(pid) => -(pid as i32),
        }
    }
}

impl Default for WaitTarget {
    fn default() -> Self {
        Self::AnyChild
    }
}

/// Argument type for [`Ruby::waitpid`].
#[derive(Clone, Copy)]
pub struct Flags(c_int);

impl Flags {
    /// An instance of `Flags` with only `NOHANG` set.
    pub const NOHANG: Self = Self::new().nohang();
    /// An instance of `Flags` with only `UNTRACED` set.
    pub const UNTRACED: Self = Self::new().untraced();

    /// Create a new `Flags` with no flags set.
    pub const fn new() -> Self {
        Self(0)
    }

    /// Set the `NOHANG` flag.
    pub const fn nohang(self) -> Self {
        Self(self.0 | WNOHANG)
    }

    /// Set the `UNTRACED` flag.
    pub const fn untraced(self) -> Self {
        Self(self.0 | WUNTRACED)
    }
}

impl Default for Flags {
    fn default() -> Self {
        Self::new()
    }
}
