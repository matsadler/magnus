use rb_sys::ruby_native_thread_p;
#[cfg(ruby_gte_4_0)]
use rb_sys::ruby_thread_has_gvl_p;
#[cfg(ruby_lt_4_0)]
unsafe extern "C" {
    fn ruby_thread_has_gvl_p() -> ::std::ffi::c_int;
}

use crate::error::RubyUnavailableError;

#[derive(Clone, Copy)]
pub enum GvlState {
    Locked,
    Unlocked,
    NonRubyThread,
}

impl GvlState {
    pub fn current() -> Self {
        if unsafe { ruby_thread_has_gvl_p() } != 0 {
            Self::Locked
        } else if unsafe { ruby_native_thread_p() != 0 } {
            Self::Unlocked
        } else {
            Self::NonRubyThread
        }
    }

    pub(crate) fn ok<T>(self, value: T) -> Result<T, RubyUnavailableError> {
        match self {
            Self::Locked => Ok(value),
            Self::Unlocked => Err(RubyUnavailableError::GvlUnlocked),
            Self::NonRubyThread => Err(RubyUnavailableError::NonRubyThread),
        }
    }
}
