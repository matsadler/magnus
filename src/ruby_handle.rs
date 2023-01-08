use std::{cell::RefCell, error::Error, fmt, marker::PhantomData};

use rb_sys::ruby_native_thread_p;

macro_rules! get_ruby {
    () => {
        if cfg!(debug_assertions) {
            $crate::ruby_handle::RubyHandle::get().unwrap()
        } else {
            unsafe { $crate::ruby_handle::RubyHandle::get_unchecked() }
        }
    };
}

/// An error returned to indicate an attempt to interact with the Ruby API from
/// a non-Ruby thread or without aquiring the GVL.
#[derive(Debug)]
pub enum RubyUnavailableError {
    /// Current thread is not a Ruby thread.
    NonRubyThread,
    /// GVL is not locked.
    #[allow(dead_code)]
    GvlUnlocked,
}

impl fmt::Display for RubyUnavailableError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NonRubyThread => write!(f, "Current thread is not a Ruby thread."),
            Self::GvlUnlocked => write!(f, "GVL is not locked."),
        }
    }
}

impl Error for RubyUnavailableError {}

#[derive(Clone, Copy)]
enum IsRubyThread {
    Yes,
    No,
    Unknown,
}

thread_local! {
    static IS_RUBY_THREAD: RefCell<IsRubyThread> = RefCell::new(IsRubyThread::Unknown);
}

/// A handle to access Ruby's API.
///
/// Using Ruby's API requires the Ruby VM to be initalised and all access to be
/// from a Ruby-created thread.
///
/// This structure allows safe access to Ruby's API as it should only be
/// possible to aquire an instance in situations where Ruby's API is known to
/// be available.
pub struct RubyHandle(PhantomData<*mut ()>);

impl RubyHandle {
    /// Get a handle to Ruby's API.
    ///
    /// Returns a new handle to Ruby's API if it can be verified the current
    /// thread is a Ruby thread.
    ///
    /// If the Ruby API is not useable, returns `Err(RubyUnavailableError)`.
    //
    // TODO This currently does not verify the GVL is held, so will erroneously
    // return a handle when the GVL has been released.
    pub fn get() -> Result<Self, RubyUnavailableError> {
        IS_RUBY_THREAD.with(|is_ruby_thread| {
            let x = *is_ruby_thread.borrow();
            match x {
                IsRubyThread::Yes => Ok(Self(PhantomData)),
                IsRubyThread::Unknown => {
                    if unsafe { ruby_native_thread_p() } != 0 {
                        *is_ruby_thread.borrow_mut() = IsRubyThread::Yes
                    } else {
                        *is_ruby_thread.borrow_mut() = IsRubyThread::No
                    }
                    Self::get()
                }
                IsRubyThread::No => Err(RubyUnavailableError::NonRubyThread),
            }
        })
    }

    /// Get a handle to Ruby's API.
    ///
    /// # Safety
    ///
    /// This must only be called from a Ruby thread - that is one created by
    /// Ruby, or the main thread after [`embed::init`](crate::embed::init) has
    /// been called - and without having released the GVL.
    pub unsafe fn get_unchecked() -> Self {
        Self(PhantomData)
    }
}
