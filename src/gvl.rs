//! Functions for working with Ruby's GVL.

use std::ffi::c_void;
use std::ptr::null_mut;

use rb_sys::{rb_thread_call_with_gvl, rb_thread_call_without_gvl};

use crate::{Ruby, error::RubyUnavailableError};

impl Ruby {
    /// Acquire the GVL.
    pub fn with_gvl<T, F>(func: F) -> T
    where
        F: FnOnce(&Ruby) -> T,
    {
        match Ruby::get() {
            Ok(ruby) => func(&ruby),
            Err(RubyUnavailableError::GvlUnlocked) => {
                let mut data = CallbackData {
                    func: Some(func),
                    result: None,
                };

                unsafe {
                    rb_thread_call_with_gvl(
                        Some(call_with_gvl::<F, T>),
                        &mut data as *mut _ as *mut c_void,
                    );
                }

                data.result.unwrap()
            }
            Err(RubyUnavailableError::NonRubyThread) => {
                panic!("cannot modify GVL from non-Ruby thread")
            }
        }
    }

    /// Release the GVL.
    pub fn without_gvl<T, F>(&self, func: F) -> T
    where
        F: Send + FnOnce() -> T,
        T: Send,
    {
        let mut data = CallbackData {
            func: Some(func),
            result: None,
        };

        unsafe {
            rb_thread_call_without_gvl(
                Some(call_without_gvl::<F, T>),
                &mut data as *mut _ as *mut c_void,
                None,
                null_mut(),
            );
        }

        data.result.unwrap()
    }
}

struct CallbackData<F, T> {
    func: Option<F>,
    result: Option<T>,
}

extern "C" fn call_without_gvl<F, T>(data: *mut c_void) -> *mut c_void
where
    F: FnOnce() -> T,
{
    let data = unsafe { &mut *(data as *mut CallbackData<F, T>) };
    let func = data.func.take().unwrap();
    data.result = Some(func());
    null_mut()
}

extern "C" fn call_with_gvl<F, T>(data: *mut c_void) -> *mut c_void
where
    F: FnOnce(&Ruby) -> T,
{
    let ruby = Ruby::get().unwrap();
    let data = unsafe { &mut *(data as *mut CallbackData<F, T>) };
    let func = data.func.take().unwrap();
    data.result = Some(func(&ruby));
    null_mut()
}
