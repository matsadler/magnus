//! Helpers for use when embedding Ruby in a Rust project.

use std::{
    ffi::CString,
    sync::atomic::{AtomicBool, Ordering},
};

use crate::ruby_sys::{
    ruby_cleanup, ruby_exec_node, ruby_executable_node, ruby_options, ruby_set_script_name,
    ruby_setup,
};

#[cfg(windows)]
use crate::ruby_sys::rb_w32_sysinit;

use crate::r_string::RString;

/// A guard value that will run the cleanup function for the Ruby VM when
/// dropped.
pub struct Cleanup();

impl Drop for Cleanup {
    fn drop(&mut self) {
        unsafe {
            ruby_cleanup(0);
        }
    }
}

/// Initialises the Ruby VM.
///
/// Calling this function is only required when embedding Ruby in Rust. It is
/// not required when embedding Rust in Ruby, e.g. in a Ruby Gem.
///
/// # Safety
///
/// Must be called in `main()`, or at least a function higher up the stack than
/// any code calling Ruby. Must not drop Cleanup until the very end of the
/// process, after all Ruby execution has finished.
///
/// # Panics
///
/// Panics if called more than once.
///
/// # Examples
///
/// ```
/// let _cleanup = unsafe { magnus::embed::init() };
/// ```
#[inline(always)]
pub unsafe fn init() -> Cleanup {
    init_options(&["-e", ""])
}

#[inline(always)]
unsafe fn init_options(opts: &[&str]) -> Cleanup {
    static INIT: AtomicBool = AtomicBool::new(false);
    match INIT.compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst) {
        Ok(false) => {
            #[cfg(windows)]
            {
                let mut argc = 0;
                let mut argv: [*mut std::os::raw::c_char; 0] = [];
                let mut argv = argv.as_mut_ptr();
                rb_w32_sysinit(&mut argc, &mut argv);
            }

            if ruby_setup() != 0 {
                panic!("Failed to setup Ruby");
            };
            let cleanup = Cleanup();
            let mut argv = vec![CString::new("ruby").unwrap()];
            argv.extend(opts.iter().map(|s| CString::new(*s).unwrap()));
            let mut argv = argv
                .iter()
                .map(|cs| cs.as_ptr() as *mut _)
                .collect::<Vec<_>>();
            let node = ruby_options(argv.len() as i32, argv.as_mut_ptr());
            let mut status = 0;
            if ruby_executable_node(node, &mut status) == 0 {
                panic!("Ruby init code not executable");
            }
            if ruby_exec_node(node) != 0 {
                panic!("Ruby init code failed");
            };
            cleanup
        }
        Err(true) => panic!("Ruby already initialized"),
        r => panic!("unexpected INIT state {:?}", r),
    }
}

/// Sets the current script name.
pub fn ruby_script<T>(name: T)
where
    T: Into<RString>,
{
    let name = name.into();
    unsafe { ruby_set_script_name(name.as_rb_value()) };
}
