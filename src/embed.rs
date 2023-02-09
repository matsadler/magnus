//! Helpers for use when embedding Ruby in a Rust project.

use std::{
    ffi::CString,
    sync::atomic::{AtomicBool, Ordering},
};

#[cfg(windows)]
use rb_sys::rb_w32_sysinit;
use rb_sys::{
    ruby_cleanup, ruby_exec_node, ruby_process_options, ruby_set_script_name, ruby_setup,
};

use crate::{error::protect, r_string::IntoRString, ruby_handle::RubyHandle, value::QNIL};

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

/// Performs basic initialisation of the Ruby VM.
///
/// This only initialises the core of Ruby's functionality, some features may
/// be missing or not work as expected. Generally [`init`] should be preferred,
/// but there may be some cases where it is not possible to run the full Ruby
/// initialisation sequence.
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
/// Panics if this or [`init`] are collectively called more than once.
///
/// # Examples
///
/// ```
/// let _cleanup = unsafe { magnus::embed::init() };
/// ```
#[inline(always)]
pub unsafe fn setup() -> Cleanup {
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
            Cleanup()
        }
        Err(true) => panic!("Ruby already initialized"),
        r => panic!("unexpected INIT state {:?}", r),
    }
}

/// Initialises the Ruby VM.
///
/// See also [`setup`].
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
/// Panics if this or [`setup`] are collectively called more than once.
///
/// # Examples
///
/// ```
/// let _cleanup = unsafe { magnus::embed::init() };
/// ```
#[inline(always)]
pub unsafe fn init() -> Cleanup {
    let cleanup = setup();
    init_options(&["-e", ""]);
    cleanup
}

#[inline(always)]
unsafe fn init_options(opts: &[&str]) {
    let mut argv = vec![CString::new("ruby").unwrap()];
    argv.extend(opts.iter().map(|s| CString::new(*s).unwrap()));
    let mut argv = argv
        .iter()
        .map(|cs| cs.as_ptr() as *mut _)
        .collect::<Vec<_>>();
    let mut node = 0 as _;
    protect(|| {
        node = ruby_process_options(argv.len() as i32, argv.as_mut_ptr());
        QNIL
    })
    .unwrap();
    if ruby_exec_node(node) != 0 {
        panic!("Ruby init code failed");
    };
}

impl RubyHandle {
    pub fn script<T>(&self, name: T)
    where
        T: IntoRString,
    {
        let name = name.into_r_string_with(self);
        unsafe { ruby_set_script_name(name.as_rb_value()) };
    }
}

/// Sets the current script name.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn ruby_script<T>(name: T)
where
    T: IntoRString,
{
    get_ruby!().script(name)
}
