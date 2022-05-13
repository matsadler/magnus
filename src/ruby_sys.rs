//! Low-level bindings to the Ruby C API.

#![allow(missing_docs)]
#![allow(dead_code)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(clippy::upper_case_acronyms)]

// see build.rs
#[cfg(not(feature = "rb-sys-interop"))]
include!(concat!(env!("OUT_DIR"), "/ruby_sys.rs"));

#[cfg(feature = "rb-sys-interop")]
pub use rb_sys::*;
