use std::ffi::CString;

use magnus::ruby_sys::{rb_define_global_const, rb_gc_start};
use magnus::{embed::init, eval_static, value::BoxValue};

#[inline(never)]
fn box_value() -> BoxValue {
    unsafe { BoxValue::new(eval_static(r#""foo""#).ok().unwrap()) }
}

#[test]
fn it_keeps_value_alive() {
    let _cleanup = unsafe { init() };

    // get the Value in a different stack frame and copy it to a BoxValue
    // test is invalid if this is done in this function.
    let val = box_value();

    // make some garbage
    eval_static(r#"1024.times.map {|i| "test#{i}"}"#)
        .ok()
        .unwrap();
    // run garbage collector
    unsafe {
        rb_gc_start();
    }

    // send value back to Ruby
    // TODO use nice api for this rather than ruby_sys
    let s = CString::new("FOO").ok().unwrap();
    unsafe {
        rb_define_global_const(s.as_c_str().as_ptr(), std::mem::transmute(*val));
    }

    // try and use value
    eval_static(r#"FOO + "bar""#).ok().unwrap();

    // didn't segfault? we passed!
}
