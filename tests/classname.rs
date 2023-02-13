use magnus::{eval, prelude::*, Value};

#[test]
fn it_returns_the_class_name() {
    let _cleanup = unsafe { magnus::embed::init() };

    unsafe {
        let val: Value = eval("42").unwrap();

        assert_eq!("Integer", val.classname());
    }
}
