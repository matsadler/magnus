use magnus::{Value, prelude::*};

#[test]
fn it_returns_the_class_name() {
    let ruby = unsafe { magnus::embed::init() };

    unsafe {
        let val: Value = ruby.eval("42").unwrap();

        assert_eq!("Integer", val.classname());
    }
}
