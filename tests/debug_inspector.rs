use magnus::{Error, Ruby, Value, eval, function, prelude::*};

fn debug(ruby: &Ruby) -> Result<Value, Error> {
    ruby.debug_inspector_open(|inspector| inspector.backtrace_locations())
}

#[test]
fn it_works() {
    let ruby = unsafe { magnus::embed::init() };

    ruby.define_global_function("debug", function!(debug, 0));
    let _: Value = eval!(
        "
            def foo = bar
            def bar = baz
            def baz = qux
            def qux = quxx
            def quxx = debug.map(&:base_label)
        "
    )
    .unwrap();
    let res: Vec<String> = ruby.class_object().funcall("foo", ()).unwrap();
    assert_eq!(res, &["debug", "quxx", "qux", "baz", "bar", "foo"])
}
