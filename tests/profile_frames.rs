use magnus::{RArray, Ruby, Value, debug::FrameBuf, eval, function, value::ReprValue};

fn test(ruby: &Ruby) -> RArray {
    let mut buf = FrameBuf::<1024>::new();
    ruby.profile_frames(&mut buf);

    ruby.ary_from_iter(buf.iter().map(|(frame, _line)| frame.full_label()))
}

#[test]
fn it_works() {
    let ruby = unsafe { magnus::embed::init() };

    ruby.define_global_function("test", function!(test, 0));
    let _: Value = eval!(
        "
            def foo = bar
            def bar = baz
            def baz = qux
            def qux = quxx
            def quxx = test
        "
    )
    .unwrap();
    let res: Vec<String> = ruby.class_object().funcall("foo", ()).unwrap();
    assert_eq!(
        res,
        &[
            "Kernel#test",
            "Object#quxx",
            "Object#qux",
            "Object#baz",
            "Object#bar",
            "Object#foo"
        ]
    )
}
