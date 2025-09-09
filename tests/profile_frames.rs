use magnus::{RArray, Ruby, Value, debug::Frame, eval, function, value::ReprValue};

fn test(ruby: &Ruby) -> RArray {
    let mut frames = [Frame::EMPTY; 128];
    let count = ruby.profile_frames(0, &mut frames, None);

    ruby.ary_from_iter(frames[0..count].iter().map(|frame| frame.full_label()))
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
