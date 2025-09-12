use std::cell::RefCell;

use magnus::{RArray, Ruby, Value, debug::FrameBuf, eval, function, prelude::*};

thread_local! {
    static FRAMES: RefCell<FrameBuf<1024>> = const { RefCell::new(FrameBuf::new()) };
}

fn profile(ruby: &Ruby) -> RArray {
    FRAMES.with_borrow_mut(|buf| {
        ruby.profile_frames(buf);
        ruby.ary_from_iter(buf.iter().map(|(frame, _line)| frame.full_label()))
    })
}

#[test]
fn it_works() {
    let ruby = unsafe { magnus::embed::init() };

    ruby.define_global_function("profile", function!(profile, 0));
    let _: Value = eval!(
        "
            def foo = bar
            def bar = baz
            def baz = qux
            def qux = quxx
            def quxx = profile
        "
    )
    .unwrap();
    let res: Vec<String> = ruby.class_object().funcall("foo", ()).unwrap();
    assert_eq!(
        res,
        &[
            "Kernel#profile",
            "Object#quxx",
            "Object#qux",
            "Object#baz",
            "Object#bar",
            "Object#foo"
        ]
    )
}
