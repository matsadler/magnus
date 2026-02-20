use std::sync::Mutex;

use magnus::{Symbol, Value, debug::Events, eval, prelude::*};

static CALLS: Mutex<Vec<String>> = Mutex::new(Vec::new());

#[test]
fn it_works() {
    let ruby = unsafe { magnus::embed::init() };

    let tp = ruby.tracepoint_new(None, Events::new().call().c_call(), |tp| {
        let id: Symbol = tp.funcall("method_id", ()).unwrap();
        CALLS.lock().unwrap().push(id.to_string());
    });

    let _: Value = eval!(
        "
            def foo = bar
            def bar = baz
            def baz = qux
            def qux = quxx
            def quxx = 1
        "
    )
    .unwrap();

    tp.enable().unwrap();

    let _: Value = ruby.class_object().funcall("foo", ()).unwrap();
    assert_eq!(
        *CALLS.lock().unwrap(),
        &["foo", "bar", "baz", "qux", "quxx"]
    )
}
