use std::sync::Mutex;

use magnus::{Error, Value, debug::Events, eval, prelude::*};

static CALLS: Mutex<Vec<String>> = Mutex::new(Vec::new());

#[test]
fn it_works() {
    let ruby = unsafe { magnus::embed::init() };

    let tp = ruby.tracepoint_new(None, Events::new().call().c_call(), |tp| {
        let id = tp.tracearg()?.method_id();
        CALLS
            .lock()
            .unwrap()
            .push(id.map(|i| i.to_string()).unwrap_or(String::from("<none>")));
        Ok::<_, Error>(())
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
