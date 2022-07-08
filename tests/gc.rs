use magnus::{embed::init, eval, gc, value::BoxValue, RString, Value};

#[inline(never)]
fn box_value() -> BoxValue<RString> {
    BoxValue::new(RString::new("foo"))
}

#[test]
fn it_boxvalue_clone() {
    let _cleanup = unsafe { init() };
    let boxed = box_value();
    let cloned = boxed.clone();
    drop(boxed);

    eval::<Value>(r#"1024.times.map {|i| "test#{i}"}"#).unwrap();
    gc::start();
    let result: String = eval!(r#"foo + "bar""#, foo = cloned).unwrap();

    assert_eq!(result, "foobar");
}
