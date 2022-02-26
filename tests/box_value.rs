use magnus::{embed::init, eval, gc, value::BoxValue, RString, Value};

#[inline(never)]
fn box_value() -> BoxValue {
    BoxValue::new(eval(r#""foo""#).unwrap())
}

#[test]
fn it_keeps_value_alive() {
    let _cleanup = unsafe { init() };

    // get the Value in a different stack frame and copy it to a BoxValue
    // test is invalid if this is done in this function.
    let val = box_value();

    // make some garbage
    eval::<Value>(r#"1024.times.map {|i| "test#{i}"}"#).unwrap();
    gc::start();

    // try and use value
    let _: RString = eval!(r#"foo + "bar""#, foo = val).unwrap();

    // didn't segfault? we passed!
}
