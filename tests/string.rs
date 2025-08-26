use magnus::{Value, prelude::*};

#[test]
fn it_converts_to_utf8_string() {
    let ruby = unsafe { magnus::embed::init() };

    let val: Value = ruby
        .eval(r#""caf\xE9".force_encoding("ISO-8859-1")"#)
        .unwrap();
    let s = String::try_convert(val).unwrap();

    assert_eq!("café", s);
}
