use magnus::{prelude::*, Value};

#[test]
fn it_converts_to_utf8_string() {
    let ruby = unsafe { magnus::embed::init() };

    let val: Value = ruby
        .eval(r#""caf\xE9".force_encoding("ISO-8859-1")"#)
        .unwrap();
    let s = String::try_convert(val).unwrap();

    assert_eq!("café", s);

    let val: Value = magnus::eval!(r#""\xFF\xFF""#).unwrap();
    let err = String::try_convert(val).unwrap_err();

    let expected_error = "invalid byte sequence in UTF-8";
    assert!(
        err.to_string().contains(expected_error),
        "Expected \"{}\" to contain \"{expected_error}\" but it didn't",
        err.to_string()
    );
}
