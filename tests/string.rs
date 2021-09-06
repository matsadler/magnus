use magnus::{eval, Value};

#[test]
fn it_converts_to_utf8_string() {
    let _cleanup = unsafe { magnus::embed::init() };

    let val: Value = eval(r#""caf\xE9".force_encoding("ISO-8859-1")"#).unwrap();
    let s = val.try_convert::<String>().unwrap();

    assert_eq!("café", s);
}
