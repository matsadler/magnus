#[test]
fn it_stops_on_err() {
    let ruby = unsafe { magnus::embed::init() };

    let s = ruby.str_new("foo");
    s.cat([128]); // invalid
    s.cat("bar");

    let count = unsafe { s.codepoints().count() };

    // f, o, o, Err = 4
    assert_eq!(count, 4);
}
