use magnus::{Error, RString};

#[test]
fn it_stops_on_err() {
    let _cleanup = unsafe { magnus::embed::init() };

    let s = RString::new("foo");
    s.cat([128]); // invalid
    s.cat("bar");

    let count = unsafe { s.codepoints().count() };

    // f, o, o, Err = 4
    assert_eq!(count, 4);
}
