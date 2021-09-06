use magnus::{eval, RString};

#[test]
fn it_converts_to_ref_str() {
    let _cleanup = unsafe { magnus::embed::init() };

    unsafe {
        // TODO why isn't this utf-8 on the Ruby side by default?
        let s: RString = eval("'hello'.encode('utf-8')").unwrap();

        assert_eq!("hello", s.as_str().unwrap());
    }
}
