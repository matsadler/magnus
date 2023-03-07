use magnus::RString;

#[test]
fn it_converts_to_ref_str() {
    let ruby = unsafe { magnus::embed::init() };

    unsafe {
        let s: RString = ruby.eval("'hello'").unwrap();

        assert_eq!("hello", s.as_str().unwrap());
    }
}
