use magnus::{eval_static, RString};

#[test]
fn it_converts_to_ref_str() {
    let _cleanup = unsafe { magnus::embed::init() };

    unsafe {
        // TODO why isn't this utf-8 on the Ruby side by default?
        let val = eval_static("'hello'.encode('utf-8')").ok().unwrap();
        let s = RString::from_value(&val).unwrap();

        assert_eq!("hello", s.as_str().ok().unwrap());
    }
}
