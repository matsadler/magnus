use magnus::{define_global_function, eval_static, method, Error, RString, Value};

fn test(_rb_self: Value, _s: &str) -> Result<(), Error> {
    Ok(())
}

#[test]
fn it_converts_to_ref_str() {
    let _cleanup = unsafe { magnus::embed::init() };

    unsafe {
        // TODO why isn't this utf-8 on the Ruby side by default?
        let val = eval_static("'hello'.encode('utf-8')").unwrap();
        let s = RString::from_value(val).unwrap();

        assert_eq!("hello", s.as_str().unwrap());
    }

    define_global_function("test", method!(test, 1));
}
