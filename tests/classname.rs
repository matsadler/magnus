use magnus::eval_static;

#[test]
fn it_returns_the_class_name() {
    let _cleanup = unsafe { magnus::embed::init() };

    unsafe {
        let val = eval_static("42").unwrap();

        assert_eq!("Integer", val.classname());
    }
}
