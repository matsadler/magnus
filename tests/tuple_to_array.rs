use magnus::define_global_variable;

macro_rules! rb_assert {
    ($eval:literal) => {
        assert!(magnus::eval_static($eval).unwrap().to_bool())
    };
}

#[test]
fn it_converts_tuple_to_array() {
    let _cleanup = unsafe { magnus::embed::init() };
    let _ = define_global_variable("$val", (1, 2.3, (), (4,))).unwrap();

    rb_assert!("$val == [1, 2.3, nil, [4]]")
}
