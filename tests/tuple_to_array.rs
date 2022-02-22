macro_rules! rb_assert {
    ($s:literal) => {
        assert!(magnus::eval::<bool>($s).unwrap())
    };
    ($s:literal, $($rest:tt)*) => {
        let result: bool = magnus::eval!($s, $($rest)*).unwrap();
        assert!(result)
    };
}

#[test]
fn it_converts_tuple_to_array() {
    let _cleanup = unsafe { magnus::embed::init() };

    rb_assert!("val == [1, 2.3, nil, [4]]", val = (1, 2.3, (), (4,)));
}
