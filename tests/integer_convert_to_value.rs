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
fn it_converts_integers_to_value() {
    let _cleanup = unsafe { magnus::embed::init() };

    rb_assert!("val == 0", val = 0u8);

    rb_assert!("val == -1", val = -1i64);

    rb_assert!("val == 9223372036854775807", val = 9223372036854775807i64);
}
