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
fn it_converts_floats_to_value() {
    let _cleanup = unsafe { magnus::embed::init() };
    rb_assert!("val == 0.5", val = 0.5);

    rb_assert!("val == 18446744073709552000.0", val = 18446744073709552000.0);

    rb_assert!("val == Float::INFINITY", val = f64::INFINITY);

    rb_assert!("val.nan?", val = f64::NAN);
}
