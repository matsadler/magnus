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
fn it_converts_ranges() {
    let _cleanup = unsafe { magnus::embed::init() };

    rb_assert!("range == (2...7)", range = 2..7);
    rb_assert!("range == (2..7)", range = 2..=7);
    rb_assert!("range == (2..)", range = 2..);
    rb_assert!("range == (...7)", range = ..7);
    rb_assert!("range == (..7)", range = ..=7);
    rb_assert!("range == Range.new(nil, nil)", range = ..);
}
