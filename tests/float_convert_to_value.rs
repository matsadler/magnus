#[test]
fn it_converts_floats_to_value() {
    let ruby = unsafe { magnus::embed::init() };
    magnus::rb_assert!(ruby, "val == 0.5", val = 0.5);

    magnus::rb_assert!(
        ruby,
        "val == 18446744073709552000.0",
        val = 18446744073709552000.0
    );

    magnus::rb_assert!(ruby, "val == Float::INFINITY", val = f64::INFINITY);

    magnus::rb_assert!(ruby, "val.nan?", val = f64::NAN);
}
