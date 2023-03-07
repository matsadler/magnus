#[test]
fn it_converts_integers_to_value() {
    let ruby = unsafe { magnus::embed::init() };

    magnus::rb_assert!(ruby, "val == 0", val = 0u8);

    magnus::rb_assert!(ruby, "val == -1", val = -1i64);

    magnus::rb_assert!(
        ruby,
        "val == 9223372036854775807",
        val = 9223372036854775807i64
    );
}
