#[test]
fn it_converts_ranges() {
    let ruby = unsafe { magnus::embed::init() };

    magnus::rb_assert!(ruby, "range == (2...7)", range = 2..7);
    magnus::rb_assert!(ruby, "range == (2..7)", range = 2..=7);
    magnus::rb_assert!(ruby, "range == (2..)", range = 2..);
    #[cfg(ruby_gte_2_7)]
    {
        magnus::rb_assert!(ruby, "range == (...7)", range = ..7);
        magnus::rb_assert!(ruby, "range == (..7)", range = ..=7);
    }
    magnus::rb_assert!(ruby, "range == Range.new(nil, nil)", range = ..);
}
