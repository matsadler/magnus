#[test]
fn it_converts_tuple_to_array() {
    let ruby = unsafe { magnus::embed::init() };

    magnus::rb_assert!(ruby, "val == [1, 2.3, nil, [4]]", val = (1, 2.3, (), (4,)));
}
