use std::collections::HashMap;

#[test]
fn it_converts_hash_map() {
    let ruby = unsafe { magnus::embed::init() };

    let map: HashMap<String, u8> = ruby
        .eval(r#"{"foo" => 1, "bar" => 2, "baz" => 3}"#)
        .unwrap();

    let mut expected = HashMap::new();
    expected.insert("foo".to_owned(), 1);
    expected.insert("bar".to_owned(), 2);
    expected.insert("baz".to_owned(), 3);
    assert_eq!(expected, map);

    let mut map = HashMap::new();
    map.insert("test", (0, 0.5));
    map.insert("example", (1, 3.75));
    magnus::rb_assert!(
        ruby,
        r#"map == {"test" => [0, 0.5], "example" => [1, 3.75]}"#,
        map
    );
}
