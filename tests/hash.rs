use magnus::eval;
use std::collections::HashMap;

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
fn it_converts_hash_map() {
    let _cleanup = unsafe { magnus::embed::init() };

    let map: HashMap<String, u8> = eval(r#"{"foo" => 1, "bar" => 2, "baz" => 3}"#).unwrap();

    let mut expected = HashMap::new();
    expected.insert("foo".to_owned(), 1);
    expected.insert("bar".to_owned(), 2);
    expected.insert("baz".to_owned(), 3);
    assert_eq!(expected, map);

    let mut map = HashMap::new();
    map.insert("test", (0, 0.5));
    map.insert("example", (1, 3.75));
    rb_assert!(
        r#"map == {"test" => [0, 0.5], "example" => [1, 3.75]}"#,
        map
    );
}
