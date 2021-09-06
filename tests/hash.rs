use magnus::{define_global_variable, eval};
use std::collections::HashMap;

macro_rules! rb_assert {
    ($eval:literal) => {
        assert!(magnus::eval::<bool>($eval).unwrap())
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
    let _ = define_global_variable("$val", map).unwrap();
    rb_assert!(r#"$val == {"test" => [0, 0.5], "example" => [1, 3.75]}"#)
}
