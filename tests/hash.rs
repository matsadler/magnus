use magnus::{define_global_variable, eval_static};
use std::collections::HashMap;

macro_rules! rb_assert {
    ($eval:literal) => {
        assert!(magnus::eval_static($eval).unwrap().to_bool())
    };
}

#[test]
fn it_converts_hash_map() {
    let _cleanup = unsafe { magnus::embed::init() };

    let val = eval_static(r#"{"foo" => 1, "bar" => 2, "baz" => 3}"#).unwrap();
    let map = val.try_convert::<HashMap<String, u8>>().unwrap();

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
