use magnus::{define_global_variable, eval, RArray, Value};

macro_rules! rb_assert {
    ($eval:literal) => {
        assert!(magnus::eval::<bool>($eval).unwrap())
    };
}

#[test]
fn it_can_check_frozen() {
    let _cleanup = unsafe { magnus::embed::init() };

    assert!(eval::<Value>(r#"42"#).unwrap().is_frozen());
    assert!(eval::<Value>(r#":foo"#).unwrap().is_frozen());

    assert!(!eval::<Value>(r#"Object.new"#).unwrap().is_frozen());
    assert!(!eval::<Value>(r#"[1]"#).unwrap().is_frozen());

    assert!(eval::<Value>(r#"Object.new.freeze"#).unwrap().is_frozen());
    assert!(eval::<Value>(r#"[1].freeze"#).unwrap().is_frozen());

    let val = RArray::new();
    define_global_variable("$val", val).unwrap();
    rb_assert!("!$val.frozen?");
    val.freeze();
    rb_assert!("$val.frozen?");
}
