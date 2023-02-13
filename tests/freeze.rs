use magnus::{eval, prelude::*, RArray, Value};

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
fn it_can_check_frozen() {
    let _cleanup = unsafe { magnus::embed::init() };

    assert!(eval::<Value>(r#"42"#).unwrap().is_frozen());
    assert!(eval::<Value>(r#":foo"#).unwrap().is_frozen());

    assert!(!eval::<Value>(r#"Object.new"#).unwrap().is_frozen());
    assert!(!eval::<Value>(r#"[1]"#).unwrap().is_frozen());

    assert!(eval::<Value>(r#"Object.new.freeze"#).unwrap().is_frozen());
    assert!(eval::<Value>(r#"[1].freeze"#).unwrap().is_frozen());

    let val = RArray::new();
    rb_assert!("!val.frozen?", val);
    val.freeze();
    rb_assert!("val.frozen?", val);
}
