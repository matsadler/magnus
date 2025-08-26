use magnus::{Value, prelude::*, rb_assert};

#[test]
fn it_can_check_frozen() {
    let ruby = unsafe { magnus::embed::init() };

    assert!(ruby.eval::<Value>(r#"42"#).unwrap().is_frozen());
    assert!(ruby.eval::<Value>(r#":foo"#).unwrap().is_frozen());

    assert!(!ruby.eval::<Value>(r#"Object.new"#).unwrap().is_frozen());
    assert!(!ruby.eval::<Value>(r#"[1]"#).unwrap().is_frozen());

    assert!(
        ruby.eval::<Value>(r#"Object.new.freeze"#)
            .unwrap()
            .is_frozen()
    );
    assert!(ruby.eval::<Value>(r#"[1].freeze"#).unwrap().is_frozen());

    let val = ruby.ary_new();
    rb_assert!(ruby, "!val.frozen?", val);
    val.freeze();
    rb_assert!(ruby, "val.frozen?", val);
}
