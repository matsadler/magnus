use magnus::{eval_static, Object, RObject};

macro_rules! rb_assert {
    ($eval:literal) => {
        assert!(magnus::eval_static($eval).unwrap().to_bool())
    };
}

#[test]
fn it_modifies_ivars() {
    let _cleanup = unsafe { magnus::embed::init() };

    let val = RObject::from_value(eval_static("$val = Object.new").unwrap()).unwrap();

    val.ivar_set("@test", 42).unwrap();

    rb_assert!("$val.instance_variable_get(:@test) == 42");

    eval_static(r#"$val.instance_variable_set(:@example, "test")"#).unwrap();

    assert_eq!("test", val.ivar_get::<_, String>("@example").unwrap())
}
