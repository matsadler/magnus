use magnus::{eval, Object, RObject, Value};

macro_rules! rb_assert {
    ($eval:literal) => {
        assert!(magnus::eval::<bool>($eval).unwrap())
    };
}

#[test]
fn it_modifies_ivars() {
    let _cleanup = unsafe { magnus::embed::init() };

    let val = eval::<RObject>("$val = Object.new").unwrap();

    val.ivar_set("@test", 42).unwrap();

    rb_assert!("$val.instance_variable_get(:@test) == 42");

    eval::<Value>(r#"$val.instance_variable_set(:@example, "test")"#).unwrap();

    assert_eq!("test", val.ivar_get::<_, String>("@example").unwrap())
}
