use magnus::{eval, prelude::*, rb_assert, RObject, Value};

#[test]
fn it_modifies_ivars() {
    let ruby = unsafe { magnus::embed::init() };

    let val: RObject = eval!(ruby, "$val = Object.new").unwrap();

    val.ivar_set("@test", 42).unwrap();

    rb_assert!(ruby, "val.instance_variable_get(:@test) == 42", val);

    let _: Value = eval!(ruby, r#"val.instance_variable_set(:@example, "test")"#, val).unwrap();

    assert_eq!("test", val.ivar_get::<_, String>("@example").unwrap())
}
