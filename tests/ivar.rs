use magnus::{eval, Object, RObject, Value};

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
fn it_modifies_ivars() {
    let _cleanup = unsafe { magnus::embed::init() };

    let val: RObject = eval!("$val = Object.new").unwrap();

    val.ivar_set("@test", 42).unwrap();

    rb_assert!("val.instance_variable_get(:@test) == 42", val);

    let _: Value = eval!(r#"val.instance_variable_set(:@example, "test")"#, val).unwrap();

    assert_eq!("test", val.ivar_get::<_, String>("@example").unwrap())
}
