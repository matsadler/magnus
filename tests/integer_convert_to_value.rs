use magnus::{define_global_variable, Qnil};

macro_rules! rb_assert {
    ($eval:literal) => {
        assert!(magnus::eval_static($eval).ok().unwrap().to_bool())
    };
}

#[test]
fn it_converts_integers_to_value() {
    let _cleanup = unsafe { magnus::init() };
    let val = define_global_variable("$val", Qnil::new().into())
        .ok()
        .unwrap();
    rb_assert!("$val == nil");

    unsafe { val.replace((0u8).into()) };
    rb_assert!("$val == 0");

    unsafe { val.replace((-1i64).into()) };
    rb_assert!("$val == -1");

    unsafe { val.replace(9223372036854775807i64.into()) };
    rb_assert!("$val == 9223372036854775807");
}
