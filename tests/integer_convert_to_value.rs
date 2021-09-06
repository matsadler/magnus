use magnus::{define_global_variable, QNIL};

macro_rules! rb_assert {
    ($eval:literal) => {
        assert!(magnus::eval::<bool>($eval).unwrap())
    };
}

#[test]
fn it_converts_integers_to_value() {
    let _cleanup = unsafe { magnus::embed::init() };
    let val = define_global_variable("$val", QNIL).unwrap();
    rb_assert!("$val == nil");

    unsafe { val.replace((0u8).into()) };
    rb_assert!("$val == 0");

    unsafe { val.replace((-1i64).into()) };
    rb_assert!("$val == -1");

    unsafe { val.replace(9223372036854775807i64.into()) };
    rb_assert!("$val == 9223372036854775807");
}
