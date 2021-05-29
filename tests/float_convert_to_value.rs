use magnus::{define_global_variable, Qnil};

macro_rules! rb_assert {
    ($eval:literal) => {
        assert!(magnus::eval_static($eval).ok().unwrap().to_bool())
    };
}

#[test]
fn it_converts_floats_to_value() {
    let _cleanup = unsafe { magnus::embed::init() };
    let val = define_global_variable("$val", Qnil::new()).ok().unwrap();
    rb_assert!("$val == nil");

    unsafe { val.replace(0.5.into()) };
    rb_assert!("$val == 0.5");

    unsafe { val.replace(18446744073709552000.0.into()) };
    rb_assert!("$val == 18446744073709552000.0");

    unsafe { val.replace(f64::INFINITY.into()) };
    rb_assert!("$val == Float::INFINITY");

    unsafe { val.replace(f64::NAN.into()) };
    rb_assert!("$val.nan?");
}
