use magnus::{define_global_variable, QNIL};

macro_rules! rb_assert {
    ($eval:literal) => {
        assert!(magnus::eval::<bool>($eval).unwrap())
    };
}

#[test]
fn it_converts_floats_to_value() {
    dbg!("A");
    let _cleanup = unsafe { magnus::embed::init() };
    dbg!("B");
    let val = define_global_variable("$val", QNIL).unwrap();
    dbg!("C");
    rb_assert!("$val == nil");

    dbg!("D");
    unsafe { val.replace(0.5.into()) };
    dbg!("E");
    rb_assert!("$val == 0.5");

    dbg!("F");
    unsafe { val.replace(18446744073709552000.0.into()) };
    dbg!("G");
    rb_assert!("$val == 18446744073709552000.0");

    dbg!("H");
    unsafe { val.replace(f64::INFINITY.into()) };
    dbg!("I");
    rb_assert!("$val == Float::INFINITY");

    dbg!("J");
    unsafe { val.replace(f64::NAN.into()) };
    dbg!("K");
    rb_assert!("$val.nan?");
    dbg!("L");
}
