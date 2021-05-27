use magnus::{define_global_variable, Qnil, Symbol};

macro_rules! rb_assert {
    ($eval:literal) => {
        assert!(magnus::eval_static($eval).ok().unwrap().to_bool())
    };
}

#[test]
fn it_makes_a_symbol() {
    let _cleanup = unsafe { magnus::init() };
    let val = define_global_variable("$val", Qnil::new().into())
        .ok()
        .unwrap();
    rb_assert!("$val == nil");

    unsafe { val.replace(Symbol::new("foo").into()) };
    rb_assert!("$val == :foo");
}
