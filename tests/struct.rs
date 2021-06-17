use magnus::{define_global_variable, r_struct::define_struct, Qnil};

macro_rules! rb_assert {
    ($eval:literal) => {
        assert!(magnus::eval_static($eval).unwrap().to_bool())
    };
}

#[test]
fn it_defines_a_struct() {
    let _cleanup = unsafe { magnus::embed::init() };
    let val = define_global_variable("$val", Qnil::new()).unwrap();
    rb_assert!("$val == nil");

    unsafe { val.replace(define_struct("Foo", ("bar", "baz")).unwrap().into()) };
    rb_assert!(r#"$val.name == "Struct::Foo""#);
    rb_assert!("$val.members == [:bar, :baz]");
}
