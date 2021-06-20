use magnus::{define_global_variable, Qnil, StaticSymbol, Symbol};

macro_rules! rb_assert {
    ($eval:literal) => {
        assert!(magnus::eval_static($eval).unwrap().to_bool())
    };
}

#[test]
fn it_makes_a_symbol() {
    let _cleanup = unsafe { magnus::embed::init() };
    let val = define_global_variable("$val", Qnil::new()).unwrap();
    rb_assert!("$val == nil");

    let sym = Symbol::new("foo");
    // not static by default
    assert!(!sym.is_static());

    unsafe { val.replace(sym.into()) };
    rb_assert!("$val == :foo");

    magnus::eval_static(":bar").unwrap();
    let sym = Symbol::new("bar");
    // static because there's a previous Ruby symbol literal
    assert!(sym.is_static());

    StaticSymbol::new("baz");
    let sym = Symbol::new("baz");
    // static because there's a previous StaticSymbol
    assert!(sym.is_static());
}
