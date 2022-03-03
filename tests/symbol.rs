use magnus::{eval, StaticSymbol, Symbol, Value};

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
fn it_makes_a_symbol() {
    let _cleanup = unsafe { magnus::embed::init() };

    let sym = Symbol::new("foo");
    // not static by default
    assert!(!sym.is_static());

    rb_assert!("sym == :foo", sym);

    magnus::eval::<Value>(":bar").unwrap();
    let sym = Symbol::new("bar");
    // static because there's a previous Ruby symbol literal
    assert!(sym.is_static());

    StaticSymbol::new("baz");
    let sym = Symbol::new("baz");
    // static because there's a previous StaticSymbol
    assert!(sym.is_static());

    let sym: Symbol = StaticSymbol::new("qux").into();
    assert!(sym.is_static());

    let sym = Symbol::new("example");
    assert!(!sym.is_static());
    sym.to_static();
    assert!(sym.is_static());

    let x = eval::<Symbol>(r#""xxx".to_sym"#).unwrap();
    assert!(!x.is_static());
    eval::<StaticSymbol>(":xxx").unwrap();

    let y = eval::<Symbol>(r#""yyy".to_sym"#).unwrap();
    assert!(!y.is_static());
    StaticSymbol::from_value(eval::<Value>(":yyy").unwrap()).unwrap();
}
