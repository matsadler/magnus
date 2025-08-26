use magnus::{StaticSymbol, Symbol, Value, rb_assert};

#[test]
fn it_makes_a_symbol() {
    let ruby = unsafe { magnus::embed::init() };

    let sym = ruby.to_symbol("foo");
    // not static by default
    assert!(!sym.is_static());

    rb_assert!(ruby, "sym == :foo", sym);

    ruby.eval::<Value>(":bar").unwrap();
    let sym = ruby.to_symbol("bar");
    // static because there's a previous Ruby symbol literal
    assert!(sym.is_static());

    ruby.sym_new("baz");
    let sym = ruby.to_symbol("baz");
    // static because there's a previous StaticSymbol
    assert!(sym.is_static());

    let sym: Symbol = ruby.sym_new("qux").into();
    assert!(sym.is_static());

    let sym = ruby.to_symbol("example");
    assert!(!sym.is_static());
    sym.to_static();
    assert!(sym.is_static());

    let x = ruby.eval::<Symbol>(r#""xxx".to_sym"#).unwrap();
    assert!(!x.is_static());
    ruby.eval::<StaticSymbol>(":xxx").unwrap();

    let y = ruby.eval::<Symbol>(r#""yyy".to_sym"#).unwrap();
    assert!(!y.is_static());
    StaticSymbol::from_value(ruby.eval::<Value>(":yyy").unwrap()).unwrap();
}
