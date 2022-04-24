use magnus::{
    encoding::{self, EncodingCapable},
    eval, RRegexp, RString, StaticSymbol, Symbol,
};

#[test]
fn it_works_across_type() {
    let _cleanup = unsafe { magnus::embed::init() };

    assert!(RString::new("example").enc_get() == encoding::Index::utf8());

    assert!(StaticSymbol::new("example").enc_get() == encoding::Index::usascii());
    assert!(Symbol::new("example").enc_get() == encoding::Index::usascii());

    // symbol upgrades to utf8 when required
    assert!(StaticSymbol::new("🦀").enc_get() == encoding::Index::utf8());
    assert!(Symbol::new("🦀").enc_get() == encoding::Index::utf8());

    let regexp: RRegexp = eval!("/example/").unwrap();
    assert!(regexp.enc_get() == encoding::Index::usascii());

    // regexp also upgrades to utf8 when needed
    let regexp: RRegexp = eval!("/🦀/").unwrap();
    assert!(regexp.enc_get() == encoding::Index::utf8());
}
