use magnus::prelude::*;

#[test]
fn it_works_across_type() {
    let ruby = unsafe { magnus::embed::init() };

    assert!(ruby.str_new("example").enc_get() == ruby.utf8_encindex());

    assert!(ruby.sym_new("example").enc_get() == ruby.usascii_encindex());
    assert!(ruby.to_symbol("example").enc_get() == ruby.usascii_encindex());

    // symbol upgrades to utf8 when required
    assert!(ruby.sym_new("🦀").enc_get() == ruby.utf8_encindex());
    assert!(ruby.to_symbol("🦀").enc_get() == ruby.utf8_encindex());

    let regexp = ruby.reg_new("example", Default::default()).unwrap();
    assert!(regexp.enc_get() == ruby.usascii_encindex());

    // regexp also upgrades to utf8 when needed
    let regexp = ruby.reg_new("🦀", Default::default()).unwrap();
    assert!(regexp.enc_get() == ruby.utf8_encindex());
}
