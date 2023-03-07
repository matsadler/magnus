use magnus::RArray;

#[test]
fn it_converts_to_array() {
    let ruby = unsafe { magnus::embed::init() };

    assert!(ruby.eval::<RArray>("[]").is_ok());
    assert!(ruby.eval::<RArray>("[nil]").is_ok());
    assert!(ruby.eval::<RArray>("[1, 2]").is_ok());
    assert!(ruby.eval::<RArray>(r#"["foo", "bar", "baz"]"#).is_ok());

    assert!(ruby.eval::<RArray>("nil").is_err());
    assert!(ruby.eval::<RArray>("1").is_err());
    assert!(ruby.eval::<RArray>(r#""foo""#).is_err());
}
