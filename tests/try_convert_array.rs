use magnus::{eval, RArray};

#[test]
fn it_converts_to_array() {
    let _cleanup = unsafe { magnus::embed::init() };

    assert!(eval::<RArray>("[]").is_ok());
    assert!(eval::<RArray>("[nil]").is_ok());
    assert!(eval::<RArray>("[1, 2]").is_ok());
    assert!(eval::<RArray>(r#"["foo", "bar", "baz"]"#).is_ok());

    assert!(eval::<RArray>("nil").is_err());
    assert!(eval::<RArray>("1").is_err());
    assert!(eval::<RArray>(r#""foo""#).is_err());
}
