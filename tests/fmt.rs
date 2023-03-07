use magnus::Value;

#[test]
fn it_formats_with_to_s() {
    let ruby = unsafe { magnus::embed::init() };

    let val = ruby
        .eval::<Value>(r#"["foo".upcase, "bar".to_sym, 1 + 2]"#)
        .unwrap();

    assert_eq!(r#"["FOO", :bar, 3]"#, format!("{:?}", val));
}
