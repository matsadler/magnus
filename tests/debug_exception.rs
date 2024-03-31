use magnus::error::ErrorType;

#[test]
fn it_includes_backtrace_in_debug() {
    let ruby = unsafe { magnus::embed::init() };

    let err = ruby
        .eval::<magnus::Value>(
            r#"
            def foo
              raise "bang"
            end

            def bar
              foo
            end

            def baz
              bar
            end

            def qux
              baz
            end

            qux
        "#,
        )
        .unwrap_err();

    let ex = match err.error_type() {
        ErrorType::Exception(e) => e,
        _ => panic!(),
    };

    let message = format!("{:#?}", ex);
    assert!(message.contains("RuntimeError: bang"));
    assert!(message.contains("eval:3:in"));
    assert!(message.contains("foo"));
    assert!(message.contains("eval:7:in"));
    assert!(message.contains("bar"));
    assert!(message.contains("eval:11:in"));
    assert!(message.contains("baz"));
    assert!(message.contains("eval:15:in"));
    assert!(message.contains("qux"));
    assert!(message.contains("eval:18:in"));
    assert!(message.contains("<main>"));
}
