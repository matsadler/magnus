use magnus::{eval_static, Exception};

#[test]
fn it_includes_backtrace_in_debug() {
    let _cleanup = unsafe { magnus::embed::init() };

    let err = unsafe {
        Exception::from_value(
            eval_static(
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

            begin
              qux
            rescue => e
            end
            e
        "#,
            )
            .unwrap(),
        )
        .unwrap()
    };

    assert_eq!(
        r#"RuntimeError: bang
eval:3:in `foo'
eval:7:in `bar'
eval:11:in `baz'
eval:15:in `qux'
eval:19:in `<main>'
"#,
        format!("{:#?}", err)
    );
}
