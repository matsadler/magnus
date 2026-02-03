fn hello(subject: String) -> String {
    format!("hello, {}", subject)
}

fn main() -> Result<(), magnus::Error> {
    magnus::Ruby::init(|ruby| {
        ruby.define_global_function("hello", magnus::function!(hello, 1));

        ruby.eval::<magnus::value::Qnil>(r#"puts hello("world")"#)
            .unwrap();

        Ok(())
    })
}
