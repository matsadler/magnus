fn main() {
    magnus::Ruby::init(|ruby| {
        // Ensure this doesn't fail with `uninitialized constant Encoding::UTF_8`
        // with `ruby-static` feature.
        ruby.eval::<magnus::value::Qnil>(r#"p Encoding::UTF_8"#)
            .unwrap();

        Ok(())
    })
    .unwrap()
}
