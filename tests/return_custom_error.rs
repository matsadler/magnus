use magnus::{Error, Ruby, error::IntoError, function, rb_assert};

struct CustomError(&'static str);

impl IntoError for CustomError {
    fn into_error(self, ruby: &Ruby) -> Error {
        Error::new(
            ruby.exception_runtime_error(),
            format!("Custom error: {}", self.0),
        )
    }
}

fn example() -> Result<(), CustomError> {
    Err(CustomError("test"))
}

#[test]
fn it_can_bind_function_returning_custom_error() {
    let ruby = unsafe { magnus::embed::init() };

    ruby.define_global_function("example", function!(example, 0));

    rb_assert!(
        ruby,
        r#"(example rescue $!).message == "Custom error: test""#
    );
}
