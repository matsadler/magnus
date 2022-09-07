use magnus::{
    define_module,
    exception::{self, ExceptionClass},
    function, memoize,
    prelude::*,
    Error, RModule,
};

fn ahriman() -> RModule {
    *memoize!(RModule: define_module("Ahriman").unwrap())
}

fn error() -> ExceptionClass {
    *memoize!(ExceptionClass: ahriman().define_error("Error", exception::standard_error()).unwrap())
}

fn rubric_error() -> ExceptionClass {
    *memoize!(ExceptionClass: ahriman().define_error("RubricError", error()).unwrap())
}

fn cast_rubric() -> Result<(), Error> {
    if false {
        Ok(())
    } else {
        Err(Error::new(rubric_error(), "All is dust."))
    }
}

#[magnus::init]
fn init() -> Result<(), Error> {
    rubric_error(); // ensure error is defined on load

    ahriman().define_singleton_method("cast_rubric", function!(cast_rubric, 0))?;
    Ok(())
}
