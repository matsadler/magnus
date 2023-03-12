use magnus::{exception::ExceptionClass, function, prelude::*, value::Lazy, Error, RModule, Ruby};

static AHRIMAN: Lazy<RModule> = Lazy::new(|ruby| ruby.define_module("Ahriman").unwrap());

static ERROR: Lazy<ExceptionClass> = Lazy::new(|ruby| {
    AHRIMAN
        .get(ruby)
        .define_error("Error", ruby.exception_standard_error())
        .unwrap()
});

static RUBRIC_ERROR: Lazy<ExceptionClass> = Lazy::new(|ruby| {
    AHRIMAN
        .get(ruby)
        .define_error("RubricError", ERROR.get(ruby))
        .unwrap()
});

fn cast_rubric(ruby: &Ruby) -> Result<(), Error> {
    if false {
        Ok(())
    } else {
        Err(Error::new(RUBRIC_ERROR.get(ruby), "All is dust."))
    }
}

#[magnus::init]
fn init(ruby: &Ruby) -> Result<(), Error> {
    RUBRIC_ERROR.get(ruby); // ensure error is defined on load

    AHRIMAN
        .get(ruby)
        .define_singleton_method("cast_rubric", function!(cast_rubric, 0))?;
    Ok(())
}
