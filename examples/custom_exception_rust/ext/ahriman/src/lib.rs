use magnus::{exception::ExceptionClass, function, prelude::*, value::Lazy, Error, RModule, Ruby};

static AHRIMAN: Lazy<RModule> = Lazy::new(|ruby| ruby.define_module("Ahriman").unwrap());

static ERROR: Lazy<ExceptionClass> = Lazy::new(|ruby| {
    ruby
        .get_inner(&AHRIMAN)
        .define_error("Error", ruby.exception_standard_error())
        .unwrap()
});

static RUBRIC_ERROR: Lazy<ExceptionClass> = Lazy::new(|ruby| {
    ruby
        .get_inner(&AHRIMAN)
        .define_error("RubricError", ruby.get_inner(&ERROR))
        .unwrap()
});

fn cast_rubric(ruby: &Ruby) -> Result<(), Error> {
    if false {
        Ok(())
    } else {
        Err(Error::new(ruby.get_inner(&RUBRIC_ERROR), "All is dust."))
    }
}

#[magnus::init]
fn init(ruby: &Ruby) -> Result<(), Error> {
    Lazy::force(&RUBRIC_ERROR, ruby); // ensure error is defined on load

    ruby
        .get_inner(&AHRIMAN)
        .define_singleton_method("cast_rubric", function!(cast_rubric, 0))?;
    Ok(())
}
