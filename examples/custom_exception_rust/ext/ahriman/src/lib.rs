use magnus::{
    define_module,
    exception::{self, ExceptionClass},
    function, memoize,
    prelude::*,
    Error, RClass, RModule,
};

fn ahriman() -> RModule {
    *memoize!(RModule: define_module("Ahriman").unwrap())
}

fn error() -> ExceptionClass {
    *memoize!(ExceptionClass: {
        let class = ahriman().define_class("Error", RClass::from_value(*exception::standard_error()).unwrap()).unwrap();
        ExceptionClass::from_value(*class).unwrap()
    })
}

fn rubric_error() -> ExceptionClass {
    *memoize!(ExceptionClass: {
        let class = ahriman().define_class("RubricError", RClass::from_value(*error()).unwrap()).unwrap();
        ExceptionClass::from_value(*class).unwrap()
    })
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
