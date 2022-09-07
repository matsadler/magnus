use magnus::{
    class, define_module, exception::ExceptionClass, function, gc::register_mark_object, memoize,
    prelude::*, Error, RModule,
};

fn rubric_error() -> ExceptionClass {
    *memoize!(ExceptionClass: {
        let ex = class::object().const_get::<_, RModule>("Ahriman").unwrap().const_get("RubricError").unwrap();
        // ensure `ex` is never garbage collected (e.g. if constant is
        // redefined) and also not moved under compacting GC.
        register_mark_object(ex);
        ex
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
    let module = define_module("Ahriman")?;
    module.define_singleton_method("cast_rubric", function!(cast_rubric, 0))?;
    Ok(())
}
