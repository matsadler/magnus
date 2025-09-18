use magnus::{Error, RModule, Ruby, exception::ExceptionClass, function, prelude::*, value::Lazy};

static RUBRIC_ERROR: Lazy<ExceptionClass> = Lazy::new(|ruby| {
    let ex = ruby
        .class_object()
        .const_get::<_, RModule>("Ahriman")
        .unwrap()
        .const_get("RubricError")
        .unwrap();
    // ensure `ex` is never garbage collected (e.g. if constant is
    // redefined) and also not moved under compacting GC.
    ruby.gc_register_mark_object(ex);
    ex
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
    let module = ruby.define_module("Ahriman")?;
    module.define_singleton_method("cast_rubric", function!(cast_rubric, 0))?;
    Ok(())
}
