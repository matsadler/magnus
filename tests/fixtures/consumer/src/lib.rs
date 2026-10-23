use magnus::{Error, RArray, RString, Ruby, function, method, prelude::*};

#[magnus::wrap(class = "MagnusConsumer::Number", free_immediately, size)]
struct Number(i64);

impl Number {
    fn new(value: i64) -> Self {
        Self(value)
    }

    fn value(&self) -> i64 {
        self.0
    }
}

fn string_length(value: RString) -> usize {
    value.len()
}

fn string_copy(value: RString) -> String {
    // SAFETY: copy the borrowed bytes before calling Ruby, so the string
    // cannot be mutated or relocated while Rust holds the reference.
    unsafe { value.to_string_lossy().into_owned() }
}

fn array_length(value: RArray) -> usize {
    value.len()
}

fn array_sum(value: RArray) -> Result<i64, Error> {
    Ok(value.to_vec::<i64>()?.into_iter().sum())
}

#[magnus::init]
fn init(ruby: &Ruby) -> Result<(), Error> {
    let module = ruby.define_module("MagnusConsumer")?;
    module.define_singleton_method("string_length", function!(string_length, 1))?;
    module.define_singleton_method("string_copy", function!(string_copy, 1))?;
    module.define_singleton_method("array_length", function!(array_length, 1))?;
    module.define_singleton_method("array_sum", function!(array_sum, 1))?;
    let class = module.define_class("Number", ruby.class_object())?;
    class.define_singleton_method("new", function!(Number::new, 1))?;
    class.define_method("value", method!(Number::value, 0))?;
    Ok(())
}
