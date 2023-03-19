use magnus::{class, embed, prelude::*, require, Value};

mod word_sink;
mod word_source;

// run with `echo foo bar baz | cargo run --example embed`
fn main() {
    // start Ruby
    let _cleanup = unsafe { embed::init() };

    // effectivly `require`ing these modules, loading the classes in Ruby
    word_source::init().unwrap();
    word_sink::init().unwrap();

    // require our Ruby code
    // this example uses a relative path from the working directory
    require("./examples/embed/transform").unwrap();

    // get the class defined in Ruby and call a method on it
    class::object()
        .const_get::<_, Value>("Transform")
        .unwrap()
        .funcall::<_, _, Value>("run", ())
        .unwrap();
}
