use magnus::{method, Error, Value};

fn hello(_rb_self: Value) -> Result<(), Error> {
    println!("hello, world");
    Ok(())
}

fn main() {
    let _cleanup = unsafe { magnus::embed::init() };

    magnus::define_global_function("hello", method!(hello, 0));

    let _ = magnus::eval_static("hello");
}
