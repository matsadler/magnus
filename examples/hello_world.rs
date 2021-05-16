use magnus::{fn_ptr, Qnil, Value};

extern "C" fn hello(_rb_self: Value) -> Value {
    println!("hello, world");
    Qnil::new().into()
}

fn main() {
    let _cleanup = unsafe { magnus::init() };

    magnus::define_global_function("hello", fn_ptr!(hello));

    let _ = magnus::eval_static("p hello");
}
