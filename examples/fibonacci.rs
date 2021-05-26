use magnus::{method, Error, Value};

fn fib(rb_self: Value, n: usize) -> Result<usize, Error> {
    match n {
        0 => Ok(0),
        1 | 2 => Ok(1),
        _ => Ok(fib(rb_self, n - 1)? + fib(rb_self, n - 2)?),
    }
}

fn main() {
    let _cleanup = unsafe { magnus::init() };

    magnus::define_global_function("fib", method!(fib, 1));

    let _ = magnus::eval_static("p (0..12).map {|n| fib(n)}");
}
