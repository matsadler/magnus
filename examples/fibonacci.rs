use magnus::{method, Value};

fn fib(rb_self: Value, n: usize) -> usize {
    match n {
        0 => 0,
        1 | 2 => 1,
        _ => fib(rb_self, n - 1) + fib(rb_self, n - 2),
    }
}

fn main() {
    let _cleanup = unsafe { magnus::embed::init() };

    magnus::define_global_function("fib", method!(fib, 1));

    let _ = magnus::eval_static("p (0..12).map {|n| fib(n)}");
}
