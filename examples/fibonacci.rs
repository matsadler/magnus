fn fib(n: usize) -> usize {
    match n {
        0 => 0,
        1 | 2 => 1,
        _ => fib(n - 1) + fib(n - 2),
    }
}

fn main() {
    let _cleanup = unsafe { magnus::embed::init() };

    magnus::define_global_function("fib", magnus::function!(fib, 1));

    magnus::eval::<magnus::Value>("p (0..12).map {|n| fib(n)}").unwrap();
}
