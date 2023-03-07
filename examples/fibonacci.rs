fn fib(n: usize) -> usize {
    match n {
        0 => 0,
        1 | 2 => 1,
        _ => fib(n - 1) + fib(n - 2),
    }
}

fn main() {
    magnus::Ruby::init(|ruby| {
        ruby.define_global_function("fib", magnus::function!(fib, 1));

        ruby.eval::<magnus::Value>("p (0..12).map {|n| fib(n)}")
            .unwrap();

        Ok(())
    })
    .unwrap()
}
