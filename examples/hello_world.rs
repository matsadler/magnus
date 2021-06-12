fn hello(subject: String) -> String {
    format!("hello, {}", subject)
}

fn main() {
    let _cleanup = unsafe { magnus::embed::init() };

    magnus::define_global_function("hello", magnus::function!(hello, 1));

    let _ = magnus::eval_static(r#"puts hello("world")"#);
}
