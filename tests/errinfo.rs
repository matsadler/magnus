use magnus::{Error, RHash, Value, r_hash::ForEach, rb_sys::AsRawValue};

fn errinfo() -> rb_sys::VALUE {
    unsafe { rb_sys::rb_errinfo() }
}

// Catching a Ruby exception is the equivalent of a Ruby `rescue`: it must
// leave `$!` as whatever Ruby was already handling. Clearing it corrupts the
// interpreter's unwind state and crashes it later with
// `ec->errinfo == nil`, see https://bugs.ruby-lang.org/issues/22240.
#[test]
fn catching_an_exception_preserves_an_in_flight_exception() {
    let ruby = unsafe { magnus::embed::init() };

    // Nothing in flight: catching an exception must leave `$!` nil rather
    // than leaking the caught exception.
    assert_eq!(errinfo(), ruby.qnil().as_raw());
    assert!(ruby.eval::<Value>("raise 'inner'").is_err());
    assert_eq!(errinfo(), ruby.qnil().as_raw());

    // Set `$!` to a live exception, mimicking Ruby calling into a native
    // extension while an exception is propagating (inside `rescue`, `ensure`,
    // or a signal trap handler that interrupted an in-flight raise).
    let in_flight: Value = ruby.eval(r#"(raise "in flight" rescue $!)"#).unwrap();
    unsafe { rb_sys::rb_set_errinfo(in_flight.as_raw()) };

    // `Ruby::eval` captures the raise with `rb_eval_string_protect`.
    assert!(ruby.eval::<Value>("raise 'inner'").is_err());
    assert_eq!(errinfo(), in_flight.as_raw(), "eval clobbered $!");

    // `Integer#to_i64` raises on an out-of-range Bignum, which magnus catches
    // internally with `error::protect`.
    let bignum: magnus::Integer = ruby.eval("2**100").unwrap();
    assert!(bignum.to_i64().is_err());
    assert_eq!(errinfo(), in_flight.as_raw(), "to_i64 clobbered $!");

    // An exception raised out of a Rust callback run by Ruby
    // (`rb_hash_foreach` here) takes the same path.
    let hash: RHash = ruby.eval(r#"{"a" => 1}"#).unwrap();
    let result = hash.foreach(|_k: Value, _v: Value| -> Result<ForEach, Error> {
        Err(Error::new(ruby.exception_runtime_error(), "from the block"))
    });
    assert!(result.is_err());
    assert_eq!(errinfo(), in_flight.as_raw(), "foreach clobbered $!");

    // Reset so nothing else runs with a bogus `$!`.
    unsafe { rb_sys::rb_set_errinfo(ruby.qnil().as_raw()) };
}
