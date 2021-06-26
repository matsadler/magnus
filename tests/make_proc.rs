use magnus::{block::block_proc, define_global_function, function};

macro_rules! rb_assert {
    ($eval:literal) => {
        assert!(magnus::eval_static($eval).unwrap().to_bool())
    };
}

#[test]
fn it_makes_a_proc() {
    let _cleanup = unsafe { magnus::embed::init() };

    define_global_function("make_proc", function!(block_proc, 0));

    rb_assert!("Proc === make_proc { 1 + 1 }");
    rb_assert!("(make_proc { 1 + 1 }).call == 2");
    rb_assert!("begin; make_proc; rescue => e; end; ArgumentError === e");
}
