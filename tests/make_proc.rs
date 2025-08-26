use magnus::{Ruby, function, rb_assert};

#[test]
fn it_makes_a_proc() {
    let ruby = unsafe { magnus::embed::init() };

    ruby.define_global_function("make_proc", function!(Ruby::block_proc, 0));

    rb_assert!(ruby, "Proc === make_proc { 1 + 1 }");
    rb_assert!(ruby, "(make_proc { 1 + 1 }).call == 2");
    rb_assert!(
        ruby,
        "begin; make_proc; rescue => e; end; ArgumentError === e"
    );
}
