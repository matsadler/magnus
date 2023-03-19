use magnus::{
    eval, function, gc, method, prelude::*, typed_data, value::Opaque, DataTypeFunctions,
    TypedData, Value,
};

#[derive(TypedData, Clone)]
#[magnus(class = "Pair", free_immediately, mark)]
struct Pair {
    #[magnus(opaque_attr_reader)]
    a: Opaque<Value>,
    #[magnus(opaque_attr_reader)]
    b: Opaque<Value>,
}

impl Pair {
    fn new(a: Value, b: Value) -> Self {
        Self {
            a: a.into(),
            b: b.into(),
        }
    }
}

impl DataTypeFunctions for Pair {
    fn mark(&self) {
        gc::mark(self.a());
        gc::mark(self.b());
    }
}

#[test]
fn it_matches_builtin_clone() {
    let ruby = unsafe { magnus::embed::init() };

    let class = ruby.define_class("Pair", ruby.class_object()).unwrap();
    class
        .define_singleton_method("new", function!(Pair::new, 2))
        .unwrap();
    class
        .define_method("dup", method!(<Pair as typed_data::Dup>::dup, 0))
        .unwrap();
    class
        .define_method("clone", method!(<Pair as typed_data::Dup>::clone, -1))
        .unwrap();

    let res: bool = eval!(
        ruby,
        r#"
        a = Pair.new("foo", 1)
        raise "shouldn't be frozen without freeze:" if a.clone.frozen?
        raise "shouldn't be frozen with freeze: nil" if a.clone(freeze: nil).frozen?
        raise "shouldn't be frozen with freeze: false" if a.clone(freeze: false).frozen?
        raise "should be frozen with freeze: true" unless a.clone(freeze: true).frozen?

        a.freeze
        raise "should be frozen without freeze:" unless a.clone.frozen?
        raise "should be frozen with freeze: nil" unless a.clone(freeze: nil).frozen?
        raise "shouldn't be frozen with #dup" if a.dup.frozen?

        b = Pair.new("bar", 2)
        def b.foobar
          "test"
        end

        raise "dup shouldn't copy singleton class" if b.dup.respond_to?(:foobar)
        b.clone.foobar == "test"
    "#
    )
    .unwrap();
    assert!(res);
}
