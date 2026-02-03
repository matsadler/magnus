use magnus::{Ruby, Value, embed::init, eval, rb_assert};

#[magnus::wrap(class = "Example", free_immediately)]
struct Example {
    value: String,
}

fn make_rb_example(ruby: &Ruby, value: &str) -> Value {
    let ex = Example {
        value: value.to_owned(),
    };
    ruby.into_value(ex)
}

#[test]
fn it_wraps_rust_struct() {
    let ruby = unsafe { init() };

    ruby.define_class("Example", ruby.class_object()).unwrap();

    let val = make_rb_example(&ruby, "foo");
    rb_assert!(ruby, "val.class == Example", val);

    let ex: &Example = eval!(ruby, "val", val).unwrap();
    assert_eq!("foo", ex.value);
}
