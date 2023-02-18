use magnus::{class, define_class, embed::init, eval, IntoValue, Value};

macro_rules! rb_assert {
    ($s:literal) => {
        assert!(magnus::eval::<bool>($s).unwrap())
    };
    ($s:literal, $($rest:tt)*) => {
        let result: bool = magnus::eval!($s, $($rest)*).unwrap();
        assert!(result)
    };
}

#[magnus::wrap(class = "Example", free_immediately)]
struct Example {
    value: String,
}

fn make_rb_example(value: &str) -> Value {
    let ex = Example {
        value: value.to_owned(),
    };
    ex.into_value()
}

#[test]
fn it_wraps_rust_struct() {
    let _cleanup = unsafe { init() };

    define_class("Example", class::object()).unwrap();

    let val = make_rb_example("foo");
    rb_assert!("val.class == Example", val);

    let ex: &Example = eval!("val", val).unwrap();
    assert_eq!("foo", ex.value)
}
