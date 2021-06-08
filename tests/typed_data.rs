use magnus::{
    define_class, define_global_variable, embed::init, eval_static, memoize, DataType, Qnil,
    RClass, TypedData, Value,
};

macro_rules! rb_assert {
    ($eval:literal) => {
        assert!(magnus::eval_static($eval).unwrap().to_bool())
    };
}

struct Example {
    value: String,
}

impl TypedData for Example {
    const NAME: &'static str = "Example";
    const FREE_IMMEDIATLY: bool = true;

    fn class() -> RClass {
        *memoize!(RClass: define_class("Example", Default::default()).unwrap())
    }

    fn data_type() -> &'static DataType {
        memoize!(DataType: Self::build_data_type())
    }
}

fn make_rb_example(value: &str) -> Value {
    let ex = Example {
        value: value.to_owned(),
    };
    ex.into()
}

#[test]
fn it_wraps_rust_struct() {
    let _cleanup = unsafe { init() };
    let val = define_global_variable("$val", Qnil::new()).unwrap();
    rb_assert!("$val == nil");

    unsafe { val.replace(make_rb_example("foo")) };
    rb_assert!("$val.class == Example");

    let value = eval_static("$val").unwrap();
    let ex = value.try_convert::<&Example>().unwrap();
    assert_eq!("foo", ex.value)
}
