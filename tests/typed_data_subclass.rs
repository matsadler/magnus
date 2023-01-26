use magnus::{
    define_class, embed::init, memoize, method, typed_data::DataTypeBuilder, Class, DataType,
    DataTypeFunctions, Module, RClass, TypedData,
};

macro_rules! rb_assert {
    ($s:literal) => {
        assert!(magnus::eval::<bool>($s).unwrap())
    };
    ($s:literal, $($rest:tt)*) => {
        let result: bool = magnus::eval!($s, $($rest)*).unwrap();
        assert!(result)
    };
}

#[derive(DataTypeFunctions)]
enum Pleasantry {
    Greeting(String),
    Farewell(String),
}

impl Pleasantry {
    fn to_s(&self) -> String {
        match self {
            Self::Greeting(subject) => format!("Hello, {}!", subject),
            Self::Farewell(subject) => format!("Goodbye, {}!", subject),
        }
    }
}

unsafe impl TypedData for Pleasantry {
    fn class() -> RClass {
        *memoize!(RClass: {
          let class = define_class("Pleasantry", Default::default()).unwrap();
          class.undef_alloc_func();
          class
        })
    }

    fn data_type() -> &'static DataType {
        memoize!(DataType: DataTypeBuilder::<Pleasantry>::new("Pleasantry").build())
    }

    fn class_for(value: &Self) -> RClass {
        match value {
            Self::Greeting(_) => *memoize!(RClass: {
                let class = define_class("Greeting", <Self as TypedData>::class()).unwrap();
                class.undef_alloc_func();
                class
            }),
            Self::Farewell(_) => *memoize!(RClass: {
                let class = define_class("Farewell", <Self as TypedData>::class()).unwrap();
                class.undef_alloc_func();
                class
            }),
        }
    }
}

#[test]
fn it_wraps_rust_struct() {
    let _cleanup = unsafe { init() };

    let class = define_class("Pleasantry", Default::default()).unwrap();
    class
        .define_method("to_s", method!(Pleasantry::to_s, 0))
        .unwrap();

    let greeting = Pleasantry::Greeting("World".to_owned());
    rb_assert!("greeting.is_a?(Greeting)", greeting);

    let greeting = Pleasantry::Greeting("World".to_owned());
    rb_assert!("greeting.is_a?(Pleasantry)", greeting);

    let greeting = Pleasantry::Greeting("World".to_owned());
    rb_assert!(r#"greeting.to_s == "Hello, World!""#, greeting);

    let farewell = Pleasantry::Farewell("World".to_owned());
    rb_assert!("farewell.is_a?(Farewell)", farewell);

    let farewell = Pleasantry::Farewell("World".to_owned());
    rb_assert!("farewell.is_a?(Pleasantry)", farewell);

    let farewell = Pleasantry::Farewell("World".to_owned());
    rb_assert!(r#"farewell.to_s == "Goodbye, World!""#, farewell);
}
