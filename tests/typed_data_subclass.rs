use magnus::{class, define_class, embed::init, method, prelude::*};

macro_rules! rb_assert {
    ($s:literal) => {
        assert!(magnus::eval::<bool>($s).unwrap())
    };
    ($s:literal, $($rest:tt)*) => {
        let result: bool = magnus::eval!($s, $($rest)*).unwrap();
        assert!(result)
    };
}

#[magnus::wrap(class = "Pleasantry")]
enum Pleasantry {
    #[magnus(class = "Greeting")]
    Greeting(String),
    #[magnus(class = "Farewell")]
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

#[test]
fn it_wraps_rust_struct() {
    let _cleanup = unsafe { init() };

    let class = define_class("Pleasantry", class::object()).unwrap();
    define_class("Farewell", class).unwrap();
    define_class("Greeting", class).unwrap();

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
