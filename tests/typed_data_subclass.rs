use magnus::{embed::init, method, prelude::*, rb_assert};

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
    let ruby = unsafe { init() };

    let class = ruby
        .define_class("Pleasantry", ruby.class_object())
        .unwrap();
    ruby.define_class("Farewell", class).unwrap();
    ruby.define_class("Greeting", class).unwrap();

    class
        .define_method("to_s", method!(Pleasantry::to_s, 0))
        .unwrap();

    let greeting = Pleasantry::Greeting("World".to_owned());
    rb_assert!(ruby, "greeting.is_a?(Greeting)", greeting);

    let greeting = Pleasantry::Greeting("World".to_owned());
    rb_assert!(ruby, "greeting.is_a?(Pleasantry)", greeting);

    let greeting = Pleasantry::Greeting("World".to_owned());
    rb_assert!(ruby, r#"greeting.to_s == "Hello, World!""#, greeting);

    let farewell = Pleasantry::Farewell("World".to_owned());
    rb_assert!(ruby, "farewell.is_a?(Farewell)", farewell);

    let farewell = Pleasantry::Farewell("World".to_owned());
    rb_assert!(ruby, "farewell.is_a?(Pleasantry)", farewell);

    let farewell = Pleasantry::Farewell("World".to_owned());
    rb_assert!(ruby, r#"farewell.to_s == "Goodbye, World!""#, farewell);
}
