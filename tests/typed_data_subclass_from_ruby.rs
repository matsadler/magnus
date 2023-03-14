use magnus::{
    embed::init, eval, exception, function, method, prelude::*, rb_assert, typed_data::Obj, Error,
    RClass, Value,
};

const FACTOR: f64 = 1000000.0;

#[magnus::wrap(class = "Temperature")]
struct Temperature {
    microkelvin: u64,
}

impl Temperature {
    fn new(class: RClass, k: f64) -> Result<Obj<Self>, Error> {
        if k < 0.0 {
            return Err(Error::new(
                exception::arg_error(),
                "temperature must be above absolute zero",
            ));
        }
        let value = Self {
            microkelvin: (k * FACTOR) as u64,
        };
        Ok(Obj::wrap_as(value, class))
    }

    fn to_kelvin(&self) -> f64 {
        self.microkelvin as f64 / FACTOR
    }

    fn to_s(&self) -> String {
        format!("{} K", self.to_kelvin())
    }
}

#[test]
fn it_wraps_rust_struct() {
    let ruby = unsafe { init() };

    let class = ruby
        .define_class("Temperature", ruby.class_object())
        .unwrap();

    class
        .define_singleton_method("new", method!(Temperature::new, 1))
        .unwrap();
    // define the `inherited` callback method so that when Temperature is
    // inherited from we undef the `alloc` method for the subclass. This
    // a) prevents uninitialised instances of the subclass being created
    // b) silences a warning on Ruby 3.2
    class
        .define_singleton_method("inherited", function!(RClass::undef_default_alloc_func, 1))
        .unwrap();
    class
        .define_method("to_kelvin", method!(Temperature::to_kelvin, 0))
        .unwrap();
    class
        .define_method("to_s", method!(Temperature::to_s, 0))
        .unwrap();

    let _: Value = eval!(
        ruby,
        r##"
        class Celsius < Temperature
          def self.new(c)
            super(c + 273.15)
          end

          def to_s
            "#{to_kelvin - 273.15} °C"
          end
        end
    "##,
    )
    .unwrap();

    rb_assert!(ruby, r#"Celsius.new(19.5).to_s == "19.5 °C""#);
    rb_assert!(ruby, r"Celsius.new(19.5).class == Celsius");
    rb_assert!(ruby, r"Celsius.new(19.5).to_kelvin == 292.65");
}
