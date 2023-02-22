use std::fmt;

use magnus::{
    class, define_class, exception, function, method, module,
    prelude::*,
    scan_args::{get_kwargs, scan_args},
    typed_data, Error, Value,
};

#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Hash)]
#[magnus::wrap(class = "Temperature", free_immediately, size)]
struct Temperature {
    microkelvin: u64,
}

const FACTOR: f64 = 1000000.0;
const C_OFFSET: f64 = 273.15;

fn f_to_c(f: f64) -> f64 {
    (f - 32.0) * (5.0 / 9.0)
}

fn c_to_f(c: f64) -> f64 {
    c * (9.0 / 5.0) + 32.0
}

impl Temperature {
    fn new(args: &[Value]) -> Result<Self, Error> {
        let args = scan_args::<(), (), (), (), _, ()>(args)?;
        let kwargs = get_kwargs::<_, (), (Option<f64>, Option<f64>, Option<f64>), ()>(
            args.keywords,
            &[],
            &["kelvin", "celsius", "fahrenheit"],
        )?;
        match kwargs.optional {
            (Some(k), None, None) => Self::from_kelvin(k),
            (None, Some(c), None) => Self::from_celsius(c),
            (None, None, Some(f)) => Self::from_fahrenheit(f),
            (None, None, None) => Err(Error::new(
                exception::arg_error(),
                "missing keyword: :kelvin, :celsius, or :fahrenheit",
            )),
            _ => Err(Error::new(
                exception::arg_error(),
                "unexpected keyword, supply one of: :kelvin, :celsius, or :fahrenheit",
            )),
        }
    }

    fn from_kelvin(k: f64) -> Result<Self, Error> {
        if k < 0.0 {
            return Err(Error::new(
                exception::arg_error(),
                "temperature must be above absolute zero",
            ));
        }
        Ok(Self {
            microkelvin: (k * FACTOR) as u64,
        })
    }

    fn from_celsius(c: f64) -> Result<Self, Error> {
        Self::from_kelvin(c + C_OFFSET)
    }

    fn from_fahrenheit(f: f64) -> Result<Self, Error> {
        Self::from_celsius(f_to_c(f))
    }

    fn to_kelvin(&self) -> f64 {
        self.microkelvin as f64 / FACTOR
    }

    fn to_celsius(&self) -> f64 {
        self.to_kelvin() - C_OFFSET
    }

    fn to_fahrenheit(&self) -> f64 {
        c_to_f(self.to_celsius())
    }
}

impl fmt::Display for Temperature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}°C", self.to_celsius())
    }
}

#[magnus::init]
fn init() -> Result<(), Error> {
    let class = define_class("Temperature", class::object())?;

    // define new directly, there is no #initialize
    class.define_singleton_method("new", function!(Temperature::new, -1))?;

    class.define_method("to_kelvin", method!(Temperature::to_kelvin, 0))?;
    class.define_method("to_celsius", method!(Temperature::to_celsius, 0))?;
    class.define_method("to_fahrenheit", method!(Temperature::to_fahrenheit, 0))?;

    // make Ruby object cloneable, based on Rust Clone impl
    // #dup and #clone have slightly different behaviour in Ruby
    class.define_method("dup", method!(<Temperature as typed_data::Dup>::dup, 0))?;
    class.define_method(
        "clone",
        method!(<Temperature as typed_data::Dup>::clone, -1),
    )?;

    // enables use as a Hash key based on Rust Hash and Eq impl
    class.define_method(
        "eql?",
        method!(<Temperature as typed_data::IsEql>::is_eql, 1),
    )?;
    class.define_method("hash", method!(<Temperature as typed_data::Hash>::hash, 0))?;

    // <=> sort operator based on Rust PartialOrd impl
    class.define_method("<=>", method!(<Temperature as typed_data::Cmp>::cmp, 1))?;
    // defines <, <=, >, >=, and == based on <=>
    class.include_module(module::comparable())?;

    // debug/console output based on Rust Debug impl
    class.define_method(
        "inspect",
        method!(<Temperature as typed_data::Inspect>::inspect, 0),
    )?;

    // human output based on Rust Display impl
    class.define_method("to_s", method!(Temperature::to_string, 0))?;

    Ok(())
}
