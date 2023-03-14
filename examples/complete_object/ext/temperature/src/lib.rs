use std::{
    cell::RefCell,
    fmt,
    hash::{Hash, Hasher},
};

use magnus::{
    class, define_class, exception, method, module,
    prelude::*,
    scan_args::{get_kwargs, scan_args},
    typed_data, Error, Value,
};

#[magnus::wrap(class = "Temperature", free_immediately, size)]
#[derive(Clone, Debug, Default, Eq, PartialEq, PartialOrd)]
struct Temperature {
    microkelvin: RefCell<u64>,
}

// can't derive this due to needing to use RefCell to get mutability
impl Hash for Temperature {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.microkelvin.borrow().hash(state)
    }
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
    fn initialize(rb_self: typed_data::Obj<Self>, args: &[Value]) -> Result<(), Error> {
        let args = scan_args::<(), (), (), (), _, ()>(args)?;
        let kwargs = get_kwargs::<_, (), (Option<f64>, Option<f64>, Option<f64>), ()>(
            args.keywords,
            &[],
            &["kelvin", "celsius", "fahrenheit"],
        )?;
        *rb_self.microkelvin.borrow_mut() = match kwargs.optional {
            (Some(k), None, None) => (k * FACTOR) as u64,
            (None, Some(c), None) => ((c + C_OFFSET) * FACTOR) as u64,
            (None, None, Some(f)) => ((f_to_c(f) + C_OFFSET) * FACTOR) as u64,
            (None, None, None) => {
                return Err(Error::new(
                    exception::arg_error(),
                    "missing keyword: :kelvin, :celsius, or :fahrenheit",
                ))
            }
            _ => {
                return Err(Error::new(
                    exception::arg_error(),
                    "unexpected keyword, supply one of: :kelvin, :celsius, or :fahrenheit",
                ))
            }
        };
        Ok(())
    }

    fn to_kelvin(&self) -> f64 {
        *self.microkelvin.borrow() as f64 / FACTOR
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

    // Define alloc func based on the Default impl, plus an initialize method,
    // rather than overwriting `new`, to allow class to be subclassed from Ruby
    class.define_alloc_func::<Temperature>();
    class.define_method("initialize", method!(Temperature::initialize, -1))?;

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
