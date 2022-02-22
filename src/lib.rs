//! Magnus is a library for writing Ruby extentions in Rust, or running Ruby
//! code from Rust.
//!
//! # Examples
//!
//! ```
//! use magnus::{define_module, function, method, prelude::*, Error};
//!
//! #[magnus::wrap(class = "Euclid::Point", free_immediatly, size)]
//! struct Point {
//!     x: isize,
//!     y: isize,
//! }
//!
//! impl Point {
//!     fn new(x: isize, y: isize) -> Self {
//!         Self { x, y }
//!     }
//!
//!     fn x(&self) -> isize {
//!         self.x
//!     }
//!
//!     fn y(&self) -> isize {
//!         self.y
//!     }
//! }
//!
//! fn distance(a: &Point, b: &Point) -> f64 {
//!     (((b.x - a.x).pow(2) + (b.y - a.y).pow(2)) as f64).sqrt()
//! }
//!
//! #[magnus::init]
//! fn init() -> Result<(), Error> {
//!     let module = define_module("Euclid")?;
//!     let class = module.define_class("Point", Default::default())?;
//!     class.define_singleton_method("new", function!(Point::new, 2));
//!     class.define_method("x", method!(Point::x, 0));
//!     class.define_method("y", method!(Point::y, 0));
//!     module.define_module_function("distance", function!(distance, 2));
//!     Ok(())
//! }
//! ```
#![warn(missing_docs)]

mod binding;
pub mod block;
#[cfg(feature = "embed")]
pub mod embed;
mod enumerator;
pub mod error;
mod exception;
mod float;
mod integer;
pub mod method;
mod module;
mod object;
mod r_array;
mod r_bignum;
mod r_class;
mod r_complex;
mod r_file;
mod r_float;
pub mod r_hash;
mod r_match;
mod r_module;
mod r_object;
mod r_rational;
mod r_regexp;
pub mod r_string;
pub mod r_struct;
pub mod r_typed_data;
pub mod ruby_sys;
mod symbol;
mod try_convert;
pub mod value;

use std::{ffi::CString, mem::transmute};

pub use magnus_macros::{init, wrap, DataTypeFunctions, TypedData};

use error::protect;
use method::Method;
use ruby_sys::{
    rb_define_class, rb_define_global_function, rb_define_module, rb_define_variable, rb_errinfo,
    rb_eval_string_protect, rb_set_errinfo, VALUE,
};

pub use value::{Fixnum, Flonum, StaticSymbol, Value, QFALSE, QNIL, QTRUE};
pub use {
    binding::Binding,
    enumerator::Enumerator,
    error::Error,
    exception::{Exception, ExceptionClass},
    float::Float,
    integer::Integer,
    module::Module,
    object::Object,
    r_array::RArray,
    r_bignum::RBignum,
    r_class::RClass,
    r_complex::RComplex,
    r_file::RFile,
    r_float::RFloat,
    r_hash::RHash,
    r_match::RMatch,
    r_module::RModule,
    r_object::RObject,
    r_rational::RRational,
    r_regexp::RRegexp,
    r_string::RString,
    r_struct::RStruct,
    r_typed_data::{DataType, DataTypeFunctions, RTypedData, TypedData},
    symbol::Symbol,
    try_convert::{ArgList, TryConvert},
};

/// Traits that commonly should be in scope.
pub mod prelude {
    pub use crate::{module::Module, object::Object};
}

/// Utility to simplify initialising a static with [`std::sync::Once`].
///
/// Similar (but less generally useful) to
/// [`lazy_static!`](https://crates.io/crates/lazy_static) without an external
/// dependency.
///
/// # Examples
///
/// ```
/// use magnus::{define_class, memoize, RClass};
///
/// fn foo_class() -> &'static RClass {
///     memoize!(RClass: define_class("Foo", Default::default()).unwrap())
/// }
/// ```
#[macro_export]
macro_rules! memoize {
    ($type:ty: $val:expr) => {{
        static INIT: std::sync::Once = std::sync::Once::new();
        static mut VALUE: Option<$type> = None;
        unsafe {
            INIT.call_once(|| {
                VALUE = Some($val);
            });
            VALUE.as_ref().unwrap()
        }
    }};
}

/// Define a class in the root scope.
pub fn define_class(name: &str, superclass: RClass) -> Result<RClass, Error> {
    debug_assert_value!(superclass);
    let name = CString::new(name).unwrap();
    let superclass = superclass.as_rb_value();
    unsafe {
        let res = protect(|| Value::new(rb_define_class(name.as_ptr(), superclass)));
        res.map(|v| RClass::from_value(v).unwrap())
    }
}

/// Define a module in the root scope.
pub fn define_module(name: &str) -> Result<RModule, Error> {
    let name = CString::new(name).unwrap();
    unsafe {
        let res = protect(|| Value::new(rb_define_module(name.as_ptr())));
        res.map(|v| RModule::from_value(v).unwrap())
    }
}

/// Define a global variable.
pub fn define_global_variable<T: Into<Value>>(name: &str, initial: T) -> Result<*mut Value, Error> {
    let initial = initial.into();
    debug_assert_value!(initial);
    let name = CString::new(name).unwrap();
    let ptr = Box::into_raw(Box::new(initial));
    unsafe {
        rb_define_variable(name.as_ptr(), ptr as *mut VALUE);
    }
    Ok(ptr)
}

/// Define a method in the root scope.
pub fn define_global_function<M>(name: &str, func: M)
where
    M: Method,
{
    let name = CString::new(name).unwrap();
    unsafe {
        rb_define_global_function(name.as_ptr(), transmute(func.as_ptr()), M::arity().into());
    }
}

/// Evaluate a string of Ruby code, converting the result to a `T`.
///
/// Errors if `s` contains a null byte, the conversion fails, or on an uncaught
/// Ruby exception.
///
/// See also the [`eval`](macro@crate::eval) macro.
pub fn eval<T>(s: &str) -> Result<T, Error>
where
    T: TryConvert,
{
    let mut state = 0;
    // safe ffi to Ruby, captures raised errors (+ brake, throw, etc) as state
    let result = unsafe {
        let s = CString::new(s).map_err(|e| Error::script_error(e.to_string()))?;
        rb_eval_string_protect(s.as_c_str().as_ptr(), &mut state as *mut _)
    };

    match state {
        // Tag::None
        0 => Value::new(result).try_convert(),
        // Tag::Raise
        6 => unsafe {
            let ex = Exception::from_rb_value_unchecked(rb_errinfo());
            rb_set_errinfo(QNIL.as_rb_value());
            Err(Error::Exception(ex))
        },
        other => Err(Error::Jump(unsafe { transmute(other) })),
    }
}
