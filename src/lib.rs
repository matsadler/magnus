pub mod block;
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
mod r_hash;
mod r_match;
mod r_module;
mod r_object;
mod r_rational;
mod r_regexp;
mod r_string;
pub mod r_struct;
pub mod r_typed_data;
pub mod ruby_sys;
mod symbol;
mod try_convert;
pub mod value;

use std::{ffi::CString, mem::transmute};

pub use magnus_macros::{init, DataTypeFunctions, TypedData};

use error::protect;
use method::Method;
use ruby_sys::{
    rb_define_class, rb_define_global_function, rb_define_module, rb_define_variable,
    rb_eval_string_protect, VALUE,
};

pub use value::{Fixnum, Flonum, QFALSE, QNIL, QTRUE, StaticSymbol, Value};
pub use {
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

pub mod prelude {
    pub use crate::{module::Module, object::Object};
}

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

pub fn define_class(name: &str, superclass: RClass) -> Result<RClass, Error> {
    debug_assert_value!(superclass);
    let name = CString::new(name).unwrap();
    let superclass = superclass.as_rb_value();
    unsafe {
        let res = protect(|| Value::new(rb_define_class(name.as_ptr(), superclass)));
        res.map(|v| RClass::from_value(v).unwrap())
    }
}

pub fn define_module(name: &str) -> Result<RModule, Error> {
    let name = CString::new(name).unwrap();
    unsafe {
        let res = protect(|| Value::new(rb_define_module(name.as_ptr())));
        res.map(|v| RModule::from_value(v).unwrap())
    }
}

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

pub fn define_global_function<M>(name: &str, func: M)
where
    M: Method,
{
    let name = CString::new(name).unwrap();
    unsafe {
        rb_define_global_function(name.as_ptr(), transmute(func.as_ptr()), M::arity().into());
    }
}

pub fn eval_static(s: &'static str) -> Result<Value, Error> {
    let mut state = 0;
    // safe ffi to Ruby, captures raised errors (+ brake, throw, etc) as state
    let result = unsafe {
        let s = CString::new(s).expect("NULL byte in eval string");
        rb_eval_string_protect(s.as_c_str().as_ptr(), &mut state as *mut _)
    };

    if state == 0 {
        Ok(Value::new(result))
    } else {
        Err(Error::Jump(unsafe { transmute(state) }))
    }
}
