use std::os::raw::c_int;

use crate::{
    error::Error,
    protect,
    r_array::RArray,
    ruby_sys::{rb_block_given_p, rb_yield, rb_yield_splat, rb_yield_values2, VALUE},
    try_convert::{TryConvert, ValueArray},
    value::Value,
};

pub fn block_given() -> bool {
    unsafe { rb_block_given_p() != 0 }
}

pub fn yield_value<T, U>(val: T) -> Result<U, Error>
where
    T: Into<Value>,
    for<'a> U: TryConvert<'a>,
{
    let val = val.into();
    unsafe { protect(|| Value::new(rb_yield(val.into_inner()))).and_then(|v| v.try_convert()) }
}

pub fn yield_values<T, U>(vals: T) -> Result<U, Error>
where
    T: ValueArray,
    for<'a> U: TryConvert<'a>,
{
    let vals = vals.into();
    let slice = vals.as_ref();
    unsafe {
        protect(|| {
            Value::new(rb_yield_values2(
                slice.len() as c_int,
                slice.as_ptr() as *const VALUE,
            ))
        })
        .and_then(|v| v.try_convert())
    }
}

pub fn yield_splat<T>(vals: RArray) -> Result<T, Error>
where
    for<'a> T: TryConvert<'a>,
{
    unsafe {
        protect(|| Value::new(rb_yield_splat(vals.into_inner()))).and_then(|v| v.try_convert())
    }
}
