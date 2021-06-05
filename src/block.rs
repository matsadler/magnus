use std::{mem::forget, os::raw::c_int};

use crate::{
    enumerator::Enumerator,
    error::{ensure, protect, Error},
    r_array::RArray,
    ruby_sys::{rb_block_given_p, rb_yield, rb_yield_splat, rb_yield_values2, VALUE},
    try_convert::{ArgList, TryConvert},
    value::Value,
};

pub fn block_given() -> bool {
    unsafe { rb_block_given_p() != 0 }
}

pub fn yield_value<T, U>(val: T) -> Result<U, Error>
where
    T: Into<Value>,
    U: TryConvert,
{
    let val = val.into();
    unsafe { protect(|| Value::new(rb_yield(val.as_rb_value()))).and_then(|v| v.try_convert()) }
}

pub fn yield_values<T, U>(vals: T) -> Result<U, Error>
where
    T: ArgList,
    U: TryConvert,
{
    let vals = vals.into_arg_list();
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
    T: TryConvert,
{
    unsafe {
        protect(|| Value::new(rb_yield_splat(vals.as_rb_value()))).and_then(|v| v.try_convert())
    }
}

// Our regular implementation of `yield` breaks yielding methods being
// converted to Enumerators because of the protect call not being compatible
// with the fibers used in Ruby itself to impliment `Enumerator#next`.
// We have to use protect in `yield` because otherwise Ruby code can
// `break`/`return` through Rust code and break Rust invariants.
// This gives up using `protect` by instead using `ensure`, not exposing the
// `yield` call to user code, and maintaining the invariants ourselves. As it
// can still be `brake`/`return`ed though it can't be public as it's only safe
// to call as the last thing in one of our method wrappers (where the raise
// would normally go). Returning an iterator from a method will trigger this.
pub(crate) fn do_yield_iter<I, T>(mut iter: I)
where
    I: Iterator<Item = T>,
    T: Into<Value>,
{
    let ptr = &mut iter as *mut I;
    forget(iter); // we're going to drop this ourself;
    unsafe {
        // ensure runs the first closure, but yield may raise, so the first
        // closure might never reach the end, so wouldn't drop. The second
        // closure is always run, and always after the first, so we do the
        // drop there
        ensure(
            || {
                for val in &mut *ptr {
                    rb_yield(val.into().as_rb_value());
                }
                Value::default()
            },
            || {
                ptr.drop_in_place();
            },
        );
    }
}

pub enum Yield<I> {
    Iter(I),
    Enumerator(Enumerator),
}
