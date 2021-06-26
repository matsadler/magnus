use std::{fmt, mem::forget, ops::Deref, os::raw::c_int};

use crate::{
    enumerator::Enumerator,
    error::{ensure, protect, Error},
    r_array::RArray,
    ruby_sys::{
        rb_block_given_p, rb_block_proc, rb_obj_is_proc, rb_proc_call, rb_yield, rb_yield_splat,
        rb_yield_values2, VALUE,
    },
    try_convert::{ArgList, RArrayArgList, TryConvert},
    value::{NonZeroValue, Value},
};

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Proc(NonZeroValue);

impl Proc {
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            Value::new(rb_obj_is_proc(val.as_rb_value()))
                .to_bool()
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    pub fn call<A, T>(self, args: A) -> Result<T, Error>
    where
        A: RArrayArgList,
        T: TryConvert,
    {
        let args = args.into_array_arg_list();
        unsafe {
            protect(|| Value::new(rb_proc_call(self.as_rb_value(), args.as_rb_value())))
                .and_then(|v| v.try_convert())
        }
    }
}

impl Deref for Proc {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
    }
}

impl fmt::Display for Proc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for Proc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl From<Proc> for Value {
    fn from(val: Proc) -> Self {
        *val
    }
}

impl TryConvert for Proc {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        if let Some(p) = Proc::from_value(*val) {
            return Ok(p);
        }
        let p_val: Value = match val.funcall("to_proc", ()) {
            Ok(v) => v,
            Err(_) => {
                return Err(Error::type_error(format!(
                    "no implicit conversion of {} into Proc",
                    unsafe { val.classname() },
                )))
            }
        };
        Proc::from_value(*val).ok_or_else(|| {
            Error::type_error(format!(
                "can't convert {0} to Proc ({0}#to_proc gives {1})",
                unsafe { val.classname() },
                unsafe { p_val.classname() },
            ))
        })
    }
}

pub fn block_given() -> bool {
    unsafe { rb_block_given_p() != 0 }
}

pub fn block_proc() -> Result<Proc, Error> {
    let val = unsafe { protect(|| Value::new(rb_block_proc()))? };
    Ok(Proc::from_value(val).unwrap())
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
pub(crate) unsafe fn do_yield_iter<I, T>(mut iter: I)
where
    I: Iterator<Item = T>,
    T: Into<Value>,
{
    let ptr = &mut iter as *mut I;
    forget(iter); // we're going to drop this ourself;
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

// see do_yield_iter
pub(crate) unsafe fn do_yield_values_iter<I, T>(mut iter: I)
where
    I: Iterator<Item = T>,
    T: ArgList,
{
    let ptr = &mut iter as *mut I;
    forget(iter);
    ensure(
        || {
            for val in &mut *ptr {
                let vals = val.into_arg_list();
                let slice = vals.as_ref();
                rb_yield_values2(slice.len() as c_int, slice.as_ptr() as *const VALUE);
            }
            Value::default()
        },
        || {
            ptr.drop_in_place();
        },
    );
}

// see do_yield_iter
pub(crate) unsafe fn do_yield_splat_iter<I>(mut iter: I)
where
    I: Iterator<Item = RArray>,
{
    let ptr = &mut iter as *mut I;
    forget(iter);
    ensure(
        || {
            for val in &mut *ptr {
                rb_yield_splat(val.as_rb_value());
            }
            Value::default()
        },
        || {
            ptr.drop_in_place();
        },
    );
}

pub enum Yield<I> {
    Iter(I),
    Enumerator(Enumerator),
}

pub enum YieldValues<I> {
    Iter(I),
    Enumerator(Enumerator),
}

pub enum YieldSplat<I> {
    Iter(I),
    Enumerator(Enumerator),
}
