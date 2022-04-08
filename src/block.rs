//! Types and functions for working with Ruby blocks and Procs.

use std::{fmt, mem::forget, ops::Deref, os::raw::c_int};

use crate::{
    enumerator::Enumerator,
    error::{ensure, protect, Error},
    exception,
    r_array::RArray,
    ruby_sys::{
        rb_block_given_p, rb_block_proc, rb_obj_is_proc, rb_proc_call, rb_yield, rb_yield_splat,
        rb_yield_values2, VALUE,
    },
    try_convert::{ArgList, RArrayArgList, TryConvert},
    value::{private, NonZeroValue, ReprValue, Value},
};

/// Wrapper type for a Value known to be an instance of Ruby’s Proc class.
///
/// All [`Value`] methods should be available on this type through [`Deref`],
/// but some may be missed by this documentation.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Proc(NonZeroValue);

impl Proc {
    /// Return `Some(Proc)` if `val` is a `Proc`, `None` otherwise.
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            Value::new(rb_obj_is_proc(val.as_rb_value()))
                .to_bool()
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    /// Call the proc with `args`.
    ///
    /// Returns `Ok(T)` if the proc runs without error and the return value
    /// converts into a `T`, or returns `Err` if the proc raises or the
    /// conversion fails.
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

unsafe impl private::ReprValue for Proc {
    fn to_value(self) -> Value {
        *self
    }

    unsafe fn from_value_unchecked(val: Value) -> Self {
        Self(NonZeroValue::new_unchecked(val))
    }
}

impl ReprValue for Proc {}

impl TryConvert for Proc {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        if let Some(p) = Proc::from_value(*val) {
            return Ok(p);
        }
        let p_val: Value = match val.funcall("to_proc", ()) {
            Ok(v) => v,
            Err(_) => {
                return Err(Error::new(
                    exception::type_error(),
                    format!("no implicit conversion of {} into Proc", unsafe {
                        val.classname()
                    },),
                ))
            }
        };
        Proc::from_value(*val).ok_or_else(|| {
            Error::new(
                exception::type_error(),
                format!(
                    "can't convert {0} to Proc ({0}#to_proc gives {1})",
                    unsafe { val.classname() },
                    unsafe { p_val.classname() },
                ),
            )
        })
    }
}

/// Returns whether a Ruby block has been supplied to the current method.
pub fn block_given() -> bool {
    unsafe { rb_block_given_p() != 0 }
}

/// Returns the block given to the current method as a [`Proc`] instance.
pub fn block_proc() -> Result<Proc, Error> {
    let val = unsafe { protect(|| Value::new(rb_block_proc()))? };
    Ok(Proc::from_value(val).unwrap())
}

/// Yields a value to the block given to the current method.
///
/// **Note:** A method using `yield_value` converted to an Enumerator with
/// `to_enum`/[`Value::enumeratorize`] will result in a non-functional
/// Enumerator. See [`Yield`] for an alternative.
pub fn yield_value<T, U>(val: T) -> Result<U, Error>
where
    T: Into<Value>,
    U: TryConvert,
{
    let val = val.into();
    unsafe { protect(|| Value::new(rb_yield(val.as_rb_value()))).and_then(|v| v.try_convert()) }
}

/// Yields multiple values to the block given to the current method.
///
/// **Note:** A method using `yield_values` converted to an Enumerator with
/// `to_enum`/[`Value::enumeratorize`] will result in a non-functional
/// Enumerator. See [`YieldValues`] for an alternative.
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

/// Yields a Ruby Array to the block given to the current method.
///
/// **Note:** A method using `yield_splat` converted to an Enumerator with
/// `to_enum`/[`Value::enumeratorize`] will result in a non-functional
/// Enumerator. See [`YieldValues`] for an alternative.
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

/// Helper type for functions that either yield a single value to a block or
/// return an Enumerator.
///
/// `I` must implement `Iterator<Item = T>`, where `T` implements `Into<Value>`.
///
/// # Examples
///
/// ```
/// use magnus::{block::{block_given, Yield}, Value};
///
/// fn count_to_3(rb_self: Value) -> Yield<impl Iterator<Item = u8>> {
///     if block_given() {
///         Yield::Iter((1..=3).into_iter())
///     } else {
///         Yield::Enumerator(rb_self.enumeratorize("count_to_3", ()))
///     }
/// }
/// ```
/// Could be called from Ruby like:
/// ``` text
/// a = []
/// count_to_3 {|i| a << i}   #=> nil
/// a                         #=> [1,2,3]
/// enumerator = count_to_3
/// enumerator.next           #=> 1
/// enumerator.next           #=> 2
/// ```
pub enum Yield<I> {
    /// Yields `I::Item` to given block.
    Iter(I),
    /// Returns `Enumerator` from the method.
    Enumerator(Enumerator),
}

/// Helper type for functions that either yield multiple values to a block or
/// return an Enumerator.
///
/// `I` must implement `Iterator<Item = T>`, where `T` implements [`ArgList`].
pub enum YieldValues<I> {
    /// Yields `I::Item` to given block.
    Iter(I),
    /// Returns `Enumerator` from the method.
    Enumerator(Enumerator),
}

/// Helper type for functions that either yield an array to a block or
/// return an Enumerator.
///
/// `I` must implement `Iterator<Item = RArray>`.
pub enum YieldSplat<I> {
    /// Yields `I::Item` to given block.
    Iter(I),
    /// Returns `Enumerator` from the method.
    Enumerator(Enumerator),
}
