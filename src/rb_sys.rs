//! Functions for interoperability with rb-sys.
//!
//! These functions are provided to interface with the lower-level Ruby
//! bindings provided by [rb-sys](rb_sys). You may want to use rb-sys when:
//!
//! 1. Magnus does not provide access to a Ruby API because the API can not be
//!    made safe & ergonomic.
//! 2. Magnus exposed the API in a way that does not work for your use case.
//! 3. The API just hasn't been implemented yet.
//!
//! Even if you are not in a position to contribute code to Magnus, please
//! [open an issue](https://github.com/matsadler/magnus/issues) outlining your
//! use case and the APIs you need whenever you find yourself reaching for this
//! module.
//!
//! # Stability
//!
//! Functions in this module are considered unstable. While there is no plan
//! to alter or remove them, non-backwards compatible changes in this module
//! will not necessarily be considered as SemVer major changes.
//!
//! # Safety
//!
//! The unsafe functions in this module are capable of producing values that
//! break the saftey guarantees of almost every other function in Magnus. Use
//! them with care.
use crate::{
    error::{self, raise, Error},
    exception::arg_error,
    value::{Id, Value},
};
use rb_sys::{ID, VALUE};
use std::{intrinsics::transmute, panic::UnwindSafe};

impl Value {
    /// Convert [`magnus::Value`](Value) to [`rb_sys::VALUE`](VALUE).
    ///
    /// ```
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// use magnus::{RString};
    ///
    /// let foo = RString::new("foo");
    /// let bar = RString::new("bar");
    ///
    /// unsafe { rb_sys::rb_str_buf_append(foo.into_raw(), bar.into_raw()) };
    ///
    /// assert_eq!(foo.to_string().unwrap(), "foobar");
    /// ```
    pub fn into_raw(self) -> VALUE {
        self.as_rb_value()
    }

    /// Convert [`rb_sys::VALUE`](VALUE) to [`magnus::Value`](Value).
    /// # Safety
    ///
    /// You must only supply a valid [`VALUE`] obtained from [rb-sys](rb_sys) to
    /// this function. Using a invalid [`Value`] produced from this function will
    /// void all saftey guarantees provided by Magnus.
    ///
    /// ```
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// use magnus::{RString, Value};
    ///
    /// let raw_value = unsafe { rb_sys::rb_str_new("foo".as_ptr() as *mut _, 3) };
    ///
    /// assert_eq!(unsafe { Value::from_raw(raw_value).unwrap().to_string() }, "foo");
    /// ```
    pub unsafe fn from_raw(val: VALUE) -> Result<Value, Error> {
        Ok(Value::new(val.into()))
    }
}

impl Id {
    /// Convert [`magnus::value::Id`](Id) to [`rb_sys::ID`](ID).
    ///
    /// ```
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// use magnus::{Symbol, value::Id};
    ///
    /// let foo: Id = Symbol::new("foo").into();
    /// let raw = foo.into_raw();
    /// let from_raw_val: Symbol = unsafe { Id::from_raw(raw).unwrap() }.into();
    ///
    /// assert_eq!(from_raw_val.inspect(), ":foo");
    /// ```
    pub fn into_raw(self) -> ID {
        self.as_rb_id()
    }

    /// Convert [`rb_sys::ID`](ID) to [`magnus::value::Id`](ID).
    ///
    /// # Safety
    ///
    /// You must only supply a valid, non-zero [`ID`] obtained from [rb-sys](rb_sys) to this
    /// function. Using a invalid [`Id`] produced from this function will void all
    /// saftey guarantees provided by Magnus.
    ///
    /// ```
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// use magnus::{Symbol, value::Id};
    /// use std::convert::TryInto;
    ///
    /// let foo: Id = Symbol::new("foo").into();
    /// let from_raw_val: Symbol = unsafe { Id::from_raw(foo.into_raw()).unwrap() }.into();
    ///
    /// assert_eq!(from_raw_val.inspect(), ":foo");
    /// assert!(unsafe { Id::from_raw(0) }.is_err());
    /// ```
    pub unsafe fn from_raw(id: ID) -> Result<Id, Error> {
        // Be nice and try to prevent some obvious seg-faults
        if Value::is_immediate(transmute::<ID, Value>(id)) {
            return Err(Error::new(
                arg_error(),
                "cannot convert special_const_p to Id",
            ));
        }

        Ok(Id::new(id.into()))
    }
}

/// Calls the given closure, catching all cases of unwinding from Ruby
/// returning them as an [`Error`].
///
/// The most common will be exceptions, but this will also catch `throw`,
/// `break`, `next`, `return` from a block, etc.
///
/// All functions exposed by Magnus that call Ruby in a way that may unwind
/// already use this internally, this should only be required to wrap functions
/// from [rb-sys](rb_sys).
pub fn protect<F>(func: F) -> Result<VALUE, Error>
where
    F: FnOnce() -> VALUE,
{
    error::protect(|| Value::new(func())).map(|v| v.as_rb_value())
}

/// Attempts to catch cases of Rust unwinding, converting to a fatal [`Error`].
///
/// This should not be used to catch and discard panics.
///
/// This function can be used to ensure Rust panics do not cross over to Ruby.
/// This will convert a panic to a Ruby fatal [`Error`] that can then be used
/// to safely terminate Ruby.
///
/// All functions exposed by Magnus that allow Ruby to call Rust code already
/// use this internally, this should only be required to wrap
/// functions/closures given directly to [rb-sys](rb_sys).
pub fn catch_unwind<F, T>(func: F) -> Result<T, Error>
where
    F: FnOnce() -> T + UnwindSafe,
{
    std::panic::catch_unwind(func).map_err(Error::from_panic)
}

/// Resumes an [`Error`] previously caught by [`protect`].
///
/// All functions exposed by Magnus where it is safe to resume an error use
/// this internally to automatically convert returned errors to raised
/// exceptions. This should only be required to in functions/closures given
/// directly to [rb-sys](rb_sys).
///
/// # Safety
///
/// Beware this function does not return and breaks the normal assumption that
/// Rust code does not unwind during normal behaviour. This can break
/// invariants in code that assumes unwinding only happens during terminating
/// panics.
///
/// If possible, only call this at the very end of a function/closure that is
/// directly called by Ruby, not other Rust code, and ensure all other values
/// in scope have been dropped before calling this function.
pub unsafe fn resume_error(e: Error) -> ! {
    raise(e)
}

/// Convert [`magnus::Value`](Value) to [`rb_sys::VALUE`].
#[deprecated(since = "0.3.3", note = "please use `Value::into_raw` instead")]
pub fn raw_value(val: Value) -> VALUE {
    val.into_raw()
}

/// Convert [`rb_sys::VALUE`] to [`magnus::Value`](Value).
///
/// # Safety
///
/// You must only supply a valid [`VALUE`] obtained from [rb-sys](rb_sys) to
/// this function. Using a invalid [`Value`] produced from this function will
/// void all saftey guarantees provided by Magnus.
#[deprecated(since = "0.3.3", note = "please use `Value::from_raw` instead")]
pub unsafe fn value_from_raw(val: VALUE) -> Value {
    Value::from_raw(val).unwrap()
}

/// Convert [`magnus::value::Id`](Id) to [`rb_sys::ID`].
#[deprecated(since = "0.3.3", note = "please use `Id::into_raw` instead")]
pub fn raw_id(id: Id) -> ID {
    id.into_raw()
}

/// Convert [`rb_sys::ID`] to [`magnus::value::Id`](Id).
///
/// # Safety
///
/// You must only supply a valid [`ID`] obtained from [rb-sys](rb_sys) to this
/// function. Using a invalid [`Id`] produced from this function will void all
/// saftey guarantees provided by Magnus.
#[deprecated(since = "0.3.3", note = "please use `Id::from_raw` instead")]
pub unsafe fn id_from_raw(id: ID) -> Id {
    Id::from_raw(id).unwrap()
}
