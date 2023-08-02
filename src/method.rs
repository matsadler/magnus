//! Traits for exposing Rust functions as Ruby methods.

#![allow(clippy::too_many_arguments)]
#![allow(clippy::many_single_char_names)]
#![allow(clippy::missing_safety_doc)]

use std::{ffi::c_void, os::raw::c_int, panic::AssertUnwindSafe, slice};

use seq_macro::seq;

use crate::{
    block::{
        do_yield_iter, do_yield_splat_iter, do_yield_values_iter, Proc, Yield, YieldSplat,
        YieldValues,
    },
    error::{raise, Error},
    into_value::{ArgList, IntoValue},
    r_array::RArray,
    try_convert::TryConvert,
    value::{ReprValue, Value},
    Ruby,
};

mod private {
    use super::*;

    pub unsafe trait Method {
        fn arity() -> i8;
        #[allow(clippy::wrong_self_convention)]
        fn as_ptr(self) -> *mut c_void;
    }

    unsafe impl Method for unsafe extern "C" fn(Value, RArray) -> Value {
        fn arity() -> i8 {
            -2
        }

        fn as_ptr(self) -> *mut c_void {
            self as *mut c_void
        }
    }

    unsafe impl Method for unsafe extern "C" fn(c_int, *const Value, Value) -> Value {
        fn arity() -> i8 {
            -1
        }

        fn as_ptr(self) -> *mut c_void {
            self as *mut c_void
        }
    }

    macro_rules! impl_method {
        ($n:literal) => {
            seq!(_ in 0..=$n {
                unsafe impl Method for unsafe extern "C" fn(#(Value,)*) -> Value {
                    fn arity() -> i8 {
                        $n
                    }

                    fn as_ptr(self) -> *mut c_void {
                        self as *mut c_void
                    }
                }
            });
        }
    }

    seq!(N in 0..=16 {
        impl_method!(N);
    });

    pub trait ReturnValue {
        fn into_return_value(self) -> Result<Value, Error>;
    }

    impl<T> ReturnValue for Result<T, Error>
    where
        T: IntoValue,
    {
        fn into_return_value(self) -> Result<Value, Error> {
            self.map(|val| unsafe { val.into_value_unchecked() })
        }
    }

    impl<T> ReturnValue for T
    where
        T: IntoValue,
    {
        fn into_return_value(self) -> Result<Value, Error> {
            Ok(self).into_return_value()
        }
    }

    impl<I, T> ReturnValue for Yield<I>
    where
        I: Iterator<Item = T>,
        T: IntoValue,
    {
        fn into_return_value(self) -> Result<Value, Error> {
            match self {
                Yield::Iter(iter) => unsafe {
                    do_yield_iter(iter);
                    Ok(Ruby::get_unchecked().qnil().as_value())
                },
                Yield::Enumerator(e) => Ok(unsafe { e.into_value_unchecked() }),
            }
        }
    }

    impl<I, T> ReturnValue for Result<Yield<I>, Error>
    where
        I: Iterator<Item = T>,
        T: IntoValue,
    {
        fn into_return_value(self) -> Result<Value, Error> {
            self?.into_return_value()
        }
    }

    impl<I, T> ReturnValue for YieldValues<I>
    where
        I: Iterator<Item = T>,
        T: ArgList,
    {
        fn into_return_value(self) -> Result<Value, Error> {
            match self {
                YieldValues::Iter(iter) => unsafe {
                    do_yield_values_iter(iter);
                    Ok(Ruby::get_unchecked().qnil().as_value())
                },
                YieldValues::Enumerator(e) => Ok(unsafe { e.into_value_unchecked() }),
            }
        }
    }

    impl<I, T> ReturnValue for Result<YieldValues<I>, Error>
    where
        I: Iterator<Item = T>,
        T: ArgList,
    {
        fn into_return_value(self) -> Result<Value, Error> {
            self?.into_return_value()
        }
    }

    impl<I> ReturnValue for YieldSplat<I>
    where
        I: Iterator<Item = RArray>,
    {
        fn into_return_value(self) -> Result<Value, Error> {
            match self {
                YieldSplat::Iter(iter) => unsafe {
                    do_yield_splat_iter(iter);
                    Ok(Ruby::get_unchecked().qnil().as_value())
                },
                YieldSplat::Enumerator(e) => Ok(unsafe { e.into_value_unchecked() }),
            }
        }
    }

    impl<I> ReturnValue for Result<YieldSplat<I>, Error>
    where
        I: Iterator<Item = RArray>,
    {
        fn into_return_value(self) -> Result<Value, Error> {
            self?.into_return_value()
        }
    }

    pub trait InitReturn {
        fn into_init_return(self) -> Result<(), Error>;
    }

    impl InitReturn for () {
        fn into_init_return(self) -> Result<(), Error> {
            Ok(())
        }
    }

    impl InitReturn for Result<(), Error> {
        fn into_init_return(self) -> Result<(), Error> {
            self
        }
    }

    pub trait BlockReturn {
        fn into_block_return(self) -> Result<Value, Error>;
    }

    impl<T> BlockReturn for Result<T, Error>
    where
        T: IntoValue,
    {
        fn into_block_return(self) -> Result<Value, Error> {
            self.map(|val| unsafe { val.into_value_unchecked() })
        }
    }

    impl<T> BlockReturn for T
    where
        T: IntoValue,
    {
        fn into_block_return(self) -> Result<Value, Error> {
            Ok(self).into_block_return()
        }
    }
}

/// Trait implemented for function pointers that can be registed as Ruby
/// methods.
///
/// While it is possible to directly write functions that will automatically
/// implement this trait it is not recommended, as those functions will not
/// have the type conversions or error handling usually provided by this
/// library. See the [`method`](crate::method!) and
/// [`function`](crate::function!) macros for converting functions to an
/// implementor of this trait.
///
/// This trait is implemented for the following function signatures:
///
/// | Arity | Signature                                                    |
/// |-------|--------------------------------------------------------------|
/// |    -2 | `unsafe extern "C" fn(Value, RArray) -> Value;`              |
/// |    -1 | `unsafe extern "C" fn(c_int, *const Value, Value) -> Value;` |
/// |     0 | `unsafe extern "C" fn(Value) -> Value;`                      |
/// |     1 | `unsafe extern "C" fn(Value, Value) -> Value;`               |
/// |     2 | `unsafe extern "C" fn(Value, Value, Value) -> Value;`        |
/// |   ... | ...                                                          |
/// |    16 | ...                                                          |
///
/// note: for arity 0..=16 the number of arguments is 1 greater than the arity,
/// due to the initial `self` argument.
pub trait Method: private::Method {}

impl<T> Method for T where T: private::Method {}

/// Trait marking types that can be returned to Ruby.
///
/// Implemented for the following types:
///
/// * `T`
/// * [`Yield<I>`]
/// * [`YieldValues<I>`]
/// * [`YieldSplat<I>`]
/// * `Result<T, magnus::Error>`
/// * `Result<Yield<I>, magnus::Error>`
/// * `Result<YieldValues<I>, magnus::Error>`
/// * `Result<YieldSplat<I>, magnus::Error>`
///
/// where `I` implements `Iterator<Item = T>` and `T` implements [`IntoValue`].
///
/// When is `Err(magnus::Error)` returned to Ruby it will be conveted to and
/// raised as a Ruby exception.
///
/// [`Yield`], [`YieldValues`], and [`YieldSplat`] allow returning a Rust
/// [`Iterator`] to be bridged to Ruby method that calls a block with the
/// elements of that [`Iterator`].
///
/// Note: functions without a specified return value will return `()`. `()`
/// implements [`IntoValue`] (converting to `nil`).
pub trait ReturnValue: private::ReturnValue {}

impl<T> ReturnValue for T where T: private::ReturnValue {}

/// Trait marking types that can be returned to Ruby from a library
/// [`init`](magnus_macros::init) function.
///
/// Implemented for the following types:
///
/// * `()`
/// * `Result<(), magnus::Error>`
///
/// When is `Err(magnus::Error)` returned to Ruby it will be conveted to and
/// raised as a Ruby exception.
///
/// Note: functions without a specified return value will return `()`. `()`
/// implements [`IntoValue`] (converting to `nil`).
pub trait InitReturn: private::InitReturn {}

impl<T> InitReturn for T where T: private::InitReturn {}

/// Trait marking types that can be returned to Ruby from a block.
///
/// Implemented for the following types:
///
/// * `T`
/// * `Result<T, magnus::Error>`
///
/// where `T` implements [`IntoValue`].
///
/// When is `Err(magnus::Error)` returned to Ruby it will be conveted to and
/// raised as a Ruby exception.
///
/// Note: functions without a specified return value will return `()`. `()`
/// implements [`IntoValue`] (converting to `nil`).
pub trait BlockReturn: private::BlockReturn {}

impl<T> BlockReturn for T where T: private::BlockReturn {}

/// Helper trait for wrapping a function with type conversions and error
/// handling, as an 'init' function.
///
/// See the [`init`](magnus_macros::init) macro.
#[doc(hidden)]
pub trait Init<Res>
where
    Self: Sized + Fn() -> Res,
    Res: InitReturn,
{
    #[inline]
    unsafe fn call_handle_error(self) {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| (self)().into_init_return())) {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(e)),
        };
        match res {
            Ok(v) => v,
            Err(e) => raise(e),
        }
    }
}

impl<Func, Res> Init<Res> for Func
where
    Func: Fn() -> Res,
    Res: InitReturn,
{
}

/// Helper trait for wrapping a function with type conversions and error
/// handling, as an 'init' function being passed [`&Ruby`](Ruby).
///
/// See the [`init`](magnus_macros::init) macro.
#[doc(hidden)]
pub trait RubyInit<Res>
where
    Self: Sized + Fn(&Ruby) -> Res,
    Res: InitReturn,
{
    #[inline]
    unsafe fn call_handle_error(self) {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
            (self)(&Ruby::get_unchecked()).into_init_return()
        })) {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(e)),
        };
        match res {
            Ok(v) => v,
            Err(e) => raise(e),
        }
    }
}

impl<Func, Res> RubyInit<Res> for Func
where
    Func: Fn(&Ruby) -> Res,
    Res: InitReturn,
{
}

/// Helper trait for wrapping a function with type conversions and error
/// handling, as an 'block' function.
///
/// See the [`Value::block_call`] function.
#[doc(hidden)]
pub trait Block<Res>
where
    Self: Sized + FnMut(&[Value], Option<Proc>) -> Res,
    Res: BlockReturn,
{
    #[inline]
    unsafe fn call_convert_value(
        mut self,
        argc: c_int,
        argv: *const Value,
        blockarg: Value,
    ) -> Result<Value, Error> {
        let args = slice::from_raw_parts(argv, argc as usize);
        (self)(args, Proc::from_value(blockarg)).into_block_return()
    }

    #[inline]
    unsafe fn call_handle_error(self, argc: c_int, argv: *const Value, blockarg: Value) -> Value {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
            self.call_convert_value(argc, argv, blockarg)
        })) {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(e)),
        };
        match res {
            Ok(v) => v,
            Err(e) => raise(e),
        }
    }
}

impl<Func, Res> Block<Res> for Func
where
    Func: FnMut(&[Value], Option<Proc>) -> Res,
    Res: BlockReturn,
{
}

/// Helper trait for wrapping a function with type conversions and error
/// handling, when creating a thread.
///
/// See the [`Ruby::thread_create`] function.
#[doc(hidden)]
pub trait Thread<Res>
where
    Self: Sized + FnOnce(&Ruby) -> Res,
    Res: BlockReturn,
{
    #[inline]
    unsafe fn call_convert_value(self) -> Result<Value, Error> {
        (self)(&Ruby::get_unchecked()).into_block_return()
    }

    #[inline]
    unsafe fn call_handle_error(self) -> Value {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| self.call_convert_value())) {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(e)),
        };
        match res {
            Ok(v) => v,
            Err(e) => raise(e),
        }
    }
}

impl<Func, Res> Thread<Res> for Func
where
    Func: FnOnce(&Ruby) -> Res,
    Res: BlockReturn,
{
}

/// Helper trait for wrapping a function as a Ruby method taking self and a
/// Ruby array of arguments, with type conversions and error handling.
///
/// See the [`method`](crate::method!) macro.
#[doc(hidden)]
pub trait MethodRbAry<RbSelf, Args, Res>
where
    Self: Sized + Fn(RbSelf, Args) -> Res,
    RbSelf: TryConvert,
    Args: TryConvert,
    Res: ReturnValue,
{
    #[inline]
    fn call_convert_value(self, rb_self: Value, args: RArray) -> Result<Value, Error> {
        (self)(
            TryConvert::try_convert(rb_self)?,
            TryConvert::try_convert(args.as_value())?,
        )
        .into_return_value()
    }

    #[inline]
    unsafe fn call_handle_error(self, rb_self: Value, args: RArray) -> Value {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
            self.call_convert_value(rb_self, args)
        })) {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(e)),
        };
        match res {
            Ok(v) => v,
            Err(e) => raise(e),
        }
    }
}

impl<Func, RbSelf, Args, Res> MethodRbAry<RbSelf, Args, Res> for Func
where
    Func: Fn(RbSelf, Args) -> Res,
    RbSelf: TryConvert,
    Args: TryConvert,
    Res: ReturnValue,
{
}

/// Helper trait for wrapping a function as a Ruby method taking
/// [`&Ruby`](Ruby), self, and a Ruby array of arguments, with type conversions
/// and error handling.
///
/// See the [`method`](crate::method!) macro.
#[doc(hidden)]
pub trait RubyMethodRbAry<RbSelf, Args, Res>
where
    Self: Sized + Fn(&Ruby, RbSelf, Args) -> Res,
    RbSelf: TryConvert,
    Args: TryConvert,
    Res: ReturnValue,
{
    #[inline]
    fn call_convert_value(self, rb_self: Value, args: RArray) -> Result<Value, Error> {
        (self)(
            &Ruby::get_with(rb_self),
            TryConvert::try_convert(rb_self)?,
            TryConvert::try_convert(args.as_value())?,
        )
        .into_return_value()
    }

    #[inline]
    unsafe fn call_handle_error(self, rb_self: Value, args: RArray) -> Value {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
            self.call_convert_value(rb_self, args)
        })) {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(e)),
        };
        match res {
            Ok(v) => v,
            Err(e) => raise(e),
        }
    }
}

impl<Func, RbSelf, Args, Res> RubyMethodRbAry<RbSelf, Args, Res> for Func
where
    Func: Fn(&Ruby, RbSelf, Args) -> Res,
    RbSelf: TryConvert,
    Args: TryConvert,
    Res: ReturnValue,
{
}

/// Helper trait for wrapping a function as a Ruby method taking self and a
/// slice of arguments, with type conversions and error handling.
///
/// See the [`method`](crate::method!) macro.
#[doc(hidden)]
pub trait MethodCAry<RbSelf, Res>
where
    Self: Sized + Fn(RbSelf, &[Value]) -> Res,
    RbSelf: TryConvert,
    Res: ReturnValue,
{
    #[inline]
    unsafe fn call_convert_value(
        self,
        argc: c_int,
        argv: *const Value,
        rb_self: Value,
    ) -> Result<Value, Error> {
        let args = slice::from_raw_parts(argv, argc as usize);
        (self)(TryConvert::try_convert(rb_self)?, args).into_return_value()
    }

    #[inline]
    unsafe fn call_handle_error(self, argc: c_int, argv: *const Value, rb_self: Value) -> Value {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
            self.call_convert_value(argc, argv, rb_self)
        })) {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(e)),
        };
        match res {
            Ok(v) => v,
            Err(e) => raise(e),
        }
    }
}

impl<Func, RbSelf, Res> MethodCAry<RbSelf, Res> for Func
where
    Func: Fn(RbSelf, &[Value]) -> Res,
    RbSelf: TryConvert,
    Res: ReturnValue,
{
}

/// Helper trait for wrapping a function as a Ruby method taking
/// [`&Ruby`](Ruby), self, and a slice of arguments, with type conversions and
/// error handling.
///
/// See the [`method`](crate::method!) macro.
#[doc(hidden)]
pub trait RubyMethodCAry<RbSelf, Res>
where
    Self: Sized + Fn(&Ruby, RbSelf, &[Value]) -> Res,
    RbSelf: TryConvert,
    Res: ReturnValue,
{
    #[inline]
    unsafe fn call_convert_value(
        self,
        argc: c_int,
        argv: *const Value,
        rb_self: Value,
    ) -> Result<Value, Error> {
        let args = slice::from_raw_parts(argv, argc as usize);
        (self)(
            &Ruby::get_with(rb_self),
            TryConvert::try_convert(rb_self)?,
            args,
        )
        .into_return_value()
    }

    #[inline]
    unsafe fn call_handle_error(self, argc: c_int, argv: *const Value, rb_self: Value) -> Value {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
            self.call_convert_value(argc, argv, rb_self)
        })) {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(e)),
        };
        match res {
            Ok(v) => v,
            Err(e) => raise(e),
        }
    }
}

impl<Func, RbSelf, Res> RubyMethodCAry<RbSelf, Res> for Func
where
    Func: Fn(&Ruby, RbSelf, &[Value]) -> Res,
    RbSelf: TryConvert,
    Res: ReturnValue,
{
}

macro_rules! method_n {
    ($name:ident, $ruby_name:ident, $n:literal) => {
        seq!(N in 0..$n {
            /// Helper trait for wrapping a function as a Ruby method taking
            /// self and N arguments, with type conversions and error handling.
            ///
            /// See the [`method`](crate::method!) macro.
            #[doc(hidden)]
            pub trait $name<RbSelf, #(T~N,)* Res>
            where
                Self: Sized + Fn(RbSelf, #(T~N,)*) -> Res,
                RbSelf: TryConvert,
                #(T~N: TryConvert,)*
                Res: ReturnValue,
            {
                #[inline]
                fn call_convert_value(self, rb_self: Value, #(arg~N: Value,)*) -> Result<Value, Error> {
                    (self)(
                        TryConvert::try_convert(rb_self)?,
                        #(TryConvert::try_convert(arg~N)?,)*
                    ).into_return_value()
                }

                #[inline]
                unsafe fn call_handle_error(self, rb_self: Value, #(arg~N: Value,)*) -> Value {
                    let res =
                        match std::panic::catch_unwind(AssertUnwindSafe(|| {
                            self.call_convert_value(rb_self, #(arg~N,)*)
                        })) {
                            Ok(v) => v,
                            Err(e) => Err(Error::from_panic(e)),
                        };
                    match res {
                        Ok(v) => v,
                        Err(e) => raise(e),
                    }
                }
            }

            impl<Func, RbSelf, #(T~N,)* Res> $name<RbSelf, #(T~N,)* Res> for Func
            where
                Func: Fn(RbSelf, #(T~N,)*) -> Res,
                RbSelf: TryConvert,
                #(T~N: TryConvert,)*
                Res: ReturnValue,
            {}

            /// Helper trait for wrapping a function as a Ruby method taking
            /// [`&Ruby`](Ruby), self, and N arguments, with type conversions
            /// and error handling.
            ///
            /// See the [`method`](crate::method!) macro.
            #[doc(hidden)]
            pub trait $ruby_name<RbSelf, #(T~N,)* Res>
            where
                Self: Sized + Fn(&Ruby, RbSelf, #(T~N,)*) -> Res,
                RbSelf: TryConvert,
                #(T~N: TryConvert,)*
                Res: ReturnValue,
            {
                #[inline]
                fn call_convert_value(self, rb_self: Value, #(arg~N: Value,)*) -> Result<Value, Error> {
                    (self)(
                        &Ruby::get_with(rb_self),
                        TryConvert::try_convert(rb_self)?,
                        #(TryConvert::try_convert(arg~N)?,)*
                    ).into_return_value()
                }

                #[inline]
                unsafe fn call_handle_error(self, rb_self: Value, #(arg~N: Value,)*) -> Value {
                    let res =
                        match std::panic::catch_unwind(AssertUnwindSafe(|| {
                            self.call_convert_value(rb_self, #(arg~N,)*)
                        })) {
                            Ok(v) => v,
                            Err(e) => Err(Error::from_panic(e)),
                        };
                    match res {
                        Ok(v) => v,
                        Err(e) => raise(e),
                    }
                }
            }

            impl<Func, RbSelf, #(T~N,)* Res> $ruby_name<RbSelf, #(T~N,)* Res> for Func
            where
                Func: Fn(&Ruby, RbSelf, #(T~N,)*) -> Res,
                RbSelf: TryConvert,
                #(T~N: TryConvert,)*
                Res: ReturnValue,
            {}
        });
    }
}

seq!(N in 0..=16 {
    method_n!(Method~N, RubyMethod~N, N);
});

/// Wrap a Rust function item with Ruby type conversion and error handling.
///
/// This macro wraps the given function and returns a function pointer
/// implementing the [`Method`] trait, suitable for passing to functions that
/// define Ruby methods such as
/// [`define_method`](crate::module::Module::define_method).
///
/// Ruby code implicitly always has a `self` parameter available. In the
/// extention API this is passed explicitly. As a result there is always an
/// extra `self` argument before the arguments explitly passed in Ruby, and the
/// number of Rust argument will be one more than the Ruby arity.
///
/// The values `-2` and `-1` for `arity` have special meaning. Both indicate
/// functions with any number of arguments, with `-2` the arguments are passed
/// as a [`RArray`], with `-1` they are passed as a slice of [`Value`]s.
/// Arity of `-1` can be used with [`scan_args`](crate::scan_args::scan_args)
/// and [`get_kwargs`](crate::scan_args::get_kwargs) for more complex method
/// signatures.
///
/// | Arity | Signature                                                 |
/// |-------|-----------------------------------------------------------|
/// |    -2 | `fn(rb_self: T, arguments: RArray) -> Result<R, Error>`   |
/// |    -1 | `fn(rb_self: T, arguments: &[Value]) -> Result<R, Error>` |
/// |     0 | `fn(rb_self: T) -> Result<R, Error>`                      |
/// |     1 | `fn(rb_self: T, arg1: U) -> Result<R, Error>`             |
/// |     2 | `fn(rb_self: T, arg1: U, arg2: V) -> Result<R, Error>`    |
/// |   ... | ...                                                       |
/// |    16 | ...                                                       |
///
/// Where `T`, `U`, `V` and so on are any types that implement `TryConvert`,
/// and `R` implements [`IntoValue`]. It is also possible to return just `R`
/// rather than a `Result` for functions that will never error, and omit the
/// return value (i.e. return `()`) for a function that returns `nil` to Ruby.
/// See [`ReturnValue`] for more details on what can be returned.
///
/// See the [`function`](crate::function!) macro for cases where there is no
/// need to handle the `self` argument.
///
/// # Examples
///
/// ```
/// use magnus::{class, define_class, method, prelude::*, Error};
///
/// fn rb_is_blank(rb_self: String) -> bool {
///     rb_self.contains(|c: char| !c.is_whitespace())
/// }
///
/// #[magnus::init]
/// fn init() -> Result<(), Error> {
///     let class = define_class("String", class::object())?;
///     class.define_method("blank?", method!(rb_is_blank, 0))?;
///     Ok(())
/// }
/// # let _cleanup = unsafe { magnus::embed::init() };
/// # init().unwrap();
/// ```
#[macro_export]
macro_rules! method {
    ($name:expr, -2) => {{
        unsafe extern "C" fn anon(rb_self: $crate::Value, args: $crate::RArray) -> $crate::Value {
            use $crate::method::{MethodRbAry, RubyMethodRbAry};
            $name.call_handle_error(rb_self, args)
        }
        anon as unsafe extern "C" fn($crate::Value, $crate::RArray) -> $crate::Value
    }};
    ($name:expr, -1) => {{
        unsafe extern "C" fn anon(
            argc: std::os::raw::c_int,
            argv: *const $crate::Value,
            rb_self: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{MethodCAry, RubyMethodCAry};
            $name.call_handle_error(argc, argv, rb_self)
        }
        anon as unsafe extern "C" fn(
            std::os::raw::c_int,
            *const $crate::Value,
            $crate::Value,
        ) -> $crate::Value
    }};
    ($name:expr, 0) => {{
        unsafe extern "C" fn anon(rb_self: $crate::Value) -> $crate::Value {
            use $crate::method::{Method0, RubyMethod0};
            $name.call_handle_error(rb_self)
        }
        anon as unsafe extern "C" fn($crate::Value) -> $crate::Value
    }};
    ($name:expr, 1) => {{
        unsafe extern "C" fn anon(rb_self: $crate::Value, a: $crate::Value) -> $crate::Value {
            use $crate::method::{Method1, RubyMethod1};
            $name.call_handle_error(rb_self, a)
        }
        anon as unsafe extern "C" fn($crate::Value, $crate::Value) -> $crate::Value
    }};
    ($name:expr, 2) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{Method2, RubyMethod2};
            $name.call_handle_error(rb_self, a, b)
        }
        anon as unsafe extern "C" fn($crate::Value, $crate::Value, $crate::Value) -> $crate::Value
    }};
    ($name:expr, 3) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
            c: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{Method3, RubyMethod3};
            $name.call_handle_error(rb_self, a, b, c)
        }
        anon as unsafe extern "C" fn(
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
        ) -> $crate::Value
    }};
    ($name:expr, 4) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
            c: $crate::Value,
            d: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{Method4, RubyMethod4};
            $name.call_handle_error(rb_self, a, b, c, d)
        }
        anon as unsafe extern "C" fn(
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
        ) -> $crate::Value
    }};
    ($name:expr, 5) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
            c: $crate::Value,
            d: $crate::Value,
            e: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{Method5, RubyMethod5};
            $name.call_handle_error(rb_self, a, b, c, d, e)
        }
        anon as unsafe extern "C" fn(
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
        ) -> $crate::Value
    }};
    ($name:expr, 6) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
            c: $crate::Value,
            d: $crate::Value,
            e: $crate::Value,
            f: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{Method6, RubyMethod6};
            $name.call_handle_error(rb_self, a, b, c, d, e, f)
        }
        anon as unsafe extern "C" fn(
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
        ) -> $crate::Value
    }};
    ($name:expr, 7) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
            c: $crate::Value,
            d: $crate::Value,
            e: $crate::Value,
            f: $crate::Value,
            g: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{Method7, RubyMethod7};
            $name.call_handle_error(rb_self, a, b, c, d, e, f, g)
        }
        anon as unsafe extern "C" fn(
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
        ) -> $crate::Value
    }};
    ($name:expr, 8) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
            c: $crate::Value,
            d: $crate::Value,
            e: $crate::Value,
            f: $crate::Value,
            g: $crate::Value,
            h: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{Method8, RubyMethod8};
            $name.call_handle_error(rb_self, a, b, c, d, e, f, g, h)
        }
        anon as unsafe extern "C" fn(
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
        ) -> $crate::Value
    }};
    ($name:expr, 9) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
            c: $crate::Value,
            d: $crate::Value,
            e: $crate::Value,
            f: $crate::Value,
            g: $crate::Value,
            h: $crate::Value,
            i: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{Method9, RubyMethod9};
            $name.call_handle_error(rb_self, a, b, c, d, e, f, g, h, i)
        }
        anon as unsafe extern "C" fn(
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
        ) -> $crate::Value
    }};
    ($name:expr, 10) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
            c: $crate::Value,
            d: $crate::Value,
            e: $crate::Value,
            f: $crate::Value,
            g: $crate::Value,
            h: $crate::Value,
            i: $crate::Value,
            j: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{Method10, RubyMethod10};
            $name.call_handle_error(rb_self, a, b, c, d, e, f, g, h, i, j)
        }
        anon as unsafe extern "C" fn(
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
        ) -> $crate::Value
    }};
    ($name:expr, 11) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
            c: $crate::Value,
            d: $crate::Value,
            e: $crate::Value,
            f: $crate::Value,
            g: $crate::Value,
            h: $crate::Value,
            i: $crate::Value,
            j: $crate::Value,
            k: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{Method11, RubyMethod11};
            $name.call_handle_error(rb_self, a, b, c, d, e, f, g, h, i, j, k)
        }
        anon as unsafe extern "C" fn(
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
        ) -> $crate::Value
    }};
    ($name:expr, 12) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
            c: $crate::Value,
            d: $crate::Value,
            e: $crate::Value,
            f: $crate::Value,
            g: $crate::Value,
            h: $crate::Value,
            i: $crate::Value,
            j: $crate::Value,
            k: $crate::Value,
            l: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{Method12, RubyMethod12};
            $name.call_handle_error(rb_self, a, b, c, d, e, f, g, h, i, j, k, l)
        }
        anon as unsafe extern "C" fn(
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
        ) -> $crate::Value
    }};
    ($name:expr, 13) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
            c: $crate::Value,
            d: $crate::Value,
            e: $crate::Value,
            f: $crate::Value,
            g: $crate::Value,
            h: $crate::Value,
            i: $crate::Value,
            j: $crate::Value,
            k: $crate::Value,
            l: $crate::Value,
            m: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{Method13, RubyMethod13};
            $name.call_handle_error(rb_self, a, b, c, d, e, f, g, h, i, j, k, l, m)
        }
        anon as unsafe extern "C" fn(
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
        ) -> $crate::Value
    }};
    ($name:expr, 14) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
            c: $crate::Value,
            d: $crate::Value,
            e: $crate::Value,
            f: $crate::Value,
            g: $crate::Value,
            h: $crate::Value,
            i: $crate::Value,
            j: $crate::Value,
            k: $crate::Value,
            l: $crate::Value,
            m: $crate::Value,
            n: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{Method14, RubyMethod14};
            $name.call_handle_error(rb_self, a, b, c, d, e, f, g, h, i, j, k, l, m, n)
        }
        anon as unsafe extern "C" fn(
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
        ) -> $crate::Value
    }};
    ($name:expr, 15) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
            c: $crate::Value,
            d: $crate::Value,
            e: $crate::Value,
            f: $crate::Value,
            g: $crate::Value,
            h: $crate::Value,
            i: $crate::Value,
            j: $crate::Value,
            k: $crate::Value,
            l: $crate::Value,
            m: $crate::Value,
            n: $crate::Value,
            o: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{Method15, RubyMethod15};
            $name.call_handle_error(rb_self, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o)
        }
        anon as unsafe extern "C" fn(
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
        ) -> $crate::Value
    }};
    ($name:expr, 16) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
            c: $crate::Value,
            d: $crate::Value,
            e: $crate::Value,
            f: $crate::Value,
            g: $crate::Value,
            h: $crate::Value,
            i: $crate::Value,
            j: $crate::Value,
            k: $crate::Value,
            l: $crate::Value,
            m: $crate::Value,
            n: $crate::Value,
            o: $crate::Value,
            p: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{Method16, RubyMethod16};
            $name.call_handle_error(rb_self, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p)
        }
        anon as unsafe extern "C" fn(
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
        ) -> $crate::Value
    }};
    ($name:expr, $arity:expr) => {
        compile_error!("arity must be an integer literal between -2..=16")
    };
}

/// Helper trait for wrapping a function as a Ruby method ignoring self and
/// taking a Ruby array of arguments, with type conversions and error handling.
///
/// See the [`function`](crate::function!) macro.
#[doc(hidden)]
pub trait FunctionRbAry<Args, Res>
where
    Self: Sized + Fn(Args) -> Res,
    Args: TryConvert,
    Res: ReturnValue,
{
    #[inline]
    fn call_convert_value(self, args: RArray) -> Result<Value, Error> {
        (self)(TryConvert::try_convert(args.as_value())?).into_return_value()
    }

    #[inline]
    unsafe fn call_handle_error(self, args: RArray) -> Value {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| self.call_convert_value(args)))
        {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(e)),
        };
        match res {
            Ok(v) => v,
            Err(e) => raise(e),
        }
    }
}

impl<Func, Args, Res> FunctionRbAry<Args, Res> for Func
where
    Func: Fn(Args) -> Res,
    Args: TryConvert,
    Res: ReturnValue,
{
}

/// Helper trait for wrapping a function as a Ruby method taking
/// [`&Ruby`](Ruby), ignoring self, and taking a Ruby array of arguments, with
/// type conversions and error handling.
///
/// See the [`function`](crate::function!) macro.
#[doc(hidden)]
pub trait RubyFunctionRbAry<Args, Res>
where
    Self: Sized + Fn(&Ruby, Args) -> Res,
    Args: TryConvert,
    Res: ReturnValue,
{
    #[inline]
    fn call_convert_value(self, args: RArray) -> Result<Value, Error> {
        (self)(
            &Ruby::get_with(args),
            TryConvert::try_convert(args.as_value())?,
        )
        .into_return_value()
    }

    #[inline]
    unsafe fn call_handle_error(self, args: RArray) -> Value {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| self.call_convert_value(args)))
        {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(e)),
        };
        match res {
            Ok(v) => v,
            Err(e) => raise(e),
        }
    }
}

impl<Func, Args, Res> RubyFunctionRbAry<Args, Res> for Func
where
    Func: Fn(&Ruby, Args) -> Res,
    Args: TryConvert,
    Res: ReturnValue,
{
}

/// Helper trait for wrapping a function as a Ruby method ignoring self and
/// taking a slice of arguments, with type conversions and error handling.
///
/// See the [`function`](crate::function!) macro.
#[doc(hidden)]
pub trait FunctionCAry<Res>
where
    Self: Sized + Fn(&[Value]) -> Res,
    Res: ReturnValue,
{
    #[inline]
    unsafe fn call_convert_value(self, argc: c_int, argv: *const Value) -> Result<Value, Error> {
        let args = slice::from_raw_parts(argv, argc as usize);
        (self)(args).into_return_value()
    }

    #[inline]
    unsafe fn call_handle_error(self, argc: c_int, argv: *const Value) -> Value {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
            self.call_convert_value(argc, argv)
        })) {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(e)),
        };
        match res {
            Ok(v) => v,
            Err(e) => raise(e),
        }
    }
}

impl<Func, Res> FunctionCAry<Res> for Func
where
    Func: Fn(&[Value]) -> Res,
    Res: ReturnValue,
{
}

/// Helper trait for wrapping a function as a Ruby method taking
/// [`&Ruby`](Ruby), ignoring self, and taking a slice of arguments, with type
/// conversions and error handling.
///
/// See the [`function`](crate::function!) macro.
#[doc(hidden)]
pub trait RubyFunctionCAry<Res>
where
    Self: Sized + Fn(&Ruby, &[Value]) -> Res,
    Res: ReturnValue,
{
    #[inline]
    unsafe fn call_convert_value(self, argc: c_int, argv: *const Value) -> Result<Value, Error> {
        let args = slice::from_raw_parts(argv, argc as usize);
        (self)(&Ruby::get_unchecked(), args).into_return_value()
    }

    #[inline]
    unsafe fn call_handle_error(self, argc: c_int, argv: *const Value) -> Value {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
            self.call_convert_value(argc, argv)
        })) {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(e)),
        };
        match res {
            Ok(v) => v,
            Err(e) => raise(e),
        }
    }
}

impl<Func, Res> RubyFunctionCAry<Res> for Func
where
    Func: Fn(&Ruby, &[Value]) -> Res,
    Res: ReturnValue,
{
}

macro_rules! function_n {
    ($name:ident, $ruby_name:ident, $n:literal) => {
        seq!(N in 0..$n {
            /// Helper trait for wrapping a function as a Ruby method ignoring
            /// self and taking N arguments, with type conversions and error
            /// handling.
            ///
            /// See the [`function`](crate::function!) macro.
            #[doc(hidden)]
            pub trait $name<#(T~N,)* Res>
            where
                Self: Sized + Fn(#(T~N,)*) -> Res,
                #(T~N: TryConvert,)*
                Res: ReturnValue,
            {
                #[inline]
                fn call_convert_value(self, #(arg~N: Value,)*) -> Result<Value, Error> {
                    (self)(
                        #(TryConvert::try_convert(arg~N)?,)*
                    ).into_return_value()
                }

                #[inline]
                unsafe fn call_handle_error(self, #(arg~N: Value,)*) -> Value {
                    let res =
                        match std::panic::catch_unwind(AssertUnwindSafe(|| {
                            self.call_convert_value(#(arg~N,)*)
                        })) {
                            Ok(v) => v,
                            Err(e) => Err(Error::from_panic(e)),
                        };
                    match res {
                        Ok(v) => v,
                        Err(e) => raise(e),
                    }
                }
            }

            impl<Func, #(T~N,)* Res> $name<#(T~N,)* Res> for Func
            where
                Func: Fn(#(T~N,)*) -> Res,
                #(T~N: TryConvert,)*
                Res: ReturnValue,
            {}

            /// Helper trait for wrapping a function as a Ruby method taking
            /// [`&Ruby`](Ruby), ignoring self, and taking N arguments, with
            /// type conversions and error handling.
            ///
            /// See the [`function`](crate::function!) macro.
            #[doc(hidden)]
            pub trait $ruby_name<#(T~N,)* Res>
            where
                Self: Sized + Fn(&Ruby, #(T~N,)*) -> Res,
                #(T~N: TryConvert,)*
                Res: ReturnValue,
            {
                #[inline]
                unsafe fn call_convert_value(self, #(arg~N: Value,)*) -> Result<Value, Error> {
                    (self)(
                        &Ruby::get_unchecked(),
                        #(TryConvert::try_convert(arg~N)?,)*
                    ).into_return_value()
                }

                #[inline]
                unsafe fn call_handle_error(self, #(arg~N: Value,)*) -> Value {
                    let res =
                        match std::panic::catch_unwind(AssertUnwindSafe(|| {
                            self.call_convert_value(#(arg~N,)*)
                        })) {
                            Ok(v) => v,
                            Err(e) => Err(Error::from_panic(e)),
                        };
                    match res {
                        Ok(v) => v,
                        Err(e) => raise(e),
                    }
                }
            }

            impl<Func, #(T~N,)* Res> $ruby_name<#(T~N,)* Res> for Func
            where
                Func: Fn(&Ruby, #(T~N,)*) -> Res,
                #(T~N: TryConvert,)*
                Res: ReturnValue,
            {}
        });
    }
}

seq!(N in 0..=16 {
    function_n!(Function~N, RubyFunction~N, N);
});

/// Wrap a Rust function item with Ruby type conversion and error handling,
/// ignoring Ruby's `self` argument.
///
/// This macro wraps the given function and returns a function pointer
/// implementing the [`Method`] trait, suitable for passing to functions that
/// define Ruby methods such as
/// [`define_method`](crate::module::Module::define_method).
///
/// Ruby code implicitly always has a `self` parameter available. In the
/// extention API this is passed explicitly. The wrapper this macro generates
/// ignores that argument, and does not pass it to the wrapped function.
///
/// The values `-2` and `-1` for `arity` have special meaning. Both indicate
/// functions with any number of arguments, with `-2` the arguments are passed
/// as a [`RArray`], with `-1` they are passed as a slice of [`Value`]s.
/// Arity of `-1` can be used with [`scan_args`](crate::scan_args::scan_args)
/// and [`get_kwargs`](crate::scan_args::get_kwargs) for more complex method
/// signatures.
///
/// | Arity | Signature                                     |
/// |-------|-----------------------------------------------|
/// |    -2 | `fn(arguments: RArray) -> Result<R, Error>`   |
/// |    -1 | `fn(arguments: &[Value]) -> Result<R, Error>` |
/// |     0 | `fn()-> Result<R, Error>`                     |
/// |     1 | `fn(arg1: T) -> Result<R, Error>`             |
/// |     2 | `fn(arg1: T, arg2: U) -> Result<R, Error>`    |
/// |   ... | ...                                           |
/// |    16 | ...                                           |
///
/// Where `T`, `U`, and so on are any types that implement `TryConvert`,
/// and `R` implements [`IntoValue`]. It is also possible to return just `R`
/// rather than a `Result` for functions that will never error, and omit the
/// return value (i.e. return `()`) for a function that returns `nil` to Ruby.
/// See [`ReturnValue`] for more details on what can be returned.
///
/// See the [`method`](crate::method!) macro for cases where the `self`
/// argument is required.
///
/// # Examples
///
/// ```
/// fn distance(a: (f64, f64), b: (f64, f64)) -> f64 {
///     ((b.0 - a.0).powi(2) + (b.0 - a.0).powi(2)).sqrt()
/// }
///
/// #[magnus::init]
/// fn init() {
///     magnus::define_global_function("distance", magnus::function!(distance, 2));
/// }
/// # let _cleanup = unsafe { magnus::embed::init() };
/// # init();
/// ```
#[macro_export]
macro_rules! function {
    ($name:expr, -2) => {{
        unsafe extern "C" fn anon(rb_self: $crate::Value, args: $crate::RArray) -> $crate::Value {
            use $crate::method::{FunctionRbAry, RubyFunctionRbAry};
            $name.call_handle_error(args)
        }
        anon as unsafe extern "C" fn($crate::Value, $crate::RArray) -> $crate::Value
    }};
    ($name:expr, -1) => {{
        unsafe extern "C" fn anon(
            argc: std::os::raw::c_int,
            argv: *const $crate::Value,
            rb_self: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{FunctionCAry, RubyFunctionCAry};
            $name.call_handle_error(argc, argv)
        }
        anon as unsafe extern "C" fn(
            std::os::raw::c_int,
            *const $crate::Value,
            $crate::Value,
        ) -> $crate::Value
    }};
    ($name:expr, 0) => {{
        unsafe extern "C" fn anon(rb_self: $crate::Value) -> $crate::Value {
            use $crate::method::{Function0, RubyFunction0};
            $name.call_handle_error()
        }
        anon as unsafe extern "C" fn($crate::Value) -> $crate::Value
    }};
    ($name:expr, 1) => {{
        unsafe extern "C" fn anon(rb_self: $crate::Value, a: $crate::Value) -> $crate::Value {
            use $crate::method::{Function1, RubyFunction1};
            $name.call_handle_error(a)
        }
        anon as unsafe extern "C" fn($crate::Value, $crate::Value) -> $crate::Value
    }};
    ($name:expr, 2) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{Function2, RubyFunction2};
            $name.call_handle_error(a, b)
        }
        anon as unsafe extern "C" fn($crate::Value, $crate::Value, $crate::Value) -> $crate::Value
    }};
    ($name:expr, 3) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
            c: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{Function3, RubyFunction3};
            $name.call_handle_error(a, b, c)
        }
        anon as unsafe extern "C" fn(
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
        ) -> $crate::Value
    }};
    ($name:expr, 4) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
            c: $crate::Value,
            d: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{Function4, RubyFunction4};
            $name.call_handle_error(a, b, c, d)
        }
        anon as unsafe extern "C" fn(
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
        ) -> $crate::Value
    }};
    ($name:expr, 5) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
            c: $crate::Value,
            d: $crate::Value,
            e: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{Function5, RubyFunction5};
            $name.call_handle_error(a, b, c, d, e)
        }
        anon as unsafe extern "C" fn(
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
        ) -> $crate::Value
    }};
    ($name:expr, 6) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
            c: $crate::Value,
            d: $crate::Value,
            e: $crate::Value,
            f: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{Function6, RubyFunction6};
            $name.call_handle_error(a, b, c, d, e, f)
        }
        anon as unsafe extern "C" fn(
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
        ) -> $crate::Value
    }};
    ($name:expr, 7) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
            c: $crate::Value,
            d: $crate::Value,
            e: $crate::Value,
            f: $crate::Value,
            g: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{Function7, RubyFunction7};
            $name.call_handle_error(a, b, c, d, e, f, g)
        }
        anon as unsafe extern "C" fn(
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
        ) -> $crate::Value
    }};
    ($name:expr, 8) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
            c: $crate::Value,
            d: $crate::Value,
            e: $crate::Value,
            f: $crate::Value,
            g: $crate::Value,
            h: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{Function8, RubyFunction8};
            $name.call_handle_error(a, b, c, d, e, f, g, h)
        }
        anon as unsafe extern "C" fn(
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
        ) -> $crate::Value
    }};
    ($name:expr, 9) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
            c: $crate::Value,
            d: $crate::Value,
            e: $crate::Value,
            f: $crate::Value,
            g: $crate::Value,
            h: $crate::Value,
            i: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{Function9, RubyFunction9};
            $name.call_handle_error(a, b, c, d, e, f, g, h, i)
        }
        anon as unsafe extern "C" fn(
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
        ) -> $crate::Value
    }};
    ($name:expr, 10) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
            c: $crate::Value,
            d: $crate::Value,
            e: $crate::Value,
            f: $crate::Value,
            g: $crate::Value,
            h: $crate::Value,
            i: $crate::Value,
            j: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{Function10, RubyFunction10};
            $name.call_handle_error(a, b, c, d, e, f, g, h, i, j)
        }
        anon as unsafe extern "C" fn(
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
        ) -> $crate::Value
    }};
    ($name:expr, 11) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
            c: $crate::Value,
            d: $crate::Value,
            e: $crate::Value,
            f: $crate::Value,
            g: $crate::Value,
            h: $crate::Value,
            i: $crate::Value,
            j: $crate::Value,
            k: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{Function11, RubyFunction11};
            $name.call_handle_error(a, b, c, d, e, f, g, h, i, j, k)
        }
        anon as unsafe extern "C" fn(
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
        ) -> $crate::Value
    }};
    ($name:expr, 12) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
            c: $crate::Value,
            d: $crate::Value,
            e: $crate::Value,
            f: $crate::Value,
            g: $crate::Value,
            h: $crate::Value,
            i: $crate::Value,
            j: $crate::Value,
            k: $crate::Value,
            l: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{Function12, RubyFunction12};
            $name.call_handle_error(a, b, c, d, e, f, g, h, i, j, k, l)
        }
        anon as unsafe extern "C" fn(
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
        ) -> $crate::Value
    }};
    ($name:expr, 13) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
            c: $crate::Value,
            d: $crate::Value,
            e: $crate::Value,
            f: $crate::Value,
            g: $crate::Value,
            h: $crate::Value,
            i: $crate::Value,
            j: $crate::Value,
            k: $crate::Value,
            l: $crate::Value,
            m: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{Function13, RubyFunction13};
            $name.call_handle_error(a, b, c, d, e, f, g, h, i, j, k, l, m)
        }
        anon as unsafe extern "C" fn(
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
        ) -> $crate::Value
    }};
    ($name:expr, 14) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
            c: $crate::Value,
            d: $crate::Value,
            e: $crate::Value,
            f: $crate::Value,
            g: $crate::Value,
            h: $crate::Value,
            i: $crate::Value,
            j: $crate::Value,
            k: $crate::Value,
            l: $crate::Value,
            m: $crate::Value,
            n: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{Function14, RubyFunction14};
            $name.call_handle_error(a, b, c, d, e, f, g, h, i, j, k, l, m, n)
        }
        anon as unsafe extern "C" fn(
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
        ) -> $crate::Value
    }};
    ($name:expr, 15) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
            c: $crate::Value,
            d: $crate::Value,
            e: $crate::Value,
            f: $crate::Value,
            g: $crate::Value,
            h: $crate::Value,
            i: $crate::Value,
            j: $crate::Value,
            k: $crate::Value,
            l: $crate::Value,
            m: $crate::Value,
            n: $crate::Value,
            o: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{Function15, RubyFunction15};
            $name.call_handle_error(a, b, c, d, e, f, g, h, i, j, k, l, m, n, o)
        }
        anon as unsafe extern "C" fn(
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
        ) -> $crate::Value
    }};
    ($name:expr, 16) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
            c: $crate::Value,
            d: $crate::Value,
            e: $crate::Value,
            f: $crate::Value,
            g: $crate::Value,
            h: $crate::Value,
            i: $crate::Value,
            j: $crate::Value,
            k: $crate::Value,
            l: $crate::Value,
            m: $crate::Value,
            n: $crate::Value,
            o: $crate::Value,
            p: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{Function16, RubyFunction16};
            $name.call_handle_error(a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p)
        }
        anon as unsafe extern "C" fn(
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
        ) -> $crate::Value
    }};
    ($name:expr, $arity:expr) => {
        compile_error!("arity must be an integer literal between -2..=16")
    };
}
