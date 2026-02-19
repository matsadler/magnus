//! Traits for exposing Rust functions as Ruby methods.

#![allow(clippy::too_many_arguments)]
#![allow(clippy::many_single_char_names)]
#![allow(clippy::missing_safety_doc)]

use std::{
    ffi::{c_int, c_void},
    panic::AssertUnwindSafe,
    slice,
};

use seq_macro::seq;

use crate::{
    Ruby,
    block::{
        Proc, Yield, YieldSplat, YieldValues, do_yield_iter, do_yield_splat_iter,
        do_yield_values_iter,
    },
    debug::{DebugInspector, TracePoint},
    error::{Error, IntoError, raise},
    into_value::{ArgList, IntoValue},
    r_array::RArray,
    try_convert::TryConvert,
    value::{ReprValue, Value},
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

    seq!(N in 0..=15 {
        impl_method!(N);
    });

    pub trait ReturnValue {
        fn into_return_value_with(self, ruby: &Ruby) -> Result<Value, Error>;
    }

    impl<T, E> ReturnValue for Result<T, E>
    where
        T: IntoValue,
        E: IntoError,
    {
        fn into_return_value_with(self, ruby: &Ruby) -> Result<Value, Error> {
            self.map(|val| val.into_value_with(ruby))
                .map_err(|err| err.into_error(ruby))
        }
    }

    impl<T> ReturnValue for T
    where
        T: IntoValue,
    {
        fn into_return_value_with(self, ruby: &Ruby) -> Result<Value, Error> {
            Ok::<T, Error>(self).into_return_value_with(ruby)
        }
    }

    impl<I, T, E> ReturnValue for Result<Yield<I>, E>
    where
        I: Iterator<Item = T>,
        T: IntoValue,
        E: IntoError,
    {
        fn into_return_value_with(self, ruby: &Ruby) -> Result<Value, Error> {
            self.map(|i| match i {
                Yield::Iter(iter) => unsafe {
                    do_yield_iter(ruby, iter);
                    ruby.qnil().as_value()
                },
                Yield::Enumerator(e) => e.into_value_with(ruby),
            })
            .map_err(|err| err.into_error(ruby))
        }
    }

    impl<I, T> ReturnValue for Yield<I>
    where
        I: Iterator<Item = T>,
        T: IntoValue,
    {
        fn into_return_value_with(self, ruby: &Ruby) -> Result<Value, Error> {
            Ok::<Self, Error>(self).into_return_value_with(ruby)
        }
    }

    impl<I, T, E> ReturnValue for Result<YieldValues<I>, E>
    where
        I: Iterator<Item = T>,
        T: ArgList,
        E: IntoError,
    {
        fn into_return_value_with(self, ruby: &Ruby) -> Result<Value, Error> {
            self.map(|i| match i {
                YieldValues::Iter(iter) => unsafe {
                    do_yield_values_iter(ruby, iter);
                    ruby.qnil().as_value()
                },
                YieldValues::Enumerator(e) => e.into_value_with(ruby),
            })
            .map_err(|err| err.into_error(ruby))
        }
    }

    impl<I, T> ReturnValue for YieldValues<I>
    where
        I: Iterator<Item = T>,
        T: ArgList,
    {
        fn into_return_value_with(self, ruby: &Ruby) -> Result<Value, Error> {
            Ok::<Self, Error>(self).into_return_value_with(ruby)
        }
    }

    impl<I, E> ReturnValue for Result<YieldSplat<I>, E>
    where
        I: Iterator<Item = RArray>,
        E: IntoError,
    {
        fn into_return_value_with(self, ruby: &Ruby) -> Result<Value, Error> {
            self.map(|i| match i {
                YieldSplat::Iter(iter) => unsafe {
                    do_yield_splat_iter(ruby, iter);
                    ruby.qnil().as_value()
                },
                YieldSplat::Enumerator(e) => e.into_value_with(ruby),
            })
            .map_err(|err| err.into_error(ruby))
        }
    }

    impl<I> ReturnValue for YieldSplat<I>
    where
        I: Iterator<Item = RArray>,
    {
        fn into_return_value_with(self, ruby: &Ruby) -> Result<Value, Error> {
            Ok::<Self, Error>(self).into_return_value_with(ruby)
        }
    }

    pub trait InitReturn {
        fn into_init_return_with(self, ruby: &Ruby) -> Result<(), Error>;
    }

    impl InitReturn for () {
        fn into_init_return_with(self, _ruby: &Ruby) -> Result<(), Error> {
            Ok(())
        }
    }

    impl<E> InitReturn for Result<(), E>
    where
        E: IntoError,
    {
        fn into_init_return_with(self, ruby: &Ruby) -> Result<(), Error> {
            self.map_err(|err| err.into_error(ruby))
        }
    }

    pub trait BlockReturn {
        fn into_block_return_with(self, ruby: &Ruby) -> Result<Value, Error>;
    }

    impl<T> BlockReturn for Result<T, Error>
    where
        T: IntoValue,
    {
        fn into_block_return_with(self, ruby: &Ruby) -> Result<Value, Error> {
            self.map(|val| val.into_value_with(ruby))
        }
    }

    impl<T> BlockReturn for T
    where
        T: IntoValue,
    {
        fn into_block_return_with(self, ruby: &Ruby) -> Result<Value, Error> {
            Ok(self).into_block_return_with(ruby)
        }
    }
}

/// Trait implemented for function pointers that can be registered as Ruby
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
/// |    15 | ...                                                          |
///
/// note: for arity 0..=15 the number of arguments is 1 greater than the arity,
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
/// When is `Err(magnus::Error)` returned to Ruby it will be converted to and
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
/// When is `Err(magnus::Error)` returned to Ruby it will be converted to and
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
/// When is `Err(magnus::Error)` returned to Ruby it will be converted to and
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
    unsafe fn call_handle_error(self, ruby: &Ruby) {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
            (self)().into_init_return_with(ruby)
        })) {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(ruby, e)),
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
    unsafe fn call_handle_error(self, ruby: &Ruby) {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
            (self)(ruby).into_init_return_with(ruby)
        })) {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(ruby, e)),
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
    Self: Sized + FnOnce(&Ruby, &[Value], Option<Proc>) -> Res,
    Res: BlockReturn,
{
    #[inline]
    unsafe fn call_convert_value(
        self,
        ruby: &Ruby,
        argc: c_int,
        argv: *const Value,
        blockarg: Value,
    ) -> Result<Value, Error> {
        unsafe {
            let args = slice::from_raw_parts(argv, argc as usize);
            (self)(ruby, args, Proc::from_value(blockarg)).into_block_return_with(ruby)
        }
    }

    #[inline]
    unsafe fn call_handle_error(
        self,
        ruby: &Ruby,
        argc: c_int,
        argv: *const Value,
        blockarg: Value,
    ) -> Value {
        unsafe {
            let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
                self.call_convert_value(ruby, argc, argv, blockarg)
            })) {
                Ok(v) => v,
                Err(e) => Err(Error::from_panic(ruby, e)),
            };
            match res {
                Ok(v) => v,
                Err(e) => raise(e),
            }
        }
    }
}

impl<Func, Res> Block<Res> for Func
where
    Func: FnOnce(&Ruby, &[Value], Option<Proc>) -> Res,
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
    fn call_convert_value(self, ruby: &Ruby) -> Result<Value, Error> {
        (self)(ruby).into_block_return_with(ruby)
    }

    #[inline]
    unsafe fn call_handle_error(self, ruby: &Ruby) -> Value {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| self.call_convert_value(ruby)))
        {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(ruby, e)),
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

/// Helper trait for wrapping a function with type conversions and error
/// handling, when calling [`Mutex::synchronize`](crate::Mutext::synchronize).
#[doc(hidden)]
pub trait Synchronize<Res>
where
    Self: Sized + FnOnce() -> Res,
    Res: BlockReturn,
{
    #[inline]
    fn call_convert_value(self, ruby: &Ruby) -> Result<Value, Error> {
        (self)().into_block_return_with(ruby)
    }

    #[inline]
    unsafe fn call_handle_error(self, ruby: &Ruby) -> Value {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| self.call_convert_value(ruby)))
        {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(ruby, e)),
        };
        match res {
            Ok(v) => v,
            Err(e) => raise(e),
        }
    }
}

impl<Func, Res> Synchronize<Res> for Func
where
    Func: FnOnce() -> Res,
    Res: BlockReturn,
{
}

/// Helper trait for wrapping a function with type conversions and error
/// handling, when opening a debug inspector.
///
/// See the [`Ruby::debug_inspector_open`] function.
#[doc(hidden)]
pub trait DebugInspectorOpen<Res>
where
    Self: Sized + FnOnce(DebugInspector) -> Res,
    Res: BlockReturn,
{
    #[inline]
    fn call_convert_value(self, ruby: &Ruby, dc: DebugInspector) -> Result<Value, Error> {
        (self)(dc).into_block_return_with(ruby)
    }

    #[inline]
    unsafe fn call_handle_error(self, ruby: &Ruby, dc: DebugInspector) -> Value {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
            self.call_convert_value(ruby, dc)
        })) {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(ruby, e)),
        };
        match res {
            Ok(v) => v,
            Err(e) => raise(e),
        }
    }
}

impl<Func, Res> DebugInspectorOpen<Res> for Func
where
    Func: FnOnce(DebugInspector) -> Res,
    Res: BlockReturn,
{
}

/// Helper trait for wrapping a function with type conversions and error
/// handling, for use as a TracePoint callback.
///
/// See the [`Ruby::tracepoint_new`] function.
#[doc(hidden)]
pub trait TracePointNew<Res>
where
    Self: Sized + FnMut(TracePoint) -> Res,
    Res: InitReturn,
{
    #[inline]
    unsafe fn call_handle_error(mut self, tp: TracePoint) {
        let ruby = Ruby::get_with(tp);
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
            (self)(tp).into_init_return_with(&ruby)
        })) {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(&ruby, e)),
        };
        match res {
            Ok(v) => v,
            Err(e) => raise(e),
        }
    }
}

impl<Func, Res> TracePointNew<Res> for Func
where
    Func: FnMut(TracePoint) -> Res,
    Res: InitReturn,
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
    fn call_convert_value(self, ruby: &Ruby, rb_self: Value, args: RArray) -> Result<Value, Error> {
        (self)(
            TryConvert::try_convert(rb_self)?,
            TryConvert::try_convert(args.as_value())?,
        )
        .into_return_value_with(ruby)
    }

    #[inline]
    unsafe fn call_handle_error(self, ruby: &Ruby, rb_self: Value, args: RArray) -> Value {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
            self.call_convert_value(ruby, rb_self, args)
        })) {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(ruby, e)),
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
    fn call_convert_value(self, ruby: &Ruby, rb_self: Value, args: RArray) -> Result<Value, Error> {
        (self)(
            ruby,
            TryConvert::try_convert(rb_self)?,
            TryConvert::try_convert(args.as_value())?,
        )
        .into_return_value_with(ruby)
    }

    #[inline]
    unsafe fn call_handle_error(self, ruby: &Ruby, rb_self: Value, args: RArray) -> Value {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
            self.call_convert_value(ruby, rb_self, args)
        })) {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(ruby, e)),
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
        ruby: &Ruby,
        argc: c_int,
        argv: *const Value,
        rb_self: Value,
    ) -> Result<Value, Error> {
        unsafe {
            let args = slice::from_raw_parts(argv, argc as usize);
            (self)(TryConvert::try_convert(rb_self)?, args).into_return_value_with(ruby)
        }
    }

    #[inline]
    unsafe fn call_handle_error(
        self,
        ruby: &Ruby,
        argc: c_int,
        argv: *const Value,
        rb_self: Value,
    ) -> Value {
        unsafe {
            let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
                self.call_convert_value(ruby, argc, argv, rb_self)
            })) {
                Ok(v) => v,
                Err(e) => Err(Error::from_panic(ruby, e)),
            };
            match res {
                Ok(v) => v,
                Err(e) => raise(e),
            }
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
        ruby: &Ruby,
        argc: c_int,
        argv: *const Value,
        rb_self: Value,
    ) -> Result<Value, Error> {
        unsafe {
            let args = slice::from_raw_parts(argv, argc as usize);
            (self)(ruby, TryConvert::try_convert(rb_self)?, args).into_return_value_with(ruby)
        }
    }

    #[inline]
    unsafe fn call_handle_error(
        self,
        ruby: &Ruby,
        argc: c_int,
        argv: *const Value,
        rb_self: Value,
    ) -> Value {
        unsafe {
            let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
                self.call_convert_value(ruby, argc, argv, rb_self)
            })) {
                Ok(v) => v,
                Err(e) => Err(Error::from_panic(ruby, e)),
            };
            match res {
                Ok(v) => v,
                Err(e) => raise(e),
            }
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
                fn call_convert_value(self, ruby: &Ruby, rb_self: Value, #(arg~N: Value,)*) -> Result<Value, Error> {
                    (self)(
                        TryConvert::try_convert(rb_self)?,
                        #(TryConvert::try_convert(arg~N)?,)*
                    ).into_return_value_with(ruby)
                }

                #[inline]
                unsafe fn call_handle_error(self, ruby: &Ruby, rb_self: Value, #(arg~N: Value,)*) -> Value {
                    let res =
                        match std::panic::catch_unwind(AssertUnwindSafe(|| {
                            self.call_convert_value(ruby, rb_self, #(arg~N,)*)
                        })) {
                            Ok(v) => v,
                            Err(e) => Err(Error::from_panic(ruby, e)),
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
                fn call_convert_value(self, ruby: &Ruby, rb_self: Value, #(arg~N: Value,)*) -> Result<Value, Error> {
                    (self)(
                        ruby,
                        TryConvert::try_convert(rb_self)?,
                        #(TryConvert::try_convert(arg~N)?,)*
                    ).into_return_value_with(ruby)
                }

                #[inline]
                unsafe fn call_handle_error(self, ruby: &Ruby, rb_self: Value, #(arg~N: Value,)*) -> Value {
                    let res =
                        match std::panic::catch_unwind(AssertUnwindSafe(|| {
                            self.call_convert_value(ruby, rb_self, #(arg~N,)*)
                        })) {
                            Ok(v) => v,
                            Err(e) => Err(Error::from_panic(ruby, e)),
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

seq!(N in 0..=15 {
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
/// extension API this is passed explicitly. As a result there is always an
/// extra `self` argument before the arguments explicitly passed in Ruby, and the
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
/// use magnus::{Error, Ruby, method, prelude::*};
///
/// fn rb_is_blank(rb_self: String) -> bool {
///     rb_self.contains(|c: char| !c.is_whitespace())
/// }
///
/// #[magnus::init]
/// fn init(ruby: &Ruby) -> Result<(), Error> {
///     let class = ruby.define_class("String", ruby.class_object())?;
///     class.define_method("blank?", method!(rb_is_blank, 0))?;
///     Ok(())
/// }
/// # let cleanup = unsafe { magnus::embed::init() };
/// # init(&cleanup).unwrap();
/// ```
#[macro_export]
macro_rules! method {
    ($name:expr_2021, -2) => {{
        unsafe extern "C" fn anon(rb_self: $crate::Value, args: $crate::RArray) -> $crate::Value {
            use $crate::method::{MethodRbAry, RubyMethodRbAry};
            unsafe { $name.call_handle_error(&$crate::Ruby::get_unchecked(), rb_self, args) }
        }
        anon as unsafe extern "C" fn($crate::Value, $crate::RArray) -> $crate::Value
    }};
    ($name:expr_2021, -1) => {{
        unsafe extern "C" fn anon(
            argc: std::ffi::c_int,
            argv: *const $crate::Value,
            rb_self: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{MethodCAry, RubyMethodCAry};
            unsafe { $name.call_handle_error(&$crate::Ruby::get_unchecked(), argc, argv, rb_self) }
        }
        anon as unsafe extern "C" fn(
            std::ffi::c_int,
            *const $crate::Value,
            $crate::Value,
        ) -> $crate::Value
    }};
    ($name:expr_2021, 0) => {{
        unsafe extern "C" fn anon(rb_self: $crate::Value) -> $crate::Value {
            use $crate::method::{Method0, RubyMethod0};
            unsafe { $name.call_handle_error(&$crate::Ruby::get_unchecked(), rb_self) }
        }
        anon as unsafe extern "C" fn($crate::Value) -> $crate::Value
    }};
    ($name:expr_2021, 1) => {{
        unsafe extern "C" fn anon(rb_self: $crate::Value, a: $crate::Value) -> $crate::Value {
            use $crate::method::{Method1, RubyMethod1};
            unsafe { $name.call_handle_error(&$crate::Ruby::get_unchecked(), rb_self, a) }
        }
        anon as unsafe extern "C" fn($crate::Value, $crate::Value) -> $crate::Value
    }};
    ($name:expr_2021, 2) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{Method2, RubyMethod2};
            unsafe { $name.call_handle_error(&$crate::Ruby::get_unchecked(), rb_self, a, b) }
        }
        anon as unsafe extern "C" fn($crate::Value, $crate::Value, $crate::Value) -> $crate::Value
    }};
    ($name:expr_2021, 3) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
            c: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{Method3, RubyMethod3};
            unsafe { $name.call_handle_error(&$crate::Ruby::get_unchecked(), rb_self, a, b, c) }
        }
        anon as unsafe extern "C" fn(
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
        ) -> $crate::Value
    }};
    ($name:expr_2021, 4) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
            c: $crate::Value,
            d: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{Method4, RubyMethod4};
            unsafe { $name.call_handle_error(&$crate::Ruby::get_unchecked(), rb_self, a, b, c, d) }
        }
        anon as unsafe extern "C" fn(
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
        ) -> $crate::Value
    }};
    ($name:expr_2021, 5) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
            c: $crate::Value,
            d: $crate::Value,
            e: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{Method5, RubyMethod5};
            unsafe {
                $name.call_handle_error(&$crate::Ruby::get_unchecked(), rb_self, a, b, c, d, e)
            }
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
    ($name:expr_2021, 6) => {{
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
            unsafe {
                $name.call_handle_error(&$crate::Ruby::get_unchecked(), rb_self, a, b, c, d, e, f)
            }
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
    ($name:expr_2021, 7) => {{
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
            unsafe {
                $name.call_handle_error(
                    &$crate::Ruby::get_unchecked(),
                    rb_self,
                    a,
                    b,
                    c,
                    d,
                    e,
                    f,
                    g,
                )
            }
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
    ($name:expr_2021, 8) => {{
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
            unsafe {
                $name.call_handle_error(
                    &$crate::Ruby::get_unchecked(),
                    rb_self,
                    a,
                    b,
                    c,
                    d,
                    e,
                    f,
                    g,
                    h,
                )
            }
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
    ($name:expr_2021, 9) => {{
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
            unsafe {
                $name.call_handle_error(
                    &$crate::Ruby::get_unchecked(),
                    rb_self,
                    a,
                    b,
                    c,
                    d,
                    e,
                    f,
                    g,
                    h,
                    i,
                )
            }
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
    ($name:expr_2021, 10) => {{
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
            unsafe {
                $name.call_handle_error(
                    &$crate::Ruby::get_unchecked(),
                    rb_self,
                    a,
                    b,
                    c,
                    d,
                    e,
                    f,
                    g,
                    h,
                    i,
                    j,
                )
            }
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
    ($name:expr_2021, 11) => {{
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
            unsafe {
                $name.call_handle_error(
                    &$crate::Ruby::get_unchecked(),
                    rb_self,
                    a,
                    b,
                    c,
                    d,
                    e,
                    f,
                    g,
                    h,
                    i,
                    j,
                    k,
                )
            }
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
    ($name:expr_2021, 12) => {{
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
            unsafe {
                $name.call_handle_error(
                    &$crate::Ruby::get_unchecked(),
                    rb_self,
                    a,
                    b,
                    c,
                    d,
                    e,
                    f,
                    g,
                    h,
                    i,
                    j,
                    k,
                    l,
                )
            }
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
    ($name:expr_2021, 13) => {{
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
            unsafe {
                $name.call_handle_error(
                    &$crate::Ruby::get_unchecked(),
                    rb_self,
                    a,
                    b,
                    c,
                    d,
                    e,
                    f,
                    g,
                    h,
                    i,
                    j,
                    k,
                    l,
                    m,
                )
            }
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
    ($name:expr_2021, 14) => {{
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
            unsafe {
                $name.call_handle_error(
                    &$crate::Ruby::get_unchecked(),
                    rb_self,
                    a,
                    b,
                    c,
                    d,
                    e,
                    f,
                    g,
                    h,
                    i,
                    j,
                    k,
                    l,
                    m,
                    n,
                )
            }
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
    ($name:expr_2021, 15) => {{
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
            unsafe {
                $name.call_handle_error(
                    &$crate::Ruby::get_unchecked(),
                    rb_self,
                    a,
                    b,
                    c,
                    d,
                    e,
                    f,
                    g,
                    h,
                    i,
                    j,
                    k,
                    l,
                    m,
                    n,
                    o,
                )
            }
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
    ($name:expr_2021, $arity:expr_2021) => {
        compile_error!("arity must be an integer literal between -2..=15")
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
    fn call_convert_value(self, ruby: &Ruby, args: RArray) -> Result<Value, Error> {
        (self)(TryConvert::try_convert(args.as_value())?).into_return_value_with(ruby)
    }

    #[inline]
    unsafe fn call_handle_error(self, ruby: &Ruby, args: RArray) -> Value {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
            self.call_convert_value(ruby, args)
        })) {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(ruby, e)),
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
    fn call_convert_value(self, ruby: &Ruby, args: RArray) -> Result<Value, Error> {
        (self)(ruby, TryConvert::try_convert(args.as_value())?).into_return_value_with(ruby)
    }

    #[inline]
    unsafe fn call_handle_error(self, ruby: &Ruby, args: RArray) -> Value {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
            self.call_convert_value(ruby, args)
        })) {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(ruby, e)),
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
    unsafe fn call_convert_value(
        self,
        ruby: &Ruby,
        argc: c_int,
        argv: *const Value,
    ) -> Result<Value, Error> {
        unsafe {
            let args = slice::from_raw_parts(argv, argc as usize);
            (self)(args).into_return_value_with(ruby)
        }
    }

    #[inline]
    unsafe fn call_handle_error(self, ruby: &Ruby, argc: c_int, argv: *const Value) -> Value {
        unsafe {
            let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
                self.call_convert_value(ruby, argc, argv)
            })) {
                Ok(v) => v,
                Err(e) => Err(Error::from_panic(ruby, e)),
            };
            match res {
                Ok(v) => v,
                Err(e) => raise(e),
            }
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
    unsafe fn call_convert_value(
        self,
        ruby: &Ruby,
        argc: c_int,
        argv: *const Value,
    ) -> Result<Value, Error> {
        unsafe {
            let args = slice::from_raw_parts(argv, argc as usize);
            (self)(ruby, args).into_return_value_with(ruby)
        }
    }

    #[inline]
    unsafe fn call_handle_error(self, ruby: &Ruby, argc: c_int, argv: *const Value) -> Value {
        unsafe {
            let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
                self.call_convert_value(ruby, argc, argv)
            })) {
                Ok(v) => v,
                Err(e) => Err(Error::from_panic(ruby, e)),
            };
            match res {
                Ok(v) => v,
                Err(e) => raise(e),
            }
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
                fn call_convert_value(self, ruby: &Ruby, #(arg~N: Value,)*) -> Result<Value, Error> {
                    (self)(
                        #(TryConvert::try_convert(arg~N)?,)*
                    ).into_return_value_with(ruby)
                }

                #[inline]
                unsafe fn call_handle_error(self, ruby: &Ruby, #(arg~N: Value,)*) -> Value {
                    let res =
                        match std::panic::catch_unwind(AssertUnwindSafe(|| {
                            self.call_convert_value(ruby, #(arg~N,)*)
                        })) {
                            Ok(v) => v,
                            Err(e) => Err(Error::from_panic(ruby, e)),
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
                fn call_convert_value(self, ruby: &Ruby, #(arg~N: Value,)*) -> Result<Value, Error> {
                    (self)(
                        ruby,
                        #(TryConvert::try_convert(arg~N)?,)*
                    ).into_return_value_with(ruby)
                }

                #[inline]
                unsafe fn call_handle_error(self, ruby: &Ruby, #(arg~N: Value,)*) -> Value {
                    let res =
                        match std::panic::catch_unwind(AssertUnwindSafe(|| {
                            self.call_convert_value(ruby, #(arg~N,)*)
                        })) {
                            Ok(v) => v,
                            Err(e) => Err(Error::from_panic(ruby, e)),
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

seq!(N in 0..=15 {
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
/// extension API this is passed explicitly. The wrapper this macro generates
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
/// fn init(ruby: &magnus::Ruby) {
///     ruby.define_global_function("distance", magnus::function!(distance, 2));
/// }
/// # let cleanup = unsafe { magnus::embed::init() };
/// # init(&cleanup);
/// ```
#[macro_export]
macro_rules! function {
    ($name:expr_2021, -2) => {{
        unsafe extern "C" fn anon(rb_self: $crate::Value, args: $crate::RArray) -> $crate::Value {
            use $crate::method::{FunctionRbAry, RubyFunctionRbAry};
            unsafe { $name.call_handle_error(&$crate::Ruby::get_unchecked(), args) }
        }
        anon as unsafe extern "C" fn($crate::Value, $crate::RArray) -> $crate::Value
    }};
    ($name:expr_2021, -1) => {{
        unsafe extern "C" fn anon(
            argc: std::ffi::c_int,
            argv: *const $crate::Value,
            rb_self: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{FunctionCAry, RubyFunctionCAry};
            unsafe { $name.call_handle_error(&$crate::Ruby::get_unchecked(), argc, argv) }
        }
        anon as unsafe extern "C" fn(
            std::ffi::c_int,
            *const $crate::Value,
            $crate::Value,
        ) -> $crate::Value
    }};
    ($name:expr_2021, 0) => {{
        unsafe extern "C" fn anon(rb_self: $crate::Value) -> $crate::Value {
            use $crate::method::{Function0, RubyFunction0};
            unsafe { $name.call_handle_error(&$crate::Ruby::get_unchecked()) }
        }
        anon as unsafe extern "C" fn($crate::Value) -> $crate::Value
    }};
    ($name:expr_2021, 1) => {{
        unsafe extern "C" fn anon(rb_self: $crate::Value, a: $crate::Value) -> $crate::Value {
            use $crate::method::{Function1, RubyFunction1};
            unsafe { $name.call_handle_error(&$crate::Ruby::get_unchecked(), a) }
        }
        anon as unsafe extern "C" fn($crate::Value, $crate::Value) -> $crate::Value
    }};
    ($name:expr_2021, 2) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{Function2, RubyFunction2};
            unsafe { $name.call_handle_error(&$crate::Ruby::get_unchecked(), a, b) }
        }
        anon as unsafe extern "C" fn($crate::Value, $crate::Value, $crate::Value) -> $crate::Value
    }};
    ($name:expr_2021, 3) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
            c: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{Function3, RubyFunction3};
            unsafe { $name.call_handle_error(&$crate::Ruby::get_unchecked(), a, b, c) }
        }
        anon as unsafe extern "C" fn(
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
        ) -> $crate::Value
    }};
    ($name:expr_2021, 4) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
            c: $crate::Value,
            d: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{Function4, RubyFunction4};
            unsafe { $name.call_handle_error(&$crate::Ruby::get_unchecked(), a, b, c, d) }
        }
        anon as unsafe extern "C" fn(
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
            $crate::Value,
        ) -> $crate::Value
    }};
    ($name:expr_2021, 5) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
            c: $crate::Value,
            d: $crate::Value,
            e: $crate::Value,
        ) -> $crate::Value {
            use $crate::method::{Function5, RubyFunction5};
            unsafe { $name.call_handle_error(&$crate::Ruby::get_unchecked(), a, b, c, d, e) }
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
    ($name:expr_2021, 6) => {{
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
            unsafe { $name.call_handle_error(&$crate::Ruby::get_unchecked(), a, b, c, d, e, f) }
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
    ($name:expr_2021, 7) => {{
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
            unsafe { $name.call_handle_error(&$crate::Ruby::get_unchecked(), a, b, c, d, e, f, g) }
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
    ($name:expr_2021, 8) => {{
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
            unsafe {
                $name.call_handle_error(&$crate::Ruby::get_unchecked(), a, b, c, d, e, f, g, h)
            }
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
    ($name:expr_2021, 9) => {{
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
            unsafe {
                $name.call_handle_error(&$crate::Ruby::get_unchecked(), a, b, c, d, e, f, g, h, i)
            }
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
    ($name:expr_2021, 10) => {{
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
            unsafe {
                $name.call_handle_error(
                    &$crate::Ruby::get_unchecked(),
                    a,
                    b,
                    c,
                    d,
                    e,
                    f,
                    g,
                    h,
                    i,
                    j,
                )
            }
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
    ($name:expr_2021, 11) => {{
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
            unsafe {
                $name.call_handle_error(
                    &$crate::Ruby::get_unchecked(),
                    a,
                    b,
                    c,
                    d,
                    e,
                    f,
                    g,
                    h,
                    i,
                    j,
                    k,
                )
            }
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
    ($name:expr_2021, 12) => {{
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
            unsafe {
                $name.call_handle_error(
                    &$crate::Ruby::get_unchecked(),
                    a,
                    b,
                    c,
                    d,
                    e,
                    f,
                    g,
                    h,
                    i,
                    j,
                    k,
                    l,
                )
            }
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
    ($name:expr_2021, 13) => {{
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
            unsafe {
                $name.call_handle_error(
                    &$crate::Ruby::get_unchecked(),
                    a,
                    b,
                    c,
                    d,
                    e,
                    f,
                    g,
                    h,
                    i,
                    j,
                    k,
                    l,
                    m,
                )
            }
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
    ($name:expr_2021, 14) => {{
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
            unsafe {
                $name.call_handle_error(
                    &$crate::Ruby::get_unchecked(),
                    a,
                    b,
                    c,
                    d,
                    e,
                    f,
                    g,
                    h,
                    i,
                    j,
                    k,
                    l,
                    m,
                    n,
                )
            }
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
    ($name:expr_2021, 15) => {{
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
            unsafe {
                $name.call_handle_error(
                    &$crate::Ruby::get_unchecked(),
                    a,
                    b,
                    c,
                    d,
                    e,
                    f,
                    g,
                    h,
                    i,
                    j,
                    k,
                    l,
                    m,
                    n,
                    o,
                )
            }
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
    ($name:expr_2021, $arity:expr_2021) => {
        compile_error!("arity must be an integer literal between -2..=15")
    };
}
