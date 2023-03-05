//! Types and Traits for exposing Rust functions as Ruby methods.

#![allow(clippy::too_many_arguments)]
#![allow(clippy::many_single_char_names)]
#![allow(clippy::missing_safety_doc)]

use std::{ffi::c_void, marker::PhantomData, os::raw::c_int, panic::AssertUnwindSafe, slice};

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

/// Helper type for wrapping a function with type conversions and error
/// handling, as an 'init' function.
///
/// See the [`init`](magnus_macros::init) macro.
#[doc(hidden)]
pub struct Init<Func, Res> {
    func: Func,
    res: PhantomData<Res>,
}

#[allow(missing_docs)]
impl<Func, Res> Init<Func, Res>
where
    Func: Fn() -> Res,
    Res: InitReturn,
{
    #[inline]
    pub fn new(func: Func) -> Self {
        Self {
            func,
            res: Default::default(),
        }
    }

    #[inline]
    pub unsafe fn call_handle_error(self) {
        let res =
            match std::panic::catch_unwind(AssertUnwindSafe(|| (self.func)().into_init_return())) {
                Ok(v) => v,
                Err(e) => Err(Error::from_panic(e)),
            };
        match res {
            Ok(v) => v,
            Err(e) => raise(e),
        }
    }
}

/// Helper type for wrapping a function with type conversions and error
/// handling, as an 'init' function being passed [`&Ruby`](Ruby).
///
/// See the [`init`](magnus_macros::init) macro.
#[doc(hidden)]
pub struct InitRuby<Func, Res> {
    func: Func,
    res: PhantomData<Res>,
}

#[allow(missing_docs)]
impl<Func, Res> InitRuby<Func, Res>
where
    Func: Fn(&Ruby) -> Res,
    Res: InitReturn,
{
    #[inline]
    pub fn new(func: Func) -> Self {
        Self {
            func,
            res: Default::default(),
        }
    }

    #[inline]
    pub unsafe fn call_handle_error(self) {
        let ruby = Ruby::get_unchecked();
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
            (self.func)(&ruby).into_init_return()
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

/// Helper type for wrapping a function with type conversions and error
/// handling, as an 'block' function.
///
/// See the [`Value::block_call`] function.
#[doc(hidden)]
pub struct Block<Func, Res> {
    func: Func,
    res: PhantomData<Res>,
}

#[allow(missing_docs)]
impl<Func, Res> Block<Func, Res>
where
    Func: FnMut(&[Value], Option<Proc>) -> Res,
    Res: BlockReturn,
{
    #[inline]
    pub fn new(func: Func) -> Self {
        Self {
            func,
            res: Default::default(),
        }
    }

    #[inline]
    pub unsafe fn call_handle_error(
        self,
        argc: c_int,
        argv: *const Value,
        blockarg: Value,
    ) -> Value {
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

    #[inline]
    unsafe fn call_convert_value(
        mut self,
        argc: c_int,
        argv: *const Value,
        blockarg: Value,
    ) -> Result<Value, Error> {
        let args = slice::from_raw_parts(argv, argc as usize);
        (self.func)(args, Proc::from_value(blockarg)).into_block_return()
    }
}

/// Helper type for wrapping a function as a Ruby method taking self and a Ruby
/// array of arguments, with type conversions and error handling.
///
/// See the [`method`](crate::method!) macro.
#[doc(hidden)]
pub struct MethodRbAry<Func, RbSelf, Args, Res> {
    func: Func,
    rb_self: PhantomData<RbSelf>,
    args: PhantomData<Args>,
    res: PhantomData<Res>,
}

#[allow(missing_docs)]
impl<Func, RbSelf, Args, Res> MethodRbAry<Func, RbSelf, Args, Res>
where
    Func: Fn(RbSelf, Args) -> Res,
    RbSelf: TryConvert,
    Args: TryConvert,
    Res: ReturnValue,
{
    #[inline]
    pub fn new(func: Func) -> Self {
        Self {
            func,
            rb_self: Default::default(),
            args: Default::default(),
            res: Default::default(),
        }
    }

    #[inline]
    unsafe fn call_convert_value(self, rb_self: Value, args: RArray) -> Result<Value, Error> {
        (self.func)(
            TryConvert::try_convert(rb_self)?,
            TryConvert::try_convert(args.as_value())?,
        )
        .into_return_value()
    }

    #[inline]
    pub unsafe fn call_handle_error(self, rb_self: Value, args: RArray) -> Value {
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

/// Helper type for wrapping a function as a Ruby method taking self and a
/// slice of arguments, with type conversions and error handling.
///
/// See the [`method`](crate::method!) macro.
#[doc(hidden)]
pub struct MethodCAry<Func, RbSelf, Res> {
    func: Func,
    rb_self: PhantomData<RbSelf>,
    res: PhantomData<Res>,
}

#[allow(missing_docs)]
impl<Func, RbSelf, Res> MethodCAry<Func, RbSelf, Res>
where
    Func: Fn(RbSelf, &[Value]) -> Res,
    RbSelf: TryConvert,
    Res: ReturnValue,
{
    #[inline]
    pub fn new(func: Func) -> Self {
        Self {
            func,
            rb_self: Default::default(),
            res: Default::default(),
        }
    }

    #[inline]
    unsafe fn call_convert_value(
        self,
        argc: c_int,
        argv: *const Value,
        rb_self: Value,
    ) -> Result<Value, Error> {
        let args = slice::from_raw_parts(argv, argc as usize);
        (self.func)(TryConvert::try_convert(rb_self)?, args).into_return_value()
    }

    #[inline]
    pub unsafe fn call_handle_error(
        self,
        argc: c_int,
        argv: *const Value,
        rb_self: Value,
    ) -> Value {
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

macro_rules! method_n {
    ($name:ident, $n:literal) => {
        seq!(N in 0..$n {
            /// Helper type for wrapping a function as a Ruby method taking
            /// self and N arguments, with type conversions and error handling.
            ///
            /// See the [`method`](crate::method!) macro.
            #[doc(hidden)]
            pub struct $name<Func, RbSelf, #(T~N,)* Res> {
                func: Func,
                rb_self: PhantomData<RbSelf>,
                #(f~N: PhantomData<T~N>,)*
                res: PhantomData<Res>,
            }

            #[allow(missing_docs)]
            impl<Func, RbSelf, #(T~N,)* Res> $name<Func, RbSelf, #(T~N,)* Res>
            where
                Func: Fn(RbSelf, #(T~N,)*) -> Res,
                RbSelf: TryConvert,
                #(T~N: TryConvert,)*
                Res: ReturnValue,
            {
                #[inline]
                pub fn new(func: Func) -> Self {
                    Self {
                        func,
                        rb_self: Default::default(),
                        #(f~N: Default::default(),)*
                        res: Default::default(),
                    }
                }

                #[inline]
                unsafe fn call_convert_value(self, rb_self: Value, #(arg~N: Value,)*) -> Result<Value, Error> {
                    (self.func)(
                        TryConvert::try_convert(rb_self)?,
                        #(TryConvert::try_convert(arg~N)?,)*

                    ).into_return_value()
                }

                #[inline]
                pub unsafe fn call_handle_error(self, rb_self: Value, #(arg~N: Value,)*) -> Value {
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
        });
    }
}

seq!(N in 0..=16 {
    method_n!(Method~N, N);
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
/// ```

#[macro_export]
macro_rules! method {
    ($name:expr, -2) => {{
        unsafe extern "C" fn anon(rb_self: $crate::Value, args: $crate::RArray) -> $crate::Value {
            $crate::method::MethodRbAry::new($name).call_handle_error(rb_self, args)
        }
        anon as unsafe extern "C" fn($crate::Value, $crate::RArray) -> $crate::Value
    }};
    ($name:expr, -1) => {{
        unsafe extern "C" fn anon(
            argc: std::os::raw::c_int,
            argv: *const $crate::Value,
            rb_self: $crate::Value,
        ) -> $crate::Value {
            $crate::method::MethodCAry::new($name).call_handle_error(argc, argv, rb_self)
        }
        anon as unsafe extern "C" fn(
            std::os::raw::c_int,
            *const $crate::Value,
            $crate::Value,
        ) -> $crate::Value
    }};
    ($name:expr, 0) => {{
        unsafe extern "C" fn anon(rb_self: $crate::Value) -> $crate::Value {
            $crate::method::Method0::new($name).call_handle_error(rb_self)
        }
        anon as unsafe extern "C" fn($crate::Value) -> $crate::Value
    }};
    ($name:expr, 1) => {{
        unsafe extern "C" fn anon(rb_self: $crate::Value, a: $crate::Value) -> $crate::Value {
            $crate::method::Method1::new($name).call_handle_error(rb_self, a)
        }
        anon as unsafe extern "C" fn($crate::Value, $crate::Value) -> $crate::Value
    }};
    ($name:expr, 2) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
        ) -> $crate::Value {
            $crate::method::Method2::new($name).call_handle_error(rb_self, a, b)
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
            $crate::method::Method3::new($name).call_handle_error(rb_self, a, b, c)
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
            $crate::method::Method4::new($name).call_handle_error(rb_self, a, b, c, d)
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
            $crate::method::Method5::new($name).call_handle_error(rb_self, a, b, c, d, e)
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
            $crate::method::Method6::new($name).call_handle_error(rb_self, a, b, c, d, e, f)
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
            $crate::method::Method7::new($name).call_handle_error(rb_self, a, b, c, d, e, f, g)
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
            $crate::method::Method8::new($name).call_handle_error(rb_self, a, b, c, d, e, f, g, h)
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
            $crate::method::Method9::new($name)
                .call_handle_error(rb_self, a, b, c, d, e, f, g, h, i)
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
            $crate::method::Method10::new($name)
                .call_handle_error(rb_self, a, b, c, d, e, f, g, h, i, j)
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
            $crate::method::Method11::new($name)
                .call_handle_error(rb_self, a, b, c, d, e, f, g, h, i, j, k)
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
            $crate::method::Method12::new($name)
                .call_handle_error(rb_self, a, b, c, d, e, f, g, h, i, j, k, l)
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
            $crate::method::Method13::new($name)
                .call_handle_error(rb_self, a, b, c, d, e, f, g, h, i, j, k, l, m)
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
            $crate::method::Method14::new($name)
                .call_handle_error(rb_self, a, b, c, d, e, f, g, h, i, j, k, l, m, n)
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
            $crate::method::Method15::new($name)
                .call_handle_error(rb_self, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o)
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
            $crate::method::Method16::new($name)
                .call_handle_error(rb_self, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p)
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

/// Helper type for wrapping a function as a Ruby method ignoring self and
/// taking a Ruby array of arguments, with type conversions and error handling.
///
/// See the [`function`](crate::function!) macro.
#[doc(hidden)]
pub struct FunctionRbAry<Func, Args, Res> {
    func: Func,
    args: PhantomData<Args>,
    res: PhantomData<Res>,
}

#[allow(missing_docs)]
impl<Func, Args, Res> FunctionRbAry<Func, Args, Res>
where
    Func: Fn(Args) -> Res,
    Args: TryConvert,
    Res: ReturnValue,
{
    #[inline]
    pub fn new(func: Func) -> Self {
        Self {
            func,
            args: Default::default(),
            res: Default::default(),
        }
    }

    #[inline]
    unsafe fn call_convert_value(self, args: RArray) -> Result<Value, Error> {
        (self.func)(TryConvert::try_convert(args.as_value())?).into_return_value()
    }

    #[inline]
    pub unsafe fn call_handle_error(self, args: RArray) -> Value {
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

/// Helper type for wrapping a function as a Ruby method ignoring self and
/// taking a slice of arguments, with type conversions and error handling.
///
/// See the [`function`](crate::function!) macro.
#[doc(hidden)]
pub struct FunctionCAry<Func, Res> {
    func: Func,
    res: PhantomData<Res>,
}

#[allow(missing_docs)]
impl<Func, Res> FunctionCAry<Func, Res>
where
    Func: Fn(&[Value]) -> Res,
    Res: ReturnValue,
{
    #[inline]
    pub fn new(func: Func) -> Self {
        Self {
            func,
            res: Default::default(),
        }
    }

    #[inline]
    unsafe fn call_convert_value(self, argc: c_int, argv: *const Value) -> Result<Value, Error> {
        let args = slice::from_raw_parts(argv, argc as usize);
        (self.func)(args).into_return_value()
    }

    #[inline]
    pub unsafe fn call_handle_error(self, argc: c_int, argv: *const Value) -> Value {
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

macro_rules! function_n {
    ($name:ident, $n:literal) => {
        seq!(N in 0..$n {
            /// Helper type for wrapping a function as a Ruby method ignoring
            /// self and taking N arguments, with type conversions and error
            /// handling.
            ///
            /// See the [`function`](crate::function!) macro.
            #[doc(hidden)]
            pub struct $name<Func, #(T~N,)* Res> {
                func: Func,
                #(f~N: PhantomData<T~N>,)*
                res: PhantomData<Res>,
            }

            #[allow(missing_docs)]
            impl<Func, #(T~N,)* Res> $name<Func, #(T~N,)* Res>
            where
                Func: Fn(#(T~N,)*) -> Res,
                #(T~N: TryConvert,)*
                Res: ReturnValue,
            {
                #[inline]
                pub fn new(func: Func) -> Self {
                    Self {
                        func,
                        #(f~N: Default::default(),)*
                        res: Default::default(),
                    }
                }

                #[inline]
                unsafe fn call_convert_value(self, #(arg~N: Value,)*) -> Result<Value, Error> {
                    (self.func)(
                        #(TryConvert::try_convert(arg~N)?,)*
                    ).into_return_value()
                }

                #[inline]
                pub unsafe fn call_handle_error(self, #(arg~N: Value,)*) -> Value {
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
        });
    }
}

seq!(N in 0..=16 {
    function_n!(Function~N, N);
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
/// See the [`method`](crate::method!) macro for cases where the `self` argument is required.
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
/// ```
#[macro_export]
macro_rules! function {
    ($name:expr, -2) => {{
        unsafe extern "C" fn anon(rb_self: $crate::Value, args: $crate::RArray) -> $crate::Value {
            $crate::method::FunctionRbAry::new($name).call_handle_error(args)
        }
        anon as unsafe extern "C" fn($crate::Value, $crate::RArray) -> $crate::Value
    }};
    ($name:expr, -1) => {{
        unsafe extern "C" fn anon(
            argc: std::os::raw::c_int,
            argv: *const $crate::Value,
            rb_self: $crate::Value,
        ) -> $crate::Value {
            $crate::method::FunctionCAry::new($name).call_handle_error(argc, argv)
        }
        anon as unsafe extern "C" fn(
            std::os::raw::c_int,
            *const $crate::Value,
            $crate::Value,
        ) -> $crate::Value
    }};
    ($name:expr, 0) => {{
        unsafe extern "C" fn anon(rb_self: $crate::Value) -> $crate::Value {
            $crate::method::Function0::new($name).call_handle_error()
        }
        anon as unsafe extern "C" fn($crate::Value) -> $crate::Value
    }};
    ($name:expr, 1) => {{
        unsafe extern "C" fn anon(rb_self: $crate::Value, a: $crate::Value) -> $crate::Value {
            $crate::method::Function1::new($name).call_handle_error(a)
        }
        anon as unsafe extern "C" fn($crate::Value, $crate::Value) -> $crate::Value
    }};
    ($name:expr, 2) => {{
        unsafe extern "C" fn anon(
            rb_self: $crate::Value,
            a: $crate::Value,
            b: $crate::Value,
        ) -> $crate::Value {
            $crate::method::Function2::new($name).call_handle_error(a, b)
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
            $crate::method::Function3::new($name).call_handle_error(a, b, c)
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
            $crate::method::Function4::new($name).call_handle_error(a, b, c, d)
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
            $crate::method::Function5::new($name).call_handle_error(a, b, c, d, e)
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
            $crate::method::Function6::new($name).call_handle_error(a, b, c, d, e, f)
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
            $crate::method::Function7::new($name).call_handle_error(a, b, c, d, e, f, g)
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
            $crate::method::Function8::new($name).call_handle_error(a, b, c, d, e, f, g, h)
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
            $crate::method::Function9::new($name).call_handle_error(a, b, c, d, e, f, g, h, i)
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
            $crate::method::Function10::new($name).call_handle_error(a, b, c, d, e, f, g, h, i, j)
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
            $crate::method::Function11::new($name)
                .call_handle_error(a, b, c, d, e, f, g, h, i, j, k)
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
            $crate::method::Function12::new($name)
                .call_handle_error(a, b, c, d, e, f, g, h, i, j, k, l)
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
            $crate::method::Function13::new($name)
                .call_handle_error(a, b, c, d, e, f, g, h, i, j, k, l, m)
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
            $crate::method::Function14::new($name)
                .call_handle_error(a, b, c, d, e, f, g, h, i, j, k, l, m, n)
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
            $crate::method::Function15::new($name)
                .call_handle_error(a, b, c, d, e, f, g, h, i, j, k, l, m, n, o)
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
            $crate::method::Function16::new($name)
                .call_handle_error(a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p)
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
