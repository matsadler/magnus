//! Types and functions for complex method arguments.
//!
//! Ruby's APIs to define methods, exposed in magnus through functions such as
//! [`define_method`](crate::module::Module::define_method) and the
//! [`method`](crate::method!) macro, allow defining methods with a fixed
//! number of positional arguments, or an unbounded collection of arguments as
//! a slice or Ruby array. The functions in this module allow for more complex
//! agument handling.
//!
//! Ruby arguments can be classified as follows:
//! ``` text
//! def example(a, b, c=nil, d=nil, *rest, e, f, g:, h:, i: nil, j: nil, **kwargs, &block)
//!             \__/  \__________/  \___/  \__/  \____/  \____________/  \______/  \____/
//!               |        |          |      |     |            |           |        |
//!            required    |        splat    |  keywords     keywords    keywords  block
//!                     optional             | (required)   (optional)   (splat)
//!                                          |
//!                                       trailing
//!                                       required
//! ```
//!
//! The [`scan_args`] function can be used with a method defined as
//! `method!(name, -1)` (i.e. receiving a slice of arguments) to implement this
//! more complex functionality.
//!
//! The [`get_kwargs`] function is used to extract keywords from a Ruby `Hash`
//! of keywords and implement the behaviour around required and optional
//! keyword arguments.

use std::{
    ffi::CString,
    fmt,
    mem::transmute,
    ops::{Bound, RangeBounds},
    os::raw::c_int,
};

use rb_sys::{rb_error_arity, rb_get_kwargs, rb_scan_args, ID, VALUE};

use crate::{
    block::Proc,
    error::{protect, Error},
    exception,
    r_array::RArray,
    r_hash::RHash,
    ruby_handle::RubyHandle,
    try_convert::{TryConvert, TryConvertOwned},
    value::{Id, IntoId, Value, QNIL},
};

struct ArgSpec {
    required: usize,
    optional: usize,
    splat: bool,
    trailing: usize,
    keywords: bool,
    block: bool,
}

impl ArgSpec {
    fn new(
        required: usize,
        optional: usize,
        splat: bool,
        trailing: usize,
        keywords: bool,
        block: bool,
    ) -> Self {
        if required > 9 {
            panic!("'required' out of bounds, expected 0..=9, got {}", required);
        }
        if optional > 9 {
            panic!("'optional' out of bounds, expected 0..=9, got {}", required);
        }
        if trailing > 9 {
            panic!("'trailing' out of bounds, expected 0..=9, got {}", required);
        }
        Self {
            required,
            optional,
            splat,
            trailing,
            keywords,
            block,
        }
    }

    fn len(&self) -> usize {
        self.required
            + self.optional
            + self.splat as usize
            + self.trailing
            + self.keywords as usize
            + self.block as usize
    }
}

impl fmt::Display for ArgSpec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.required > 0 || self.optional > 0 || self.trailing > 0 {
            write!(f, "{}", self.required)?;
        }
        if self.optional > 0 || (!self.splat && self.trailing > 0) {
            write!(f, "{}", self.optional)?;
        }
        if self.splat {
            write!(f, "*")?;
        }
        if self.trailing > 0 {
            write!(f, "{}", self.trailing)?;
        }
        if self.keywords {
            write!(f, ":")?;
        }
        if self.block {
            write!(f, "&")?;
        }
        Ok(())
    }
}

/// Arguments returned from [`scan_args`].
pub struct Args<Req, Opt, Splat, Trail, Kw, Block> {
    /// Required arguments.
    pub required: Req,
    /// Optional arguments.
    pub optional: Opt,
    /// The splat argument.
    pub splat: Splat,
    /// Trailing required arguments.
    pub trailing: Trail,
    /// Keywords arguments.
    pub keywords: Kw,
    /// This block argument.
    pub block: Block,
}

struct ScannedArgs {
    arg_spec: ArgSpec,
    args: [Value; 30],
    parsed: usize,
}

impl ScannedArgs {
    fn required(&self) -> &[Value] {
        &self.args[0..self.arg_spec.required]
    }

    fn optional(&self) -> &[Value] {
        let start = self.arg_spec.required;
        let end = start
            + self
                .arg_spec
                .optional
                .min(self.parsed - start - self.arg_spec.trailing);
        &self.args[start..end]
    }

    fn splat(&self) -> Option<Value> {
        self.arg_spec
            .splat
            .then(|| self.args[self.arg_spec.required + self.arg_spec.optional])
    }

    fn trailing(&self) -> &[Value] {
        let start = self.arg_spec.required + self.arg_spec.optional + self.arg_spec.splat as usize;
        let end = start + self.arg_spec.trailing;
        &self.args[start..end]
    }

    fn keywords(&self) -> Option<Value> {
        self.arg_spec.keywords.then(|| {
            self.args[self.arg_spec.required
                + self.arg_spec.optional
                + self.arg_spec.splat as usize
                + self.arg_spec.trailing]
        })
    }

    fn block(&self) -> Option<Value> {
        self.arg_spec.block.then(|| {
            self.args[self.arg_spec.required
                + self.arg_spec.optional
                + self.arg_spec.splat as usize
                + self.arg_spec.trailing
                + self.arg_spec.keywords as usize]
        })
    }
}

mod private {
    use super::*;

    pub trait ScanArgsRequired: Sized {
        const LEN: usize;

        fn from_slice(vals: &[Value]) -> Result<Self, Error>;
    }

    impl ScanArgsRequired for () {
        const LEN: usize = 0;

        fn from_slice(vals: &[Value]) -> Result<Self, Error> {
            if vals.len() == <Self as ScanArgsRequired>::LEN {
                Ok(())
            } else {
                panic!(
                    "unexpected arguments, expected {} got {}",
                    <Self as ScanArgsRequired>::LEN,
                    vals.len()
                );
            }
        }
    }

    impl<T0> ScanArgsRequired for (T0,)
    where
        T0: TryConvert,
    {
        const LEN: usize = 1;

        fn from_slice(vals: &[Value]) -> Result<Self, Error> {
            if vals.len() == <Self as ScanArgsRequired>::LEN {
                Ok((vals[0].try_convert()?,))
            } else {
                panic!(
                    "unexpected arguments, expected {} got {}",
                    <Self as ScanArgsRequired>::LEN,
                    vals.len()
                );
            }
        }
    }

    impl<T0, T1> ScanArgsRequired for (T0, T1)
    where
        T0: TryConvert,
        T1: TryConvert,
    {
        const LEN: usize = 2;

        fn from_slice(vals: &[Value]) -> Result<Self, Error> {
            if vals.len() == <Self as ScanArgsRequired>::LEN {
                Ok((vals[0].try_convert()?, vals[1].try_convert()?))
            } else {
                panic!(
                    "unexpected arguments, expected {} got {}",
                    <Self as ScanArgsRequired>::LEN,
                    vals.len()
                );
            }
        }
    }

    impl<T0, T1, T2> ScanArgsRequired for (T0, T1, T2)
    where
        T0: TryConvert,
        T1: TryConvert,
        T2: TryConvert,
    {
        const LEN: usize = 3;

        fn from_slice(vals: &[Value]) -> Result<Self, Error> {
            if vals.len() == <Self as ScanArgsRequired>::LEN {
                Ok((
                    vals[0].try_convert()?,
                    vals[1].try_convert()?,
                    vals[2].try_convert()?,
                ))
            } else {
                panic!(
                    "unexpected arguments, expected {} got {}",
                    <Self as ScanArgsRequired>::LEN,
                    vals.len()
                );
            }
        }
    }

    impl<T0, T1, T2, T3> ScanArgsRequired for (T0, T1, T2, T3)
    where
        T0: TryConvert,
        T1: TryConvert,
        T2: TryConvert,
        T3: TryConvert,
    {
        const LEN: usize = 4;

        fn from_slice(vals: &[Value]) -> Result<Self, Error> {
            if vals.len() == <Self as ScanArgsRequired>::LEN {
                Ok((
                    vals[0].try_convert()?,
                    vals[1].try_convert()?,
                    vals[2].try_convert()?,
                    vals[3].try_convert()?,
                ))
            } else {
                panic!(
                    "unexpected arguments, expected {} got {}",
                    <Self as ScanArgsRequired>::LEN,
                    vals.len()
                );
            }
        }
    }

    impl<T0, T1, T2, T3, T4> ScanArgsRequired for (T0, T1, T2, T3, T4)
    where
        T0: TryConvert,
        T1: TryConvert,
        T2: TryConvert,
        T3: TryConvert,
        T4: TryConvert,
    {
        const LEN: usize = 5;

        fn from_slice(vals: &[Value]) -> Result<Self, Error> {
            if vals.len() == <Self as ScanArgsRequired>::LEN {
                Ok((
                    vals[0].try_convert()?,
                    vals[1].try_convert()?,
                    vals[2].try_convert()?,
                    vals[3].try_convert()?,
                    vals[4].try_convert()?,
                ))
            } else {
                panic!(
                    "unexpected arguments, expected {} got {}",
                    <Self as ScanArgsRequired>::LEN,
                    vals.len()
                );
            }
        }
    }

    impl<T0, T1, T2, T3, T4, T5> ScanArgsRequired for (T0, T1, T2, T3, T4, T5)
    where
        T0: TryConvert,
        T1: TryConvert,
        T2: TryConvert,
        T3: TryConvert,
        T4: TryConvert,
        T5: TryConvert,
    {
        const LEN: usize = 6;

        fn from_slice(vals: &[Value]) -> Result<Self, Error> {
            if vals.len() == <Self as ScanArgsRequired>::LEN {
                Ok((
                    vals[0].try_convert()?,
                    vals[1].try_convert()?,
                    vals[2].try_convert()?,
                    vals[3].try_convert()?,
                    vals[4].try_convert()?,
                    vals[5].try_convert()?,
                ))
            } else {
                panic!(
                    "unexpected arguments, expected {} got {}",
                    <Self as ScanArgsRequired>::LEN,
                    vals.len()
                );
            }
        }
    }

    impl<T0, T1, T2, T3, T4, T5, T6> ScanArgsRequired for (T0, T1, T2, T3, T4, T5, T6)
    where
        T0: TryConvert,
        T1: TryConvert,
        T2: TryConvert,
        T3: TryConvert,
        T4: TryConvert,
        T5: TryConvert,
        T6: TryConvert,
    {
        const LEN: usize = 7;

        fn from_slice(vals: &[Value]) -> Result<Self, Error> {
            if vals.len() == <Self as ScanArgsRequired>::LEN {
                Ok((
                    vals[0].try_convert()?,
                    vals[1].try_convert()?,
                    vals[2].try_convert()?,
                    vals[3].try_convert()?,
                    vals[4].try_convert()?,
                    vals[5].try_convert()?,
                    vals[6].try_convert()?,
                ))
            } else {
                panic!(
                    "unexpected arguments, expected {} got {}",
                    <Self as ScanArgsRequired>::LEN,
                    vals.len()
                );
            }
        }
    }

    impl<T0, T1, T2, T3, T4, T5, T6, T7> ScanArgsRequired for (T0, T1, T2, T3, T4, T5, T6, T7)
    where
        T0: TryConvert,
        T1: TryConvert,
        T2: TryConvert,
        T3: TryConvert,
        T4: TryConvert,
        T5: TryConvert,
        T6: TryConvert,
        T7: TryConvert,
    {
        const LEN: usize = 8;

        fn from_slice(vals: &[Value]) -> Result<Self, Error> {
            if vals.len() == <Self as ScanArgsRequired>::LEN {
                Ok((
                    vals[0].try_convert()?,
                    vals[1].try_convert()?,
                    vals[2].try_convert()?,
                    vals[3].try_convert()?,
                    vals[4].try_convert()?,
                    vals[5].try_convert()?,
                    vals[6].try_convert()?,
                    vals[7].try_convert()?,
                ))
            } else {
                panic!(
                    "unexpected arguments, expected {} got {}",
                    <Self as ScanArgsRequired>::LEN,
                    vals.len()
                );
            }
        }
    }

    impl<T0, T1, T2, T3, T4, T5, T6, T7, T8> ScanArgsRequired for (T0, T1, T2, T3, T4, T5, T6, T7, T8)
    where
        T0: TryConvert,
        T1: TryConvert,
        T2: TryConvert,
        T3: TryConvert,
        T4: TryConvert,
        T5: TryConvert,
        T6: TryConvert,
        T7: TryConvert,
        T8: TryConvert,
    {
        const LEN: usize = 9;

        fn from_slice(vals: &[Value]) -> Result<Self, Error> {
            if vals.len() == <Self as ScanArgsRequired>::LEN {
                Ok((
                    vals[0].try_convert()?,
                    vals[1].try_convert()?,
                    vals[2].try_convert()?,
                    vals[3].try_convert()?,
                    vals[4].try_convert()?,
                    vals[5].try_convert()?,
                    vals[6].try_convert()?,
                    vals[7].try_convert()?,
                    vals[8].try_convert()?,
                ))
            } else {
                panic!(
                    "unexpected arguments, expected {} got {}",
                    <Self as ScanArgsRequired>::LEN,
                    vals.len()
                );
            }
        }
    }

    pub trait ScanArgsOpt: Sized {
        const LEN: usize;

        fn from_slice(vals: &[Value]) -> Result<Self, Error>;
    }

    impl ScanArgsOpt for () {
        const LEN: usize = 0;

        fn from_slice(vals: &[Value]) -> Result<Self, Error> {
            if vals.len() == <Self as ScanArgsOpt>::LEN {
                Ok(())
            } else {
                panic!(
                    "unexpected arguments, expected {} got {}",
                    <Self as ScanArgsOpt>::LEN,
                    vals.len()
                );
            }
        }
    }

    impl<T0> ScanArgsOpt for (Option<T0>,)
    where
        T0: TryConvert,
    {
        const LEN: usize = 1;

        fn from_slice(vals: &[Value]) -> Result<Self, Error> {
            if vals.len() <= <Self as ScanArgsOpt>::LEN {
                Ok((vals
                    .get(0)
                    .filter(|v| !v.is_undef())
                    .map(|v| v.try_convert())
                    .transpose()?,))
            } else {
                panic!(
                    "unexpected arguments, expected {} got {}",
                    <Self as ScanArgsOpt>::LEN,
                    vals.len()
                );
            }
        }
    }

    impl<T0, T1> ScanArgsOpt for (Option<T0>, Option<T1>)
    where
        T0: TryConvert,
        T1: TryConvert,
    {
        const LEN: usize = 2;

        fn from_slice(vals: &[Value]) -> Result<Self, Error> {
            if vals.len() <= <Self as ScanArgsOpt>::LEN {
                Ok((
                    vals.get(0)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                    vals.get(1)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                ))
            } else {
                panic!(
                    "unexpected arguments, expected {} got {}",
                    <Self as ScanArgsOpt>::LEN,
                    vals.len()
                );
            }
        }
    }

    impl<T0, T1, T2> ScanArgsOpt for (Option<T0>, Option<T1>, Option<T2>)
    where
        T0: TryConvert,
        T1: TryConvert,
        T2: TryConvert,
    {
        const LEN: usize = 3;

        fn from_slice(vals: &[Value]) -> Result<Self, Error> {
            if vals.len() <= <Self as ScanArgsOpt>::LEN {
                Ok((
                    vals.get(0)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                    vals.get(1)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                    vals.get(2)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                ))
            } else {
                panic!(
                    "unexpected arguments, expected {} got {}",
                    <Self as ScanArgsOpt>::LEN,
                    vals.len()
                );
            }
        }
    }

    impl<T0, T1, T2, T3> ScanArgsOpt for (Option<T0>, Option<T1>, Option<T2>, Option<T3>)
    where
        T0: TryConvert,
        T1: TryConvert,
        T2: TryConvert,
        T3: TryConvert,
    {
        const LEN: usize = 4;

        fn from_slice(vals: &[Value]) -> Result<Self, Error> {
            if vals.len() <= <Self as ScanArgsOpt>::LEN {
                Ok((
                    vals.get(0)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                    vals.get(1)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                    vals.get(2)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                    vals.get(3)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                ))
            } else {
                panic!(
                    "unexpected arguments, expected {} got {}",
                    <Self as ScanArgsOpt>::LEN,
                    vals.len()
                );
            }
        }
    }

    impl<T0, T1, T2, T3, T4> ScanArgsOpt
        for (Option<T0>, Option<T1>, Option<T2>, Option<T3>, Option<T4>)
    where
        T0: TryConvert,
        T1: TryConvert,
        T2: TryConvert,
        T3: TryConvert,
        T4: TryConvert,
    {
        const LEN: usize = 5;

        fn from_slice(vals: &[Value]) -> Result<Self, Error> {
            if vals.len() <= <Self as ScanArgsOpt>::LEN {
                Ok((
                    vals.get(0)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                    vals.get(1)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                    vals.get(2)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                    vals.get(3)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                    vals.get(4)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                ))
            } else {
                panic!(
                    "unexpected arguments, expected {} got {}",
                    <Self as ScanArgsOpt>::LEN,
                    vals.len()
                );
            }
        }
    }

    impl<T0, T1, T2, T3, T4, T5> ScanArgsOpt
        for (
            Option<T0>,
            Option<T1>,
            Option<T2>,
            Option<T3>,
            Option<T4>,
            Option<T5>,
        )
    where
        T0: TryConvert,
        T1: TryConvert,
        T2: TryConvert,
        T3: TryConvert,
        T4: TryConvert,
        T5: TryConvert,
    {
        const LEN: usize = 6;

        fn from_slice(vals: &[Value]) -> Result<Self, Error> {
            if vals.len() <= <Self as ScanArgsOpt>::LEN {
                Ok((
                    vals.get(0)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                    vals.get(1)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                    vals.get(2)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                    vals.get(3)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                    vals.get(4)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                    vals.get(5)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                ))
            } else {
                panic!(
                    "unexpected arguments, expected {} got {}",
                    <Self as ScanArgsOpt>::LEN,
                    vals.len()
                );
            }
        }
    }

    impl<T0, T1, T2, T3, T4, T5, T6> ScanArgsOpt
        for (
            Option<T0>,
            Option<T1>,
            Option<T2>,
            Option<T3>,
            Option<T4>,
            Option<T5>,
            Option<T6>,
        )
    where
        T0: TryConvert,
        T1: TryConvert,
        T2: TryConvert,
        T3: TryConvert,
        T4: TryConvert,
        T5: TryConvert,
        T6: TryConvert,
    {
        const LEN: usize = 7;

        fn from_slice(vals: &[Value]) -> Result<Self, Error> {
            if vals.len() <= <Self as ScanArgsOpt>::LEN {
                Ok((
                    vals.get(0)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                    vals.get(1)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                    vals.get(2)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                    vals.get(3)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                    vals.get(4)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                    vals.get(5)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                    vals.get(6)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                ))
            } else {
                panic!(
                    "unexpected arguments, expected {} got {}",
                    <Self as ScanArgsOpt>::LEN,
                    vals.len()
                );
            }
        }
    }

    impl<T0, T1, T2, T3, T4, T5, T6, T7> ScanArgsOpt
        for (
            Option<T0>,
            Option<T1>,
            Option<T2>,
            Option<T3>,
            Option<T4>,
            Option<T5>,
            Option<T6>,
            Option<T7>,
        )
    where
        T0: TryConvert,
        T1: TryConvert,
        T2: TryConvert,
        T3: TryConvert,
        T4: TryConvert,
        T5: TryConvert,
        T6: TryConvert,
        T7: TryConvert,
    {
        const LEN: usize = 8;

        fn from_slice(vals: &[Value]) -> Result<Self, Error> {
            if vals.len() <= <Self as ScanArgsOpt>::LEN {
                Ok((
                    vals.get(0)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                    vals.get(1)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                    vals.get(2)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                    vals.get(3)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                    vals.get(4)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                    vals.get(5)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                    vals.get(6)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                    vals.get(7)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                ))
            } else {
                panic!(
                    "unexpected arguments, expected {} got {}",
                    <Self as ScanArgsOpt>::LEN,
                    vals.len()
                );
            }
        }
    }

    impl<T0, T1, T2, T3, T4, T5, T6, T7, T8> ScanArgsOpt
        for (
            Option<T0>,
            Option<T1>,
            Option<T2>,
            Option<T3>,
            Option<T4>,
            Option<T5>,
            Option<T6>,
            Option<T7>,
            Option<T8>,
        )
    where
        T0: TryConvert,
        T1: TryConvert,
        T2: TryConvert,
        T3: TryConvert,
        T4: TryConvert,
        T5: TryConvert,
        T6: TryConvert,
        T7: TryConvert,
        T8: TryConvert,
    {
        const LEN: usize = 9;

        fn from_slice(vals: &[Value]) -> Result<Self, Error> {
            if vals.len() <= <Self as ScanArgsOpt>::LEN {
                Ok((
                    vals.get(0)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                    vals.get(1)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                    vals.get(2)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                    vals.get(3)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                    vals.get(4)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                    vals.get(5)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                    vals.get(6)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                    vals.get(7)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                    vals.get(8)
                        .filter(|v| !v.is_undef())
                        .map(|v| v.try_convert())
                        .transpose()?,
                ))
            } else {
                panic!(
                    "unexpected arguments, expected {} got {}",
                    <Self as ScanArgsOpt>::LEN,
                    vals.len()
                );
            }
        }
    }

    pub trait ScanArgsSplat: Sized {
        const REQ: bool;

        fn from_opt(val: Option<Value>) -> Result<Self, Error>;
    }

    impl ScanArgsSplat for () {
        const REQ: bool = false;

        fn from_opt(val: Option<Value>) -> Result<Self, Error> {
            if let Some(val) = val {
                panic!("unexpected argument {:?}", val);
            };
            Ok(())
        }
    }

    impl ScanArgsSplat for RArray {
        const REQ: bool = true;

        fn from_opt(val: Option<Value>) -> Result<Self, Error> {
            val.expect("expected splat").try_convert()
        }
    }

    impl<T> ScanArgsSplat for Vec<T>
    where
        T: TryConvertOwned,
    {
        const REQ: bool = true;

        fn from_opt(val: Option<Value>) -> Result<Self, Error> {
            val.expect("expected splat").try_convert()
        }
    }

    pub trait ScanArgsKw: Sized {
        const REQ: bool;

        fn from_opt(val: Option<Value>) -> Result<Self, Error>;
    }

    impl ScanArgsKw for () {
        const REQ: bool = false;

        fn from_opt(val: Option<Value>) -> Result<Self, Error> {
            if let Some(val) = val {
                panic!("unexpected argument {:?}", val);
            };
            Ok(())
        }
    }

    impl ScanArgsKw for RHash {
        const REQ: bool = true;

        fn from_opt(val: Option<Value>) -> Result<Self, Error> {
            let val = val.expect("expected keywords");
            if val.is_nil() {
                return Ok(RHash::new());
            }
            val.try_convert()
        }
    }

    pub trait ScanArgsBlock: Sized {
        const REQ: bool;

        fn from_opt(val: Option<Value>) -> Result<Self, Error>;
    }

    impl ScanArgsBlock for () {
        const REQ: bool = false;

        fn from_opt(val: Option<Value>) -> Result<Self, Error> {
            if let Some(val) = val {
                panic!("unexpected argument {:?}", val);
            };
            Ok(())
        }
    }

    impl ScanArgsBlock for Proc {
        const REQ: bool = true;

        fn from_opt(val: Option<Value>) -> Result<Self, Error> {
            let val = val.expect("expected block");
            if val.is_nil() {
                return Err(Error::new(exception::arg_error(), "no block given"));
            }
            val.try_convert()
        }
    }

    impl ScanArgsBlock for Option<Proc> {
        const REQ: bool = true;

        fn from_opt(val: Option<Value>) -> Result<Self, Error> {
            val.expect("expected block").try_convert()
        }
    }
}

/// Trait implemented for types that can be retrieved as required arguments by
/// [`scan_args`].
///
/// This trait is implemented for `(T0,)`, `(T0, T1)`, `(T0, T1, T2)`, etc,
/// through to a length of 9, where `T0`, `T1`, etc implement [`TryConvert`].
///
/// `()` also implements this trait as a placeholder indicating no required
/// arguments are required.
pub trait ScanArgsRequired: private::ScanArgsRequired {}
impl<T> ScanArgsRequired for T where T: private::ScanArgsRequired {}

/// Trait implemented for types that can be retrieved as optional arguments by
/// [`scan_args`].
///
/// This trait is implemented for `(Option<T0>,)`, `(Option<T0>, Option<T1>)`,
/// etc, through to a length of 9, where `T0`, `T1`, etc implement
/// [`TryConvert`].
///
/// `()` also implements this trait as a placeholder indicating no optional
/// arguments are required.
pub trait ScanArgsOpt: private::ScanArgsOpt {}
impl<T> ScanArgsOpt for T where T: private::ScanArgsOpt {}

/// Trait implemented for types that can be retrieved a 'splat' argument by
/// [`scan_args`].
///
/// This trait is implemented for `Vec<T>` where `T` implements [`TryConvert`]
/// and converts to an owned Rust value (not a handle to a Ruby object). It is
/// also implemented for [`RArray`].
///
/// `()` also implements this trait as a placeholder indicating no splat
/// argument is required.
pub trait ScanArgsSplat: private::ScanArgsSplat {}
impl<T> ScanArgsSplat for T where T: private::ScanArgsSplat {}

/// Trait implemented for types that can be retrieved as keyword arguments by
/// [`scan_args`].
///
/// This trait is implemented for [`RHash`].
///
/// `()` also implements this trait as a placeholder indicating no keyword
/// arguments are required.
pub trait ScanArgsKw: private::ScanArgsKw {}
impl<T> ScanArgsKw for T where T: private::ScanArgsKw {}

/// Trait implemented for types that can be retrieved as a block argument by
/// [`scan_args`].
///
/// This trait is implemented for [`Proc`] and `Option<Proc>`.
///
/// `()` also implements this trait as a placeholder for when no block argument
/// is required, although Ruby will still allow a block to be passed, it will
/// just ignore it (as is standard for all Ruby methods).
pub trait ScanArgsBlock: private::ScanArgsBlock {}
impl<T> ScanArgsBlock for T where T: private::ScanArgsBlock {}

/// Retrieves arguments from a slice.
///
/// This function can be used to implement Ruby methods with more complex
/// signatures, including optional arguments and 'splats'.
///
/// The format of the arguments required is driven by the types in the return
/// value. The stuct [`Args`] is returned but the types of its fields are
/// determined by type parameters. The type `()` is used as a placeholder when
/// a set of arguments is not required.
///
/// # Examples
///
/// `TCPServer::new`'s argument handling. This is roughly equivalent to
/// `def new(hostname=nil, port)`.
/// ```
/// use magnus::{prelude::*, define_class, error::Error, function, scan_args::scan_args, Value};
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// fn tcp_svr_init(args: &[Value]) -> Result<Value, Error> {
///     let args = scan_args(args)?;
///     let _: () = args.required;
///     let (hostname,): (Option<String>,) = args.optional;
///     let _: () = args.splat;
///     let (port,): (u16,) = args.trailing;
///     let _: () = args.keywords;
///     let _: () = args.block;
///
///     // ...
/// #   let res = magnus::RArray::with_capacity(2);
/// #   res.push(hostname)?;
/// #   res.push(port)?;
/// #   Ok(res.into())
/// }
///
/// let class = define_class("TCPServer", Default::default()).unwrap();
/// class.define_singleton_method("new", function!(tcp_svr_init, -1)).unwrap();
/// # let res = magnus::eval::<bool>(r#"TCPServer.new("foo", 1) == ["foo", 1]"#).unwrap();
/// # assert!(res);
/// # let res = magnus::eval::<bool>(r#"TCPServer.new(2) == [nil, 2]"#).unwrap();
/// # assert!(res);
/// ```
///
/// The same example as above, specifying the types slightly differently.
/// ```
/// use magnus::{prelude::*, define_class, error::Error, function, scan_args::scan_args, Value};
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// fn tcp_svr_init(args: &[Value]) -> Result<Value, Error> {
///     let args = scan_args::<(), (Option<String>,), (), (u16,), (), ()>(args)?;
///     let (hostname,) = args.optional;
///     let (port,) = args.trailing;
///
///     // ...
/// #   let res = magnus::RArray::with_capacity(2);
/// #   res.push(hostname)?;
/// #   res.push(port)?;
/// #   Ok(res.into())
/// }
///
/// let class = define_class("TCPServer", Default::default()).unwrap();
/// class.define_singleton_method("new", function!(tcp_svr_init, -1)).unwrap();
/// # let res = magnus::eval::<bool>(r#"TCPServer.new("foo", 1) == ["foo", 1]"#).unwrap();
/// # assert!(res);
/// # let res = magnus::eval::<bool>(r#"TCPServer.new(2) == [nil, 2]"#).unwrap();
/// # assert!(res);
/// ```
///
/// `Addrinfo::getaddrinfo`'s argument handling. This is roughly equivalent to
/// `def getaddrinfo(nodename, service, family=nil, socktype=nil, protocol=nil, flags=nil, timeout: nil)`.
/// ```
/// use magnus::{
///     prelude::*, define_class, error::Error, function, scan_args::{scan_args, get_kwargs}, RHash, Symbol, Value,
/// };
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// fn getaddrinfo(args: &[Value]) -> Result<Value, Error> {
///     let args = scan_args::<_, _, (), (), _, ()>(args)?;
///     let (nodename, service): (String, u16) = args.required;
///     let (family, socktype, protocol, flags): (
///         Option<Symbol>,
///         Option<Symbol>,
///         Option<i64>,
///         Option<i64>,
///     ) = args.optional;
///     let kw = get_kwargs::<_, (), (Option<usize>,), ()>(args.keywords, &[], &["timeout"])?;
///     let (timeout,) = kw.optional;
///
///     // ...
/// #   let res = magnus::RArray::with_capacity(7);
/// #   res.push(nodename)?;
/// #   res.push(service)?;
/// #   res.push(family)?;
/// #   res.push(socktype)?;
/// #   res.push(protocol)?;
/// #   res.push(flags)?;
/// #   res.push(timeout)?;
/// #   Ok(res.into())
/// }
///
/// let class = define_class("Addrinfo", Default::default()).unwrap();
/// class.define_singleton_method("getaddrinfo", function!(getaddrinfo, -1)).unwrap();
/// # let res = magnus::eval::<bool>(r#"Addrinfo.getaddrinfo("a", 1) == ["a", 1, nil, nil, nil, nil, nil]"#).unwrap();
/// # assert!(res);
/// # let res = magnus::eval::<bool>(r#"Addrinfo.getaddrinfo("a", 1, :b, :c, 3, 4, timeout: 5) == ["a", 1, :b, :c, 3, 4, 5]"#).unwrap();
/// # assert!(res);
/// ```
pub fn scan_args<Req, Opt, Splat, Trail, Kw, Block>(
    args: &[Value],
) -> Result<Args<Req, Opt, Splat, Trail, Kw, Block>, Error>
where
    Req: ScanArgsRequired,
    Opt: ScanArgsOpt,
    Splat: ScanArgsSplat,
    Trail: ScanArgsRequired,
    Kw: ScanArgsKw,
    Block: ScanArgsBlock,
{
    let arg_spec = ArgSpec::new(
        Req::LEN,
        Opt::LEN,
        Splat::REQ,
        Trail::LEN,
        Kw::REQ,
        Block::REQ,
    );
    let scanned_args = scan_args_untyped(args, arg_spec)?;

    Ok(Args {
        required: Req::from_slice(scanned_args.required())?,
        optional: Opt::from_slice(scanned_args.optional())?,
        splat: Splat::from_opt(scanned_args.splat())?,
        trailing: Trail::from_slice(scanned_args.trailing())?,
        keywords: Kw::from_opt(scanned_args.keywords())?,
        block: Block::from_opt(scanned_args.block())?,
    })
}

// Nice-ish interface to rb_scan_args, but returns `Value`s without conversion.
fn scan_args_untyped(args: &[Value], arg_spec: ArgSpec) -> Result<ScannedArgs, Error> {
    let mut out = [*QNIL; 30];
    let parsed =
        unsafe { scan_args_impl(args, &arg_spec.to_string(), &mut out[..arg_spec.len()])? };

    Ok(ScannedArgs {
        arg_spec,
        args: out,
        parsed,
    })
}

// Fairly close to rb_scan_args, but Rust types and works around variadic args.
// Size of `out` must be >= number of arguments specified in `fmt`.
unsafe fn scan_args_impl(args: &[Value], fmt: &str, out: &mut [Value]) -> Result<usize, Error> {
    let out: &mut [VALUE] = transmute(out);
    let argc = args.len() as c_int;
    let argv = args.as_ptr() as *const VALUE;
    let cstr = CString::new(fmt).unwrap();
    let fmt = cstr.as_ptr();
    let mut result = 0;
    match out.len() {
        0 => protect(|| {
            result = rb_scan_args(argc, argv, fmt) as usize;
            QNIL
        })?,
        1 => protect(|| {
            result = rb_scan_args(argc, argv, fmt, &mut out[0] as *mut VALUE) as usize;
            QNIL
        })?,
        2 => protect(|| {
            result = rb_scan_args(
                argc,
                argv,
                fmt,
                &mut out[0] as *mut VALUE,
                &mut out[1] as *mut VALUE,
            ) as usize;
            QNIL
        })?,
        3 => protect(|| {
            result = rb_scan_args(
                argc,
                argv,
                fmt,
                &mut out[0] as *mut VALUE,
                &mut out[1] as *mut VALUE,
                &mut out[2] as *mut VALUE,
            ) as usize;
            QNIL
        })?,
        4 => protect(|| {
            result = rb_scan_args(
                argc,
                argv,
                fmt,
                &mut out[0] as *mut VALUE,
                &mut out[1] as *mut VALUE,
                &mut out[2] as *mut VALUE,
                &mut out[3] as *mut VALUE,
            ) as usize;
            QNIL
        })?,
        5 => protect(|| {
            result = rb_scan_args(
                argc,
                argv,
                fmt,
                &mut out[0] as *mut VALUE,
                &mut out[1] as *mut VALUE,
                &mut out[2] as *mut VALUE,
                &mut out[3] as *mut VALUE,
                &mut out[4] as *mut VALUE,
            ) as usize;
            QNIL
        })?,
        6 => protect(|| {
            result = rb_scan_args(
                argc,
                argv,
                fmt,
                &mut out[0] as *mut VALUE,
                &mut out[1] as *mut VALUE,
                &mut out[2] as *mut VALUE,
                &mut out[3] as *mut VALUE,
                &mut out[4] as *mut VALUE,
                &mut out[5] as *mut VALUE,
            ) as usize;
            QNIL
        })?,
        7 => protect(|| {
            result = rb_scan_args(
                argc,
                argv,
                fmt,
                &mut out[0] as *mut VALUE,
                &mut out[1] as *mut VALUE,
                &mut out[2] as *mut VALUE,
                &mut out[3] as *mut VALUE,
                &mut out[4] as *mut VALUE,
                &mut out[5] as *mut VALUE,
                &mut out[6] as *mut VALUE,
            ) as usize;
            QNIL
        })?,
        8 => protect(|| {
            result = rb_scan_args(
                argc,
                argv,
                fmt,
                &mut out[0] as *mut VALUE,
                &mut out[1] as *mut VALUE,
                &mut out[2] as *mut VALUE,
                &mut out[3] as *mut VALUE,
                &mut out[4] as *mut VALUE,
                &mut out[5] as *mut VALUE,
                &mut out[6] as *mut VALUE,
                &mut out[7] as *mut VALUE,
            ) as usize;
            QNIL
        })?,
        9 => protect(|| {
            result = rb_scan_args(
                argc,
                argv,
                fmt,
                &mut out[0] as *mut VALUE,
                &mut out[1] as *mut VALUE,
                &mut out[2] as *mut VALUE,
                &mut out[3] as *mut VALUE,
                &mut out[4] as *mut VALUE,
                &mut out[5] as *mut VALUE,
                &mut out[6] as *mut VALUE,
                &mut out[7] as *mut VALUE,
                &mut out[8] as *mut VALUE,
            ) as usize;
            QNIL
        })?,
        10 => protect(|| {
            result = rb_scan_args(
                argc,
                argv,
                fmt,
                &mut out[0] as *mut VALUE,
                &mut out[1] as *mut VALUE,
                &mut out[2] as *mut VALUE,
                &mut out[3] as *mut VALUE,
                &mut out[4] as *mut VALUE,
                &mut out[5] as *mut VALUE,
                &mut out[6] as *mut VALUE,
                &mut out[7] as *mut VALUE,
                &mut out[8] as *mut VALUE,
                &mut out[9] as *mut VALUE,
            ) as usize;
            QNIL
        })?,
        11 => protect(|| {
            result = rb_scan_args(
                argc,
                argv,
                fmt,
                &mut out[0] as *mut VALUE,
                &mut out[1] as *mut VALUE,
                &mut out[2] as *mut VALUE,
                &mut out[3] as *mut VALUE,
                &mut out[4] as *mut VALUE,
                &mut out[5] as *mut VALUE,
                &mut out[6] as *mut VALUE,
                &mut out[7] as *mut VALUE,
                &mut out[8] as *mut VALUE,
                &mut out[9] as *mut VALUE,
                &mut out[10] as *mut VALUE,
            ) as usize;
            QNIL
        })?,
        12 => protect(|| {
            result = rb_scan_args(
                argc,
                argv,
                fmt,
                &mut out[0] as *mut VALUE,
                &mut out[1] as *mut VALUE,
                &mut out[2] as *mut VALUE,
                &mut out[3] as *mut VALUE,
                &mut out[4] as *mut VALUE,
                &mut out[5] as *mut VALUE,
                &mut out[6] as *mut VALUE,
                &mut out[7] as *mut VALUE,
                &mut out[8] as *mut VALUE,
                &mut out[9] as *mut VALUE,
                &mut out[10] as *mut VALUE,
                &mut out[11] as *mut VALUE,
            ) as usize;
            QNIL
        })?,
        13 => protect(|| {
            result = rb_scan_args(
                argc,
                argv,
                fmt,
                &mut out[0] as *mut VALUE,
                &mut out[1] as *mut VALUE,
                &mut out[2] as *mut VALUE,
                &mut out[3] as *mut VALUE,
                &mut out[4] as *mut VALUE,
                &mut out[5] as *mut VALUE,
                &mut out[6] as *mut VALUE,
                &mut out[7] as *mut VALUE,
                &mut out[8] as *mut VALUE,
                &mut out[9] as *mut VALUE,
                &mut out[10] as *mut VALUE,
                &mut out[11] as *mut VALUE,
                &mut out[12] as *mut VALUE,
            ) as usize;
            QNIL
        })?,
        14 => protect(|| {
            result = rb_scan_args(
                argc,
                argv,
                fmt,
                &mut out[0] as *mut VALUE,
                &mut out[1] as *mut VALUE,
                &mut out[2] as *mut VALUE,
                &mut out[3] as *mut VALUE,
                &mut out[4] as *mut VALUE,
                &mut out[5] as *mut VALUE,
                &mut out[6] as *mut VALUE,
                &mut out[7] as *mut VALUE,
                &mut out[8] as *mut VALUE,
                &mut out[9] as *mut VALUE,
                &mut out[10] as *mut VALUE,
                &mut out[11] as *mut VALUE,
                &mut out[12] as *mut VALUE,
                &mut out[13] as *mut VALUE,
            ) as usize;
            QNIL
        })?,
        15 => protect(|| {
            result = rb_scan_args(
                argc,
                argv,
                fmt,
                &mut out[0] as *mut VALUE,
                &mut out[1] as *mut VALUE,
                &mut out[2] as *mut VALUE,
                &mut out[3] as *mut VALUE,
                &mut out[4] as *mut VALUE,
                &mut out[5] as *mut VALUE,
                &mut out[6] as *mut VALUE,
                &mut out[7] as *mut VALUE,
                &mut out[8] as *mut VALUE,
                &mut out[9] as *mut VALUE,
                &mut out[10] as *mut VALUE,
                &mut out[11] as *mut VALUE,
                &mut out[12] as *mut VALUE,
                &mut out[13] as *mut VALUE,
                &mut out[14] as *mut VALUE,
            ) as usize;
            QNIL
        })?,
        16 => protect(|| {
            result = rb_scan_args(
                argc,
                argv,
                fmt,
                &mut out[0] as *mut VALUE,
                &mut out[1] as *mut VALUE,
                &mut out[2] as *mut VALUE,
                &mut out[3] as *mut VALUE,
                &mut out[4] as *mut VALUE,
                &mut out[5] as *mut VALUE,
                &mut out[6] as *mut VALUE,
                &mut out[7] as *mut VALUE,
                &mut out[8] as *mut VALUE,
                &mut out[9] as *mut VALUE,
                &mut out[10] as *mut VALUE,
                &mut out[11] as *mut VALUE,
                &mut out[12] as *mut VALUE,
                &mut out[13] as *mut VALUE,
                &mut out[14] as *mut VALUE,
                &mut out[15] as *mut VALUE,
            ) as usize;
            QNIL
        })?,
        17 => protect(|| {
            result = rb_scan_args(
                argc,
                argv,
                fmt,
                &mut out[0] as *mut VALUE,
                &mut out[1] as *mut VALUE,
                &mut out[2] as *mut VALUE,
                &mut out[3] as *mut VALUE,
                &mut out[4] as *mut VALUE,
                &mut out[5] as *mut VALUE,
                &mut out[6] as *mut VALUE,
                &mut out[7] as *mut VALUE,
                &mut out[8] as *mut VALUE,
                &mut out[9] as *mut VALUE,
                &mut out[10] as *mut VALUE,
                &mut out[11] as *mut VALUE,
                &mut out[12] as *mut VALUE,
                &mut out[13] as *mut VALUE,
                &mut out[14] as *mut VALUE,
                &mut out[15] as *mut VALUE,
                &mut out[16] as *mut VALUE,
            ) as usize;
            QNIL
        })?,
        18 => protect(|| {
            result = rb_scan_args(
                argc,
                argv,
                fmt,
                &mut out[0] as *mut VALUE,
                &mut out[1] as *mut VALUE,
                &mut out[2] as *mut VALUE,
                &mut out[3] as *mut VALUE,
                &mut out[4] as *mut VALUE,
                &mut out[5] as *mut VALUE,
                &mut out[6] as *mut VALUE,
                &mut out[7] as *mut VALUE,
                &mut out[8] as *mut VALUE,
                &mut out[9] as *mut VALUE,
                &mut out[10] as *mut VALUE,
                &mut out[11] as *mut VALUE,
                &mut out[12] as *mut VALUE,
                &mut out[13] as *mut VALUE,
                &mut out[14] as *mut VALUE,
                &mut out[15] as *mut VALUE,
                &mut out[16] as *mut VALUE,
                &mut out[17] as *mut VALUE,
            ) as usize;
            QNIL
        })?,
        19 => protect(|| {
            result = rb_scan_args(
                argc,
                argv,
                fmt,
                &mut out[0] as *mut VALUE,
                &mut out[1] as *mut VALUE,
                &mut out[2] as *mut VALUE,
                &mut out[3] as *mut VALUE,
                &mut out[4] as *mut VALUE,
                &mut out[5] as *mut VALUE,
                &mut out[6] as *mut VALUE,
                &mut out[7] as *mut VALUE,
                &mut out[8] as *mut VALUE,
                &mut out[9] as *mut VALUE,
                &mut out[10] as *mut VALUE,
                &mut out[11] as *mut VALUE,
                &mut out[12] as *mut VALUE,
                &mut out[13] as *mut VALUE,
                &mut out[14] as *mut VALUE,
                &mut out[15] as *mut VALUE,
                &mut out[16] as *mut VALUE,
                &mut out[17] as *mut VALUE,
                &mut out[18] as *mut VALUE,
            ) as usize;
            QNIL
        })?,
        20 => protect(|| {
            result = rb_scan_args(
                argc,
                argv,
                fmt,
                &mut out[0] as *mut VALUE,
                &mut out[1] as *mut VALUE,
                &mut out[2] as *mut VALUE,
                &mut out[3] as *mut VALUE,
                &mut out[4] as *mut VALUE,
                &mut out[5] as *mut VALUE,
                &mut out[6] as *mut VALUE,
                &mut out[7] as *mut VALUE,
                &mut out[8] as *mut VALUE,
                &mut out[9] as *mut VALUE,
                &mut out[10] as *mut VALUE,
                &mut out[11] as *mut VALUE,
                &mut out[12] as *mut VALUE,
                &mut out[13] as *mut VALUE,
                &mut out[14] as *mut VALUE,
                &mut out[15] as *mut VALUE,
                &mut out[16] as *mut VALUE,
                &mut out[17] as *mut VALUE,
                &mut out[18] as *mut VALUE,
                &mut out[19] as *mut VALUE,
            ) as usize;
            QNIL
        })?,
        21 => protect(|| {
            result = rb_scan_args(
                argc,
                argv,
                fmt,
                &mut out[0] as *mut VALUE,
                &mut out[1] as *mut VALUE,
                &mut out[2] as *mut VALUE,
                &mut out[3] as *mut VALUE,
                &mut out[4] as *mut VALUE,
                &mut out[5] as *mut VALUE,
                &mut out[6] as *mut VALUE,
                &mut out[7] as *mut VALUE,
                &mut out[8] as *mut VALUE,
                &mut out[9] as *mut VALUE,
                &mut out[10] as *mut VALUE,
                &mut out[11] as *mut VALUE,
                &mut out[12] as *mut VALUE,
                &mut out[13] as *mut VALUE,
                &mut out[14] as *mut VALUE,
                &mut out[15] as *mut VALUE,
                &mut out[16] as *mut VALUE,
                &mut out[17] as *mut VALUE,
                &mut out[18] as *mut VALUE,
                &mut out[19] as *mut VALUE,
                &mut out[20] as *mut VALUE,
            ) as usize;
            QNIL
        })?,
        22 => protect(|| {
            result = rb_scan_args(
                argc,
                argv,
                fmt,
                &mut out[0] as *mut VALUE,
                &mut out[1] as *mut VALUE,
                &mut out[2] as *mut VALUE,
                &mut out[3] as *mut VALUE,
                &mut out[4] as *mut VALUE,
                &mut out[5] as *mut VALUE,
                &mut out[6] as *mut VALUE,
                &mut out[7] as *mut VALUE,
                &mut out[8] as *mut VALUE,
                &mut out[9] as *mut VALUE,
                &mut out[10] as *mut VALUE,
                &mut out[11] as *mut VALUE,
                &mut out[12] as *mut VALUE,
                &mut out[13] as *mut VALUE,
                &mut out[14] as *mut VALUE,
                &mut out[15] as *mut VALUE,
                &mut out[16] as *mut VALUE,
                &mut out[17] as *mut VALUE,
                &mut out[18] as *mut VALUE,
                &mut out[19] as *mut VALUE,
                &mut out[20] as *mut VALUE,
                &mut out[21] as *mut VALUE,
            ) as usize;
            QNIL
        })?,
        23 => protect(|| {
            result = rb_scan_args(
                argc,
                argv,
                fmt,
                &mut out[0] as *mut VALUE,
                &mut out[1] as *mut VALUE,
                &mut out[2] as *mut VALUE,
                &mut out[3] as *mut VALUE,
                &mut out[4] as *mut VALUE,
                &mut out[5] as *mut VALUE,
                &mut out[6] as *mut VALUE,
                &mut out[7] as *mut VALUE,
                &mut out[8] as *mut VALUE,
                &mut out[9] as *mut VALUE,
                &mut out[10] as *mut VALUE,
                &mut out[11] as *mut VALUE,
                &mut out[12] as *mut VALUE,
                &mut out[13] as *mut VALUE,
                &mut out[14] as *mut VALUE,
                &mut out[15] as *mut VALUE,
                &mut out[16] as *mut VALUE,
                &mut out[17] as *mut VALUE,
                &mut out[18] as *mut VALUE,
                &mut out[19] as *mut VALUE,
                &mut out[20] as *mut VALUE,
                &mut out[21] as *mut VALUE,
                &mut out[22] as *mut VALUE,
            ) as usize;
            QNIL
        })?,
        24 => protect(|| {
            result = rb_scan_args(
                argc,
                argv,
                fmt,
                &mut out[0] as *mut VALUE,
                &mut out[1] as *mut VALUE,
                &mut out[2] as *mut VALUE,
                &mut out[3] as *mut VALUE,
                &mut out[4] as *mut VALUE,
                &mut out[5] as *mut VALUE,
                &mut out[6] as *mut VALUE,
                &mut out[7] as *mut VALUE,
                &mut out[8] as *mut VALUE,
                &mut out[9] as *mut VALUE,
                &mut out[10] as *mut VALUE,
                &mut out[11] as *mut VALUE,
                &mut out[12] as *mut VALUE,
                &mut out[13] as *mut VALUE,
                &mut out[14] as *mut VALUE,
                &mut out[15] as *mut VALUE,
                &mut out[16] as *mut VALUE,
                &mut out[17] as *mut VALUE,
                &mut out[18] as *mut VALUE,
                &mut out[19] as *mut VALUE,
                &mut out[20] as *mut VALUE,
                &mut out[21] as *mut VALUE,
                &mut out[22] as *mut VALUE,
                &mut out[23] as *mut VALUE,
            ) as usize;
            QNIL
        })?,
        25 => protect(|| {
            result = rb_scan_args(
                argc,
                argv,
                fmt,
                &mut out[0] as *mut VALUE,
                &mut out[1] as *mut VALUE,
                &mut out[2] as *mut VALUE,
                &mut out[3] as *mut VALUE,
                &mut out[4] as *mut VALUE,
                &mut out[5] as *mut VALUE,
                &mut out[6] as *mut VALUE,
                &mut out[7] as *mut VALUE,
                &mut out[8] as *mut VALUE,
                &mut out[9] as *mut VALUE,
                &mut out[10] as *mut VALUE,
                &mut out[11] as *mut VALUE,
                &mut out[12] as *mut VALUE,
                &mut out[13] as *mut VALUE,
                &mut out[14] as *mut VALUE,
                &mut out[15] as *mut VALUE,
                &mut out[16] as *mut VALUE,
                &mut out[17] as *mut VALUE,
                &mut out[18] as *mut VALUE,
                &mut out[19] as *mut VALUE,
                &mut out[20] as *mut VALUE,
                &mut out[21] as *mut VALUE,
                &mut out[22] as *mut VALUE,
                &mut out[23] as *mut VALUE,
                &mut out[24] as *mut VALUE,
            ) as usize;
            QNIL
        })?,
        26 => protect(|| {
            result = rb_scan_args(
                argc,
                argv,
                fmt,
                &mut out[0] as *mut VALUE,
                &mut out[1] as *mut VALUE,
                &mut out[2] as *mut VALUE,
                &mut out[3] as *mut VALUE,
                &mut out[4] as *mut VALUE,
                &mut out[5] as *mut VALUE,
                &mut out[6] as *mut VALUE,
                &mut out[7] as *mut VALUE,
                &mut out[8] as *mut VALUE,
                &mut out[9] as *mut VALUE,
                &mut out[10] as *mut VALUE,
                &mut out[11] as *mut VALUE,
                &mut out[12] as *mut VALUE,
                &mut out[13] as *mut VALUE,
                &mut out[14] as *mut VALUE,
                &mut out[15] as *mut VALUE,
                &mut out[16] as *mut VALUE,
                &mut out[17] as *mut VALUE,
                &mut out[18] as *mut VALUE,
                &mut out[19] as *mut VALUE,
                &mut out[20] as *mut VALUE,
                &mut out[21] as *mut VALUE,
                &mut out[22] as *mut VALUE,
                &mut out[23] as *mut VALUE,
                &mut out[24] as *mut VALUE,
                &mut out[25] as *mut VALUE,
            ) as usize;
            QNIL
        })?,
        27 => protect(|| {
            result = rb_scan_args(
                argc,
                argv,
                fmt,
                &mut out[0] as *mut VALUE,
                &mut out[1] as *mut VALUE,
                &mut out[2] as *mut VALUE,
                &mut out[3] as *mut VALUE,
                &mut out[4] as *mut VALUE,
                &mut out[5] as *mut VALUE,
                &mut out[6] as *mut VALUE,
                &mut out[7] as *mut VALUE,
                &mut out[8] as *mut VALUE,
                &mut out[9] as *mut VALUE,
                &mut out[10] as *mut VALUE,
                &mut out[11] as *mut VALUE,
                &mut out[12] as *mut VALUE,
                &mut out[13] as *mut VALUE,
                &mut out[14] as *mut VALUE,
                &mut out[15] as *mut VALUE,
                &mut out[16] as *mut VALUE,
                &mut out[17] as *mut VALUE,
                &mut out[18] as *mut VALUE,
                &mut out[19] as *mut VALUE,
                &mut out[20] as *mut VALUE,
                &mut out[21] as *mut VALUE,
                &mut out[22] as *mut VALUE,
                &mut out[23] as *mut VALUE,
                &mut out[24] as *mut VALUE,
                &mut out[25] as *mut VALUE,
                &mut out[26] as *mut VALUE,
            ) as usize;
            QNIL
        })?,
        28 => protect(|| {
            result = rb_scan_args(
                argc,
                argv,
                fmt,
                &mut out[0] as *mut VALUE,
                &mut out[1] as *mut VALUE,
                &mut out[2] as *mut VALUE,
                &mut out[3] as *mut VALUE,
                &mut out[4] as *mut VALUE,
                &mut out[5] as *mut VALUE,
                &mut out[6] as *mut VALUE,
                &mut out[7] as *mut VALUE,
                &mut out[8] as *mut VALUE,
                &mut out[9] as *mut VALUE,
                &mut out[10] as *mut VALUE,
                &mut out[11] as *mut VALUE,
                &mut out[12] as *mut VALUE,
                &mut out[13] as *mut VALUE,
                &mut out[14] as *mut VALUE,
                &mut out[15] as *mut VALUE,
                &mut out[16] as *mut VALUE,
                &mut out[17] as *mut VALUE,
                &mut out[18] as *mut VALUE,
                &mut out[19] as *mut VALUE,
                &mut out[20] as *mut VALUE,
                &mut out[21] as *mut VALUE,
                &mut out[22] as *mut VALUE,
                &mut out[23] as *mut VALUE,
                &mut out[24] as *mut VALUE,
                &mut out[25] as *mut VALUE,
                &mut out[26] as *mut VALUE,
                &mut out[27] as *mut VALUE,
            ) as usize;
            QNIL
        })?,
        29 => protect(|| {
            result = rb_scan_args(
                argc,
                argv,
                fmt,
                &mut out[0] as *mut VALUE,
                &mut out[1] as *mut VALUE,
                &mut out[2] as *mut VALUE,
                &mut out[3] as *mut VALUE,
                &mut out[4] as *mut VALUE,
                &mut out[5] as *mut VALUE,
                &mut out[6] as *mut VALUE,
                &mut out[7] as *mut VALUE,
                &mut out[8] as *mut VALUE,
                &mut out[9] as *mut VALUE,
                &mut out[10] as *mut VALUE,
                &mut out[11] as *mut VALUE,
                &mut out[12] as *mut VALUE,
                &mut out[13] as *mut VALUE,
                &mut out[14] as *mut VALUE,
                &mut out[15] as *mut VALUE,
                &mut out[16] as *mut VALUE,
                &mut out[17] as *mut VALUE,
                &mut out[18] as *mut VALUE,
                &mut out[19] as *mut VALUE,
                &mut out[20] as *mut VALUE,
                &mut out[21] as *mut VALUE,
                &mut out[22] as *mut VALUE,
                &mut out[23] as *mut VALUE,
                &mut out[24] as *mut VALUE,
                &mut out[25] as *mut VALUE,
                &mut out[26] as *mut VALUE,
                &mut out[27] as *mut VALUE,
                &mut out[28] as *mut VALUE,
            ) as usize;
            QNIL
        })?,
        _ => protect(|| {
            result = rb_scan_args(
                argc,
                argv,
                fmt,
                &mut out[0] as *mut VALUE,
                &mut out[1] as *mut VALUE,
                &mut out[2] as *mut VALUE,
                &mut out[3] as *mut VALUE,
                &mut out[4] as *mut VALUE,
                &mut out[5] as *mut VALUE,
                &mut out[6] as *mut VALUE,
                &mut out[7] as *mut VALUE,
                &mut out[8] as *mut VALUE,
                &mut out[9] as *mut VALUE,
                &mut out[10] as *mut VALUE,
                &mut out[11] as *mut VALUE,
                &mut out[12] as *mut VALUE,
                &mut out[13] as *mut VALUE,
                &mut out[14] as *mut VALUE,
                &mut out[15] as *mut VALUE,
                &mut out[16] as *mut VALUE,
                &mut out[17] as *mut VALUE,
                &mut out[18] as *mut VALUE,
                &mut out[19] as *mut VALUE,
                &mut out[20] as *mut VALUE,
                &mut out[21] as *mut VALUE,
                &mut out[22] as *mut VALUE,
                &mut out[23] as *mut VALUE,
                &mut out[24] as *mut VALUE,
                &mut out[25] as *mut VALUE,
                &mut out[26] as *mut VALUE,
                &mut out[27] as *mut VALUE,
                &mut out[28] as *mut VALUE,
                &mut out[29] as *mut VALUE,
            ) as usize;
            QNIL
        })?,
    };
    Ok(result)
}

/// Arguments returned from [`get_kwargs`].
pub struct KwArgs<Req, Opt, Splat> {
    /// Required arguments.
    pub required: Req,
    /// Optional arguments.
    pub optional: Opt,
    /// The splat argument.
    pub splat: Splat,
}

/// Deconstruct keyword arguments.
///
/// Extracts `required` and `optional` arguments from the given `kw` hash.
///
/// The format of the arguments required is driven by the types in the return
/// value. The stuct [`KwArgs`] is returned but the types of its fields are
/// determined by type parameters. The type `()` is used as a placeholder when
/// a set of arguments is not required.
///
/// # Panics
///
/// This function will panic if `required` or `optional` arguments don't match
/// the length of the `Req` and `Opt` type parameters.
///
/// # Examples
///
/// The rough equivalent of `def example(a:, b:, c: nil, **rest)` would be:
/// ```
/// use magnus::{prelude::*, class, error::Error, method, scan_args::get_kwargs, RHash, Value};
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// fn example(rb_self: Value, kw: RHash) -> Result<Value, Error> {
///     let args = get_kwargs(kw, &["a", "b"], &["c"])?;
///     let (a, b): (String, usize) = args.required;
///     let (c,): (Option<bool>,) = args.optional;
///     let rest: RHash = args.splat;
///
///     // ...
/// #   let res = magnus::RArray::with_capacity(4);
/// #   res.push(a)?;
/// #   res.push(b)?;
/// #   res.push(c)?;
/// #   res.push(rest)?;
/// #   Ok(res.into())
/// }
///
/// class::object().define_method("example", method!(example, 1)).unwrap();
/// # let res = magnus::eval::<bool>(r#"Object.new.example(a: "foo", b: 1, c: true, d: "bar") == ["foo", 1, true, {d: "bar"}]"#).unwrap();
/// # assert!(res);
/// # let res = magnus::eval::<bool>(r#"Object.new.example(a: "foo", b: 1) == ["foo", 1, nil, {}]"#).unwrap();
/// # assert!(res);
/// ```
/// The rough equivalent of `def example(a: "foo")` would be:
/// ```
/// use magnus::{prelude::*, class, error::Error, method, scan_args::{get_kwargs, scan_args}, RHash, Value};
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// fn example(rb_self: Value, args: &[Value]) -> Result<Value, Error> {
///     let args = scan_args::<(), (), (), (), _, ()>(args)?;
///     let args = get_kwargs(args.keywords, &[], &["a"])?;
///     let _: () = args.required;
///     let (a,): (Option<String>,) = args.optional;
///     let _: () = args.splat;
///
///     let a  = a.unwrap_or_else(|| String::from("foo"));
///
///     // ...
///     Ok(a.into())
/// }
///
/// class::object().define_method("example", method!(example, -1)).unwrap();
/// # let res = magnus::eval::<bool>(r#"Object.new.example(a: "test") == "test""#).unwrap();
/// # assert!(res);
/// # let res = magnus::eval::<bool>(r#"Object.new.example == "foo""#).unwrap();
/// # assert!(res);
/// ```
/// or, specifying the types slightly differently:
/// ```
/// use magnus::{prelude::*, class, error::Error, method, scan_args::{get_kwargs, scan_args}, RHash, Value};
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// fn example(rb_self: Value, args: &[Value]) -> Result<Value, Error> {
///     let args = scan_args::<(), (), (), (), RHash, ()>(args)?;
///     let args = get_kwargs::<_, (), (Option<String>,), ()>(args.keywords, &[], &["a"])?;
///     let (a,) = args.optional;
///     let a  = a.unwrap_or_else(|| String::from("foo"));
///
///     // ...
///     Ok(a.into())
/// }
///
/// class::object().define_method("example", method!(example, -1)).unwrap();
/// # let res = magnus::eval::<bool>(r#"Object.new.example(a: "test") == "test""#).unwrap();
/// # assert!(res);
/// # let res = magnus::eval::<bool>(r#"Object.new.example == "foo""#).unwrap();
/// # assert!(res);
/// ```
pub fn get_kwargs<T, Req, Opt, Splat>(
    kw: RHash,
    required: &[T],
    optional: &[T],
) -> Result<KwArgs<Req, Opt, Splat>, Error>
where
    T: IntoId + Copy,
    Req: ScanArgsRequired,
    Opt: ScanArgsOpt,
    Splat: ScanArgsKw,
{
    assert_eq!(required.len(), Req::LEN);
    assert_eq!(optional.len(), Opt::LEN);

    let ids = required
        .iter()
        .copied()
        .map(|id| unsafe { id.into_id_unchecked() })
        .chain(
            optional
                .iter()
                .copied()
                .map(|id| unsafe { id.into_id_unchecked() }),
        )
        .collect::<Vec<Id>>();
    let optional_len = if Splat::REQ {
        -(optional.len() as i8 + 1)
    } else {
        optional.len() as i8
    };
    let mut out = [*QNIL; 19];
    let total = Req::LEN + Opt::LEN + Splat::REQ as usize;

    let mut parsed = 0;
    unsafe {
        protect(|| {
            parsed = rb_get_kwargs(
                kw.as_rb_value(),
                ids.as_ptr() as *const ID,
                required.len() as c_int,
                optional_len as c_int,
                out[..total].as_mut_ptr() as *mut VALUE,
            ) as usize;
            QNIL
        })?;
    };

    let opt_end = Req::LEN + Opt::LEN;
    Ok(KwArgs {
        required: Req::from_slice(&out[..Req::LEN])?,
        optional: Opt::from_slice(&out[Req::LEN..opt_end])?,
        splat: Splat::from_opt(Splat::REQ.then(|| kw.into()))?,
    })
}

impl RubyHandle {
    pub fn check_arity<T>(&self, len: usize, bounds: T) -> Result<(), Error>
    where
        T: RangeBounds<usize>,
    {
        if !bounds.contains(&len) {
            let min = match bounds.start_bound() {
                Bound::Included(v) => *v as c_int,
                Bound::Excluded(_) => unreachable!(),
                Bound::Unbounded => 0,
            };
            let max = match bounds.end_bound() {
                Bound::Included(v) => *v as c_int,
                Bound::Excluded(v) if *v == 0 => 0,
                Bound::Excluded(v) => (v - 1) as c_int,
                Bound::Unbounded => -1,
            };
            protect(|| {
                unsafe { rb_error_arity(len as c_int, min, max) };
                QNIL
            })?;
        }
        Ok(())
    }
}

/// Returns `Err` containing a Ruby `ArgumentError` if `len` is not within
/// `bounds`.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
///
/// # Examples
///
/// ```
/// use magnus::{define_global_function, eval, function, scan_args::check_arity, Error, RArray, RString, Value};
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// fn example(args: &[Value]) -> Result<RString, Error> {
///     check_arity(args.len(), 2..5)?;
///     RArray::from_slice(args).join(", ")
/// }
///
/// define_global_function("example", function!(example, -1));
///
/// assert_eq!(eval::<String>("example(1)").unwrap_err().to_string(), "wrong number of arguments (given 1, expected 2..4)");
/// assert_eq!(eval::<String>("example(1, 2, 3, 4, 5)").unwrap_err().to_string(), "wrong number of arguments (given 5, expected 2..4)");
/// ```
#[inline]
pub fn check_arity<T>(len: usize, bounds: T) -> Result<(), Error>
where
    T: RangeBounds<usize>,
{
    get_ruby!().check_arity(len, bounds)
}
