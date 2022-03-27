//! Types and functions for complex method arguments.

use std::{ffi::CString, fmt, mem::transmute, os::raw::c_int};

use crate::{
    block::Proc,
    error::{protect, Error},
    exception,
    r_array::RArray,
    r_hash::RHash,
    ruby_sys::{rb_scan_args, VALUE},
    try_convert::{TryConvert, TryConvertOwned},
    value::{Value, QNIL},
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
        let end = start + self.arg_spec.optional.min(self.parsed - start);
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
                Ok((vals.get(0).map(|v| v.try_convert()).transpose()?,))
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
                    vals.get(0).map(|v| v.try_convert()).transpose()?,
                    vals.get(1).map(|v| v.try_convert()).transpose()?,
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
                    vals.get(0).map(|v| v.try_convert()).transpose()?,
                    vals.get(1).map(|v| v.try_convert()).transpose()?,
                    vals.get(2).map(|v| v.try_convert()).transpose()?,
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
                    vals.get(0).map(|v| v.try_convert()).transpose()?,
                    vals.get(1).map(|v| v.try_convert()).transpose()?,
                    vals.get(2).map(|v| v.try_convert()).transpose()?,
                    vals.get(3).map(|v| v.try_convert()).transpose()?,
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
                    vals.get(0).map(|v| v.try_convert()).transpose()?,
                    vals.get(1).map(|v| v.try_convert()).transpose()?,
                    vals.get(2).map(|v| v.try_convert()).transpose()?,
                    vals.get(3).map(|v| v.try_convert()).transpose()?,
                    vals.get(4).map(|v| v.try_convert()).transpose()?,
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
                    vals.get(0).map(|v| v.try_convert()).transpose()?,
                    vals.get(1).map(|v| v.try_convert()).transpose()?,
                    vals.get(2).map(|v| v.try_convert()).transpose()?,
                    vals.get(3).map(|v| v.try_convert()).transpose()?,
                    vals.get(4).map(|v| v.try_convert()).transpose()?,
                    vals.get(5).map(|v| v.try_convert()).transpose()?,
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
                    vals.get(0).map(|v| v.try_convert()).transpose()?,
                    vals.get(1).map(|v| v.try_convert()).transpose()?,
                    vals.get(2).map(|v| v.try_convert()).transpose()?,
                    vals.get(3).map(|v| v.try_convert()).transpose()?,
                    vals.get(4).map(|v| v.try_convert()).transpose()?,
                    vals.get(5).map(|v| v.try_convert()).transpose()?,
                    vals.get(6).map(|v| v.try_convert()).transpose()?,
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
                    vals.get(0).map(|v| v.try_convert()).transpose()?,
                    vals.get(1).map(|v| v.try_convert()).transpose()?,
                    vals.get(2).map(|v| v.try_convert()).transpose()?,
                    vals.get(3).map(|v| v.try_convert()).transpose()?,
                    vals.get(4).map(|v| v.try_convert()).transpose()?,
                    vals.get(5).map(|v| v.try_convert()).transpose()?,
                    vals.get(6).map(|v| v.try_convert()).transpose()?,
                    vals.get(7).map(|v| v.try_convert()).transpose()?,
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
                    vals.get(0).map(|v| v.try_convert()).transpose()?,
                    vals.get(1).map(|v| v.try_convert()).transpose()?,
                    vals.get(2).map(|v| v.try_convert()).transpose()?,
                    vals.get(3).map(|v| v.try_convert()).transpose()?,
                    vals.get(4).map(|v| v.try_convert()).transpose()?,
                    vals.get(5).map(|v| v.try_convert()).transpose()?,
                    vals.get(6).map(|v| v.try_convert()).transpose()?,
                    vals.get(7).map(|v| v.try_convert()).transpose()?,
                    vals.get(8).map(|v| v.try_convert()).transpose()?,
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
pub trait ScanArgsRequired: private::ScanArgsRequired {}
impl<T> ScanArgsRequired for T where T: private::ScanArgsRequired {}

/// Trait implemented for types that can be retrieved as optional arguments by
/// [`scan_args`].
pub trait ScanArgsOpt: private::ScanArgsOpt {}
impl<T> ScanArgsOpt for T where T: private::ScanArgsOpt {}

/// Trait implemented for types that can be retrieved a 'splat' argument by
/// [`scan_args`].
pub trait ScanArgsSplat: private::ScanArgsSplat {}
impl<T> ScanArgsSplat for T where T: private::ScanArgsSplat {}

/// Trait implemented for types that can be retrieved as keyword arguments by
/// [`scan_args`].
pub trait ScanArgsKw: private::ScanArgsKw {}
impl<T> ScanArgsKw for T where T: private::ScanArgsKw {}

/// Trait implemented for types that can be retrieved as a block argument by
/// [`scan_args`].
pub trait ScanArgsBlock: private::ScanArgsBlock {}
impl<T> ScanArgsBlock for T where T: private::ScanArgsBlock {}

/// Retrieves arguments from a slice.
///
/// This function can be used to implement Ruby methods with more complex
/// signatures, including optional arguments and 'splats'.
///
/// # Examples
///
/// `TCPServer::new`'s argument handling. This is roughly equivalent to
/// `def new(hostname=nil, port)`.
/// ```
/// use magnus::{define_class, error::Error, eval, function, scan_args::scan_args, Object, Value};
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
///     todo!()
/// }
///
/// let class = define_class("TCPServer", Default::default()).unwrap();
/// class.define_singleton_method("new", function!(tcp_svr_init, -1));
/// ```
///
/// The same example as above, specifying the types slightly differently.
/// ```
/// use magnus::{define_class, error::Error, eval, function, scan_args::scan_args, Object, Value};
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// fn tcp_svr_init(args: &[Value]) -> Result<Value, Error> {
///     let args = scan_args::<(), (Option<String>,), (), (u16,), (), ()>(args)?;
///     let (hostname,) = args.optional;
///     let (port,) = args.trailing;
///
///     todo!()
/// }
///
/// let class = define_class("TCPServer", Default::default()).unwrap();
/// class.define_singleton_method("new", function!(tcp_svr_init, -1));
/// ```
///
/// `Addrinfo::getaddrinfo`'s argument handling. This is roughly equivalent to
/// `def getaddrinfo(nodename, service, family=nil, socktype=nil, protocol=nil, flags=nil, timeout: nil)`.
/// ```
/// use magnus::{
///     define_class, error::Error, eval, function, scan_args::scan_args, Object, RHash, Symbol, Value,
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
///     let kw: RHash = args.keywords;
///
///     todo!()
/// }
///
/// let class = define_class("Addrinfo", Default::default()).unwrap();
/// class.define_singleton_method("getaddrinfo", function!(getaddrinfo, -1));
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
            *QNIL
        })?,
        1 => protect(|| {
            result = rb_scan_args(argc, argv, fmt, &mut out[0] as *mut VALUE) as usize;
            *QNIL
        })?,
        2 => protect(|| {
            result = rb_scan_args(
                argc,
                argv,
                fmt,
                &mut out[0] as *mut VALUE,
                &mut out[1] as *mut VALUE,
            ) as usize;
            *QNIL
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
            *QNIL
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
            *QNIL
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
            *QNIL
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
            *QNIL
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
            *QNIL
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
            *QNIL
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
            *QNIL
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
            *QNIL
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
            *QNIL
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
            *QNIL
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
            *QNIL
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
            *QNIL
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
            *QNIL
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
            *QNIL
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
            *QNIL
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
            *QNIL
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
            *QNIL
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
            *QNIL
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
            *QNIL
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
            *QNIL
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
            *QNIL
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
            *QNIL
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
            *QNIL
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
            *QNIL
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
            *QNIL
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
            *QNIL
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
            *QNIL
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
            *QNIL
        })?,
    };
    Ok(result)
}
