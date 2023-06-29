use seq_macro::seq;

use crate::{
    r_array::RArray,
    r_hash::RHash,
    value::{ReprValue, Value},
    Ruby,
};

/// # Conversion to `Value`
///
/// Helpers for the [`IntoValue`] trait.
///
/// See also the [`IntoValue`] trait.
impl Ruby {
    /// Convert `val` into [`Value`].
    #[allow(clippy::wrong_self_convention)]
    #[inline]
    pub fn into_value<T>(&self, val: T) -> Value
    where
        T: IntoValue,
    {
        val.into_value_with(self)
    }
}

/// Conversions from Rust types into [`Value`].
pub trait IntoValue: Sized {
    /// Convert `self` into [`Value`].
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread. See
    /// [`IntoValue::into_value_with`] for the non-panicking version.
    #[cfg_attr(
        not(feature = "friendly-api"),
        deprecated(note = "please use `IntoValue::into_value_with` instead")
    )]
    #[inline]
    fn into_value(self) -> Value {
        self.into_value_with(&get_ruby!())
    }

    /// Convert `self` into [`Value`].
    ///
    /// # Safety
    ///
    /// This method should only be called from a Ruby thread.
    #[inline]
    unsafe fn into_value_unchecked(self) -> Value {
        self.into_value_with(&Ruby::get_unchecked())
    }

    /// Convert `self` into [`Value`].
    fn into_value_with(self, handle: &Ruby) -> Value;
}

/// Conversions from Rust types that do not contain [`Value`] into [`Value`].
///
/// This trait is used as a bound in functions such as
/// [`RArray::from_vec`](crate::r_array::RArray::from_vec) to prevent accepting
/// heap allocated datastructures containing `Value`, as it is not safe to
/// store a `Value` on the heap.
///
/// # Safety
///
/// This trait must not be implemented for types that contain `Value`.
pub unsafe trait IntoValueFromNative: IntoValue {}

/// Trait for types that can be used as an arguments list when calling Ruby
/// methods.
pub trait ArgList {
    /// The specific Ruby value type.
    type Value: ReprValue;
    /// The type of the arguments list. Must convert to `&[Self::Value]` with
    /// [`AsRef`].
    type Output: AsRef<[Self::Value]>;

    /// Convert `self` into a type that can be used as a Ruby argument list.
    fn into_arg_list_with(self, handle: &Ruby) -> Self::Output;

    /// Whether the argument list contains keyword arguments. If true, the
    /// last element of the `&[Self::Value]` produced by
    /// `Self::into_arg_list_with` and [`AsRef`] must be a [`RHash`]
    fn contains_kw_args(&self) -> bool;
}

pub(crate) fn kw_splat(args: &impl RArrayArgList) -> u32 {
    if args.contains_kw_args() {
        rb_sys::RB_PASS_KEYWORDS
    } else {
        rb_sys::RB_NO_KEYWORDS
    }
}

/// Wrapper for [`RHash`] intended for use in the tuple implementations of
/// [`ArgList`] to indicate that the last argument in the tuple is to be
/// passed as keyword arguments.
#[repr(transparent)]
pub struct KwArgs(pub RHash);

/// Create a [`KwArgs`] from Rust key-value mappings. Keys must be string
/// literals, while values can be anything that implements [`IntoValue`].
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
///
/// # Examples
///
/// ```
/// use magnus::{eval, kwargs, prelude::*, RObject};
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// let kwargs = kwargs!("a" => 1, "b" => 2);
/// let object: RObject = eval!(
///     r#"
///     class Adder
///       def add(a:, b:)
///         a + b
///       end
///     end
///
///     Adder.new
/// "#
/// )
/// .unwrap();
///
/// let result: i32 = object.funcall("add", (kwargs,)).unwrap();
/// assert_eq!(3, result);
/// ```
#[macro_export]
macro_rules! kwargs {
    ($ruby:expr, $($k:literal => $v:expr),+) => {{
        use $crate::IntoValue;
        let h = $ruby.hash_new();
        $(
            h.aset(
                $ruby.to_symbol($k),
                $v.into_value_with($ruby),
            ).unwrap();
        )+
        $crate::KwArgs(h)
    }};
    ($($k:literal => $v:expr),+) => {{
        $crate::kwargs!(&$crate::Ruby::get().unwrap(), $($k => $v),+)
    }};
}

/// # Safety
///
/// The implmentation of `ArgList` for slices is not intended to suggest that
/// it is valid to build a `Vec` of Ruby values to then convert to a slice.
/// [Ruby values should never be put into a `Vec`](crate#safety).
impl<'a, T> ArgList for &'a [T]
where
    T: ReprValue,
{
    type Value = T;
    type Output = &'a [Self::Value];

    fn into_arg_list_with(self, _: &Ruby) -> Self::Output {
        self
    }

    fn contains_kw_args(&self) -> bool {
        false
    }
}

macro_rules! impl_arg_list {
    ($n:literal) => {
        seq!(N in 0..$n {
            impl<#(T~N,)*> ArgList for (#(T~N,)*)
            where
                #(T~N: IntoValue,)*
            {
                type Value = Value;
                type Output = [Self::Value; $n];

                #[allow(unused_variables)]
                fn into_arg_list_with(self, handle: &Ruby) -> Self::Output {
                    [#(handle.into_value(self.N),)*]
                }

                fn contains_kw_args(&self) -> bool {
                    false
                }
            }
        });
    }
}

seq!(N in 0..=12 {
    impl_arg_list!(N);
});

macro_rules! impl_arg_list_kw {
    ($n:literal) => {
        seq!(N in 0..$n {
            impl<#(T~N,)*> ArgList for (#(T~N,)* KwArgs,)
            where
                #(T~N: IntoValue,)*
            {
                type Value = Value;
                type Output = [Self::Value; { $n + 1 }];

                #[allow(unused_variables)]
                fn into_arg_list_with(self, handle: &Ruby) -> Self::Output {
                    [#(handle.into_value(self.N),)* handle.into_value(self.$n.0)]
                }

                fn contains_kw_args(&self) -> bool {
                    true
                }
            }
        });
    }
}

seq!(N in 0..=12 {
    impl_arg_list_kw!(N);
});

impl<T, const N: usize> ArgList for [T; N]
where
    T: ReprValue,
{
    type Value = T;
    type Output = [Self::Value; N];

    fn into_arg_list_with(self, _: &Ruby) -> Self::Output {
        self
    }

    fn contains_kw_args(&self) -> bool {
        false
    }
}

/// Trait for types that can be used as an arguments list when calling Ruby
/// Procs.
pub trait RArrayArgList {
    /// Convert `self` into a type that can be used as a Ruby Proc argument
    /// list.
    fn into_array_arg_list_with(self, handle: &Ruby) -> RArray;

    /// Whether the argument list contains keyword arguments. If true, the
    /// last element of the `RArray` produced by
    /// `Self::into_array_arg_list_with` must be a [`RHash`]
    fn contains_kw_args(&self) -> bool;
}

impl RArrayArgList for RArray {
    fn into_array_arg_list_with(self, _: &Ruby) -> RArray {
        self
    }

    fn contains_kw_args(&self) -> bool {
        false
    }
}

impl<T> RArrayArgList for T
where
    T: ArgList,
{
    fn into_array_arg_list_with(self, handle: &Ruby) -> RArray {
        handle.ary_new_from_values(self.into_arg_list_with(handle).as_ref())
    }

    fn contains_kw_args(&self) -> bool {
        <Self as ArgList>::contains_kw_args(self)
    }
}
