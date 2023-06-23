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
    #[cfg(feature = "friendly-api")]
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
            }
        });
    }
}

seq!(N in 0..=12 {
    impl_arg_list!(N);
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
}

/// Trait for types that can be used as an arguments list when calling Ruby
/// Procs.
pub trait RArrayArgList {
    /// Convert `self` into a type that can be used as a Ruby Proc argument
    /// list.
    fn into_array_arg_list_with(self, handle: &Ruby) -> RArray;
}

impl RArrayArgList for RArray {
    fn into_array_arg_list_with(self, _: &Ruby) -> RArray {
        self
    }
}

impl<T> RArrayArgList for T
where
    T: ArgList,
{
    fn into_array_arg_list_with(self, handle: &Ruby) -> RArray {
        handle.ary_new_from_values(self.into_arg_list_with(handle).as_ref())
    }
}

/// Trait for types that can be used as keyword arguments when calling Ruby
/// methods.
pub trait KwArgList {
    /// The specific Ruby value type.
    type Value: ReprValue;
    /// The type of the arguments list. Must convert to `&[Self::Value]` with
    /// [`AsRef`]
    type Output: AsRef<[Self::Value]>;

    /// Convert `self` into a type that can be used as a Ruby argument list.
    fn into_arg_list_with(self, handle: &Ruby) -> Self::Output;

    /// Whether the argument list contains keyword arguments. If true, the
    /// last element of the `&[Self::Value]` produced by
    /// `Self::into_arg_list_with` and [`AsRef`]
    fn contains_kw_args(&self) -> bool;

    fn kw_splat(&self) -> u32 {
        if self.contains_kw_args() {
            rb_sys::RB_PASS_KEYWORDS
        } else {
            rb_sys::RB_NO_KEYWORDS
        }
    }
}

impl KwArgList for RHash {
    type Value = RHash;
    type Output = [RHash; 1];

    fn into_arg_list_with(self, _: &Ruby) -> Self::Output {
        [self]
    }

    fn contains_kw_args(&self) -> bool {
        true
    }
}
