use crate::{r_array::RArray, value::Value, Ruby};

#[allow(missing_docs)]
impl Ruby {
    #[allow(clippy::wrong_self_convention)]
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
    /// Panics if called from a non-Ruby thread.
    ///
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
    /// The type of the arguments list. Must convert to `&[Value]` with
    /// [`AsRef`].
    type Output: AsRef<[Value]>;

    /// Convert `self` into a type that can be used as a Ruby argument list.
    fn into_arg_list_with(self, handle: &Ruby) -> Self::Output;
}

/// # Safety
///
/// The implmentation of `ArgList` for slices is not intended to suggest that
/// it is valid to build a `Vec` of Ruby values to then convert to a slice.
/// [Ruby values should never be put into a `Vec`](crate#safety).
impl<'a> ArgList for &'a [Value] {
    type Output = &'a [Value];

    fn into_arg_list_with(self, _: &Ruby) -> Self::Output {
        self
    }
}

impl ArgList for () {
    type Output = [Value; 0];

    fn into_arg_list_with(self, _: &Ruby) -> Self::Output {
        []
    }
}

impl<A> ArgList for (A,)
where
    A: IntoValue,
{
    type Output = [Value; 1];

    fn into_arg_list_with(self, handle: &Ruby) -> Self::Output {
        [handle.into_value(self.0)]
    }
}

impl<A, B> ArgList for (A, B)
where
    A: IntoValue,
    B: IntoValue,
{
    type Output = [Value; 2];

    fn into_arg_list_with(self, handle: &Ruby) -> Self::Output {
        [handle.into_value(self.0), handle.into_value(self.1)]
    }
}

impl<A, B, C> ArgList for (A, B, C)
where
    A: IntoValue,
    B: IntoValue,
    C: IntoValue,
{
    type Output = [Value; 3];

    fn into_arg_list_with(self, handle: &Ruby) -> Self::Output {
        [
            handle.into_value(self.0),
            handle.into_value(self.1),
            handle.into_value(self.2),
        ]
    }
}

impl<A, B, C, D> ArgList for (A, B, C, D)
where
    A: IntoValue,
    B: IntoValue,
    C: IntoValue,
    D: IntoValue,
{
    type Output = [Value; 4];

    fn into_arg_list_with(self, handle: &Ruby) -> Self::Output {
        [
            handle.into_value(self.0),
            handle.into_value(self.1),
            handle.into_value(self.2),
            handle.into_value(self.3),
        ]
    }
}

impl<A, B, C, D, E> ArgList for (A, B, C, D, E)
where
    A: IntoValue,
    B: IntoValue,
    C: IntoValue,
    D: IntoValue,
    E: IntoValue,
{
    type Output = [Value; 5];

    fn into_arg_list_with(self, handle: &Ruby) -> Self::Output {
        [
            handle.into_value(self.0),
            handle.into_value(self.1),
            handle.into_value(self.2),
            handle.into_value(self.3),
            handle.into_value(self.4),
        ]
    }
}

impl<A, B, C, D, E, F> ArgList for (A, B, C, D, E, F)
where
    A: IntoValue,
    B: IntoValue,
    C: IntoValue,
    D: IntoValue,
    E: IntoValue,
    F: IntoValue,
{
    type Output = [Value; 6];

    fn into_arg_list_with(self, handle: &Ruby) -> Self::Output {
        [
            handle.into_value(self.0),
            handle.into_value(self.1),
            handle.into_value(self.2),
            handle.into_value(self.3),
            handle.into_value(self.4),
            handle.into_value(self.5),
        ]
    }
}

impl<A, B, C, D, E, F, G> ArgList for (A, B, C, D, E, F, G)
where
    A: IntoValue,
    B: IntoValue,
    C: IntoValue,
    D: IntoValue,
    E: IntoValue,
    F: IntoValue,
    G: IntoValue,
{
    type Output = [Value; 7];

    fn into_arg_list_with(self, handle: &Ruby) -> Self::Output {
        [
            handle.into_value(self.0),
            handle.into_value(self.1),
            handle.into_value(self.2),
            handle.into_value(self.3),
            handle.into_value(self.4),
            handle.into_value(self.5),
            handle.into_value(self.6),
        ]
    }
}

impl<A, B, C, D, E, F, G, H> ArgList for (A, B, C, D, E, F, G, H)
where
    A: IntoValue,
    B: IntoValue,
    C: IntoValue,
    D: IntoValue,
    E: IntoValue,
    F: IntoValue,
    G: IntoValue,
    H: IntoValue,
{
    type Output = [Value; 8];

    fn into_arg_list_with(self, handle: &Ruby) -> Self::Output {
        [
            handle.into_value(self.0),
            handle.into_value(self.1),
            handle.into_value(self.2),
            handle.into_value(self.3),
            handle.into_value(self.4),
            handle.into_value(self.5),
            handle.into_value(self.6),
            handle.into_value(self.7),
        ]
    }
}

impl<A, B, C, D, E, F, G, H, I> ArgList for (A, B, C, D, E, F, G, H, I)
where
    A: IntoValue,
    B: IntoValue,
    C: IntoValue,
    D: IntoValue,
    E: IntoValue,
    F: IntoValue,
    G: IntoValue,
    H: IntoValue,
    I: IntoValue,
{
    type Output = [Value; 9];

    fn into_arg_list_with(self, handle: &Ruby) -> Self::Output {
        [
            handle.into_value(self.0),
            handle.into_value(self.1),
            handle.into_value(self.2),
            handle.into_value(self.3),
            handle.into_value(self.4),
            handle.into_value(self.5),
            handle.into_value(self.6),
            handle.into_value(self.7),
            handle.into_value(self.8),
        ]
    }
}

impl<A, B, C, D, E, F, G, H, I, J> ArgList for (A, B, C, D, E, F, G, H, I, J)
where
    A: IntoValue,
    B: IntoValue,
    C: IntoValue,
    D: IntoValue,
    E: IntoValue,
    F: IntoValue,
    G: IntoValue,
    H: IntoValue,
    I: IntoValue,
    J: IntoValue,
{
    type Output = [Value; 10];

    fn into_arg_list_with(self, handle: &Ruby) -> Self::Output {
        [
            handle.into_value(self.0),
            handle.into_value(self.1),
            handle.into_value(self.2),
            handle.into_value(self.3),
            handle.into_value(self.4),
            handle.into_value(self.5),
            handle.into_value(self.6),
            handle.into_value(self.7),
            handle.into_value(self.8),
            handle.into_value(self.9),
        ]
    }
}

impl<A, B, C, D, E, F, G, H, I, J, K> ArgList for (A, B, C, D, E, F, G, H, I, J, K)
where
    A: IntoValue,
    B: IntoValue,
    C: IntoValue,
    D: IntoValue,
    E: IntoValue,
    F: IntoValue,
    G: IntoValue,
    H: IntoValue,
    I: IntoValue,
    J: IntoValue,
    K: IntoValue,
{
    type Output = [Value; 11];

    fn into_arg_list_with(self, handle: &Ruby) -> Self::Output {
        [
            handle.into_value(self.0),
            handle.into_value(self.1),
            handle.into_value(self.2),
            handle.into_value(self.3),
            handle.into_value(self.4),
            handle.into_value(self.5),
            handle.into_value(self.6),
            handle.into_value(self.7),
            handle.into_value(self.8),
            handle.into_value(self.9),
            handle.into_value(self.10),
        ]
    }
}

impl<A, B, C, D, E, F, G, H, I, J, K, L> ArgList for (A, B, C, D, E, F, G, H, I, J, K, L)
where
    A: IntoValue,
    B: IntoValue,
    C: IntoValue,
    D: IntoValue,
    E: IntoValue,
    F: IntoValue,
    G: IntoValue,
    H: IntoValue,
    I: IntoValue,
    J: IntoValue,
    K: IntoValue,
    L: IntoValue,
{
    type Output = [Value; 12];

    fn into_arg_list_with(self, handle: &Ruby) -> Self::Output {
        [
            handle.into_value(self.0),
            handle.into_value(self.1),
            handle.into_value(self.2),
            handle.into_value(self.3),
            handle.into_value(self.4),
            handle.into_value(self.5),
            handle.into_value(self.6),
            handle.into_value(self.7),
            handle.into_value(self.8),
            handle.into_value(self.9),
            handle.into_value(self.10),
            handle.into_value(self.11),
        ]
    }
}

impl<const N: usize> ArgList for [Value; N] {
    type Output = [Value; N];

    fn into_arg_list_with(self, _: &Ruby) -> Self::Output {
        self
    }
}

pub trait RArrayArgList {
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
