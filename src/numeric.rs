//! Types and Traits for working with Ruby’s Numeric class.

use std::fmt;

use rb_sys::{rb_num_coerce_bin, rb_num_coerce_bit, rb_num_coerce_cmp, rb_num_coerce_relop, VALUE};

use crate::{
    class,
    error::{protect, Error},
    exception,
    into_value::IntoValue,
    try_convert::TryConvert,
    value::{
        private::{self, ReprValue as _},
        IntoId, NonZeroValue, ReprValue, Value,
    },
    Ruby,
};

/// Functions available for all of Ruby's Numeric types.
pub trait Numeric: ReprValue + Copy {
    /// Apply the operator `op` with coercion.
    ///
    /// As Ruby's operators are implemented as methods, this function can be
    /// thought of as a specialised version of [`Value::funcall`], just for
    /// subclasses of `Numeric`, and that follows Ruby's coercion protocol.
    ///
    /// Returns `Ok(U)` if the method returns without error and the return
    /// value converts to a `U`, or returns Err if the method raises or the
    /// conversion fails.
    ///
    /// The returned errors are tailored for binary operators such as `+`, `/`,
    /// etc.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Integer, Numeric};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let a = Integer::from_i64(2);
    /// let b = Integer::from_i64(3);
    /// let c: i64 = a.coerce_bin(b, "+").unwrap();
    /// assert_eq!(c, 5);
    /// ```
    ///
    /// Avoiding type conversion of the result to demonstrate Ruby is coercing
    /// the types:
    ///
    /// ```
    /// use magnus::{Float, Integer, Numeric, Value};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let a = Integer::from_i64(2);
    /// let b = Float::from_f64(3.5);
    /// let c: Value = a.coerce_bin(b, "+").unwrap();
    /// let c = Float::from_value(c);
    /// assert!(c.is_some());
    /// assert_eq!(c.unwrap().to_f64(), 5.5);
    /// ```
    fn coerce_bin<T, ID, U>(self, other: T, op: ID) -> Result<U, Error>
    where
        T: Numeric,
        ID: IntoId,
        U: TryConvert,
    {
        let op = op.into_id_with(&Ruby::get_with(self));
        protect(|| unsafe {
            Value::new(rb_num_coerce_bin(
                self.as_rb_value(),
                other.as_rb_value(),
                op.as_rb_id(),
            ))
        })
        .and_then(TryConvert::try_convert)
    }

    /// Apply the operator `op` with coercion.
    ///
    /// As Ruby's operators are implemented as methods, this function can be
    /// thought of as a specialised version of [`Value::funcall`], just for
    /// subclasses of `Numeric`, and that follows Ruby's coercion protocol.
    ///
    /// Returns `Ok(U)` if the method returns without error and the return
    /// value converts to a `U`, or returns Err if the method raises or the
    /// conversion fails.
    ///
    /// The returned errors are tailored for comparison operators such as `<=>`.
    ///
    /// Note, if coercion fails this will return `nil`, if you want to detect
    /// this you should set the result type to `Option<U>`. Other errors in
    /// applying `op` will still result in an `Err`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::num::NonZeroI64;
    /// use magnus::{Float, Numeric, RRational};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let a = RRational::new(1, NonZeroI64::new(4).unwrap());
    /// let b = Float::from_f64(0.3);
    /// let result: i64 = a.coerce_cmp(b, "<=>").unwrap();
    /// assert_eq!(result, -1);
    /// ```
    fn coerce_cmp<T, ID, U>(self, other: T, op: ID) -> Result<U, Error>
    where
        T: Numeric,
        ID: IntoId,
        U: TryConvert,
    {
        let op = op.into_id_with(&Ruby::get_with(self));
        protect(|| unsafe {
            Value::new(rb_num_coerce_cmp(
                self.as_rb_value(),
                other.as_rb_value(),
                op.as_rb_id(),
            ))
        })
        .and_then(TryConvert::try_convert)
    }

    /// Apply the operator `op` with coercion.
    ///
    /// As Ruby's operators are implemented as methods, this function can be
    /// thought of as a specialised version of [`Value::funcall`], just for
    /// subclasses of `Numeric`, and that follows Ruby's coercion protocol.
    ///
    /// Returns `Ok(U)` if the method returns without error and the return
    /// value converts to a `U`, or returns Err if the method raises or the
    /// conversion fails.
    ///
    /// The returned errors are tailored for relationship operators such as
    /// `<=`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::num::NonZeroI64;
    /// use magnus::{Float, Numeric, RRational};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let a = Float::from_f64(0.3);
    /// let b = RRational::new(1, NonZeroI64::new(4).unwrap());
    /// let result: bool = a.coerce_cmp(b, "<=").unwrap();
    /// assert_eq!(result, false);
    /// ```
    fn coerce_relop<T, ID, U>(self, other: T, op: ID) -> Result<U, Error>
    where
        T: Numeric,
        ID: IntoId,
        U: TryConvert,
    {
        let op = op.into_id_with(&Ruby::get_with(self));
        protect(|| unsafe {
            Value::new(rb_num_coerce_relop(
                self.as_rb_value(),
                other.as_rb_value(),
                op.as_rb_id(),
            ))
        })
        .and_then(TryConvert::try_convert)
    }

    /// Apply the operator `op` with coercion.
    ///
    /// As Ruby's operators are implemented as methods, this function can be
    /// thought of as a specialised version of [`Value::funcall`], just for
    /// subclasses of `Numeric`, and that follows Ruby's coercion protocol.
    ///
    /// Returns `Ok(U)` if the method returns without error and the return
    /// value converts to a `U`, or returns Err if the method raises or the
    /// conversion fails.
    ///
    /// The returned errors are tailored for bitwise operators such as `|`,
    /// `^`, etc.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::num::NonZeroI64;
    /// use magnus::{Integer, Numeric};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let a = Integer::from_i64(0b00000011);
    /// let b = Integer::from_i64(0b00001110);
    /// let result: i64 = a.coerce_cmp(b, "^").unwrap();
    /// assert_eq!(result, 0b00001101);
    /// ```
    fn coerce_bit<T, ID, U>(self, other: T, op: ID) -> Result<U, Error>
    where
        T: Numeric,
        ID: IntoId,
        U: TryConvert,
    {
        let op = op.into_id_with(&Ruby::get_with(self));
        protect(|| unsafe {
            Value::new(rb_num_coerce_bit(
                self.as_rb_value(),
                other.as_rb_value(),
                op.as_rb_id(),
            ))
        })
        .and_then(TryConvert::try_convert)
    }
}

/// Wrapper type for a Value known to be an instance of Ruby’s Numeric class.
///
/// See the [`ReprValue`] trait for additional methods available on this type.
///
/// # Examples
///
/// ```
/// use std::num::NonZeroI64;
/// use magnus::{prelude::*, numeric::NumericValue, Integer, Float, RRational};
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// let a = Integer::from_i64(1);
/// let b = RRational::new(1, NonZeroI64::new(2).unwrap());
/// let c = Float::from_f64(0.3);
/// let d = Integer::from_i64(4);
///
/// let result: NumericValue = a.coerce_bin(b, "+").unwrap();
/// let result: NumericValue = result.coerce_bin(c, "+").unwrap();
/// let result: NumericValue = result.coerce_bin(d, "+").unwrap();
/// assert_eq!(f64::try_convert(result.as_value()).unwrap(), 5.8);
/// ```
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct NumericValue(NonZeroValue);

impl NumericValue {
    #[inline]
    unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        Self(NonZeroValue::new_unchecked(Value::new(val)))
    }
}

impl fmt::Display for NumericValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for NumericValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl IntoValue for NumericValue {
    fn into_value_with(self, _: &Ruby) -> Value {
        self.0.get()
    }
}

unsafe impl private::ReprValue for NumericValue {}

impl Numeric for NumericValue {}

impl ReprValue for NumericValue {}

impl TryConvert for NumericValue {
    fn try_convert(val: Value) -> Result<Self, Error> {
        val.is_kind_of(class::numeric())
            .then(|| unsafe { Self::from_rb_value_unchecked(val.as_rb_value()) })
            .ok_or_else(|| {
                Error::new(
                    exception::type_error(),
                    format!("no implicit conversion of {} into Numeric", unsafe {
                        val.classname()
                    },),
                )
            })
    }
}
