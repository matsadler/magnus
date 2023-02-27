//! Types for working with Ruby ranges.

use std::{
    fmt,
    ops::{Range as StdRange, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive},
    os::raw::{c_int, c_long},
};

use rb_sys::{rb_range_beg_len, rb_range_new};

use crate::{
    error::{protect, Error},
    into_value::{IntoValue, IntoValueFromNative},
    object::Object,
    r_struct::RStruct,
    try_convert::TryConvert,
    value::{
        private::{self, ReprValue as _},
        ReprValue, Value,
    },
    Ruby,
};

impl Ruby {
    pub fn range_new<T, U>(&self, beg: T, end: U, excl: bool) -> Result<Range, Error>
    where
        T: IntoValue,
        U: IntoValue,
    {
        protect(|| unsafe {
            Range(RStruct::from_rb_value_unchecked(rb_range_new(
                self.into_value(beg).as_rb_value(),
                self.into_value(end).as_rb_value(),
                excl as c_int,
            )))
        })
    }
}

/// Wrapper type for a Value known to be an instance of Ruby's Range class.
///
/// See the [`ReprValue`] and [`Object`] traits for additional methods
/// available on this type.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Range(RStruct);

impl Range {
    /// Return `Some(Range)` if `val` is an `Range`, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::eval;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(magnus::Range::from_value(eval("2..7").unwrap()).is_some());
    /// assert!(magnus::Range::from_value(eval("1").unwrap()).is_none());
    /// ```
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        RStruct::from_value(val)
            .filter(|_| val.is_kind_of(Ruby::get_with(val).class_range()))
            .map(Self)
    }

    /// Create a new `Range`.
    ///
    /// Returns `Err` if `beg` and `end` are not comparable.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::eval;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let range = magnus::Range::new(2, 7, false).unwrap();
    /// let res: bool = eval!("range == (2..7)", range).unwrap();
    /// assert!(res);
    /// ```
    ///
    /// ```
    /// use magnus::eval;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let range = magnus::Range::new(2, 7, true).unwrap();
    /// let res: bool = eval!("range == (2...7)", range).unwrap();
    /// assert!(res);
    /// ```
    #[inline]
    pub fn new<T, U>(beg: T, end: U, excl: bool) -> Result<Self, Error>
    where
        T: IntoValue,
        U: IntoValue,
    {
        get_ruby!().range_new(beg, end, excl)
    }

    /// Return the value that defines the beginning of the range, converting it
    /// to a `T`.
    ///
    /// Errors if the conversion fails.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::eval;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let range = eval::<magnus::Range>("2..7").unwrap();
    /// assert_eq!(range.beg::<i64>().unwrap(), 2);
    /// ```
    pub fn beg<T>(self) -> Result<T, Error>
    where
        T: TryConvert,
    {
        self.0.get(0)
    }

    /// Return the value that defines the end of the range, converting it
    /// to a `T`.
    ///
    /// Errors if the conversion fails.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::eval;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let range = eval::<magnus::Range>("2..7").unwrap();
    /// assert_eq!(range.end::<i64>().unwrap(), 7);
    /// ```
    pub fn end<T>(self) -> Result<T, Error>
    where
        T: TryConvert,
    {
        self.0.get(1)
    }

    /// Returns `true` if the range excludes its end value, `false` if the end
    /// value is included.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::eval;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let range = eval::<magnus::Range>("2..7").unwrap();
    /// assert_eq!(range.excl(), false);
    /// ```
    pub fn excl(self) -> bool {
        self.0.get::<Value>(2).unwrap().to_bool()
    }

    /// Given a total `length`, returns a beginning index and length of the
    /// range within that total length.
    ///
    /// Returns `Err` if `self` is a non-numerical range, or the range is out
    /// of range for `length`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::eval;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let range = eval::<magnus::Range>("2..").unwrap();
    /// assert_eq!(range.beg_len(10).unwrap(), (2, 8));
    /// ```
    ///
    /// ```
    /// use magnus::eval;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// # #[cfg(ruby_gte_2_7)]
    /// let range = eval::<magnus::Range>("..7").unwrap();
    /// # #[cfg(ruby_gte_2_7)]
    /// assert_eq!(range.beg_len(10).unwrap(), (0, 8));
    /// ```
    ///
    /// ```
    /// use magnus::eval;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let range = eval::<magnus::Range>("-3..-1").unwrap();
    /// assert_eq!(range.beg_len(10).unwrap(), (7, 3));
    /// ```
    pub fn beg_len(self, length: usize) -> Result<(usize, usize), Error> {
        let mut begp: c_long = 0;
        let mut lenp: c_long = 0;
        protect(|| unsafe {
            Value::new(rb_range_beg_len(
                self.as_rb_value(),
                &mut begp as *mut _,
                &mut lenp as *mut _,
                length as c_long,
                1,
            ))
        })?;
        Ok((begp as usize, lenp as usize))
    }

    /// Given a total `length`, converts the Ruby `Range` to a Rust
    /// [`std::ops::Range`].
    ///
    /// `length` is required to account for Ruby conventions such as a range
    /// from `-2..-1` returning the end of a collection.
    ///
    /// Returns `Err` if `self` is a non-numerical range, or the range is out
    /// of range for `length`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::eval;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// // Ruby's .. range is inclusive
    /// let range = eval::<magnus::Range>("2..7").unwrap();
    /// // Rust's .. range in exclusive
    /// assert_eq!(range.to_range_with_len(10).unwrap(), 2..8);
    /// ```
    ///
    /// ```
    /// use magnus::eval;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let range = eval::<magnus::Range>("2..").unwrap();
    /// assert_eq!(range.to_range_with_len(10).unwrap(), 2..10);
    /// ```
    ///
    /// ```
    /// use magnus::eval;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// # #[cfg(ruby_gte_2_7)]
    /// let range = eval::<magnus::Range>("..7").unwrap();
    /// # #[cfg(ruby_gte_2_7)]
    /// assert_eq!(range.to_range_with_len(10).unwrap(), 0..8);
    /// ```
    ///
    /// ```
    /// use magnus::eval;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let range = eval::<magnus::Range>("-3..-1").unwrap();
    /// assert_eq!(range.to_range_with_len(10).unwrap(), 7..10);
    /// ```
    pub fn to_range_with_len(self, length: usize) -> Result<StdRange<usize>, Error> {
        let (beg, len) = self.beg_len(length)?;
        Ok(beg..(beg + len))
    }
}

impl fmt::Display for Range {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for Range {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl IntoValue for Range {
    fn into_value_with(self, handle: &Ruby) -> Value {
        self.0.into_value_with(handle)
    }
}

impl<T> IntoValue for StdRange<T>
where
    T: IntoValue,
{
    fn into_value_with(self, handle: &Ruby) -> Value {
        handle
            .range_new(self.start, self.end, true)
            .unwrap()
            .into_value_with(handle)
    }
}

unsafe impl<T> IntoValueFromNative for StdRange<T> where T: IntoValueFromNative {}

impl<T> IntoValue for RangeFrom<T>
where
    T: IntoValue,
{
    fn into_value_with(self, handle: &Ruby) -> Value {
        handle
            .range_new(self.start, handle.qnil(), false)
            .unwrap()
            .into_value_with(handle)
    }
}

unsafe impl<T> IntoValueFromNative for RangeFrom<T> where T: IntoValueFromNative {}

impl IntoValue for RangeFull {
    fn into_value_with(self, handle: &Ruby) -> Value {
        handle
            .range_new(handle.qnil(), handle.qnil(), false)
            .unwrap()
            .into_value_with(handle)
    }
}

unsafe impl IntoValueFromNative for RangeFull {}

impl<T> IntoValue for RangeInclusive<T>
where
    T: IntoValue,
{
    fn into_value_with(self, handle: &Ruby) -> Value {
        let (start, end) = self.into_inner();
        handle
            .range_new(start, end, false)
            .unwrap()
            .into_value_with(handle)
    }
}

unsafe impl<T> IntoValueFromNative for RangeInclusive<T> where T: IntoValueFromNative {}

impl<T> IntoValue for RangeTo<T>
where
    T: IntoValue,
{
    fn into_value_with(self, handle: &Ruby) -> Value {
        handle
            .range_new(handle.qnil(), self.end, true)
            .unwrap()
            .into_value_with(handle)
    }
}

unsafe impl<T> IntoValueFromNative for RangeTo<T> where T: IntoValueFromNative {}

impl<T> IntoValue for RangeToInclusive<T>
where
    T: IntoValue,
{
    fn into_value_with(self, handle: &Ruby) -> Value {
        handle
            .range_new(handle.qnil(), self.end, false)
            .unwrap()
            .into_value_with(handle)
    }
}

unsafe impl<T> IntoValueFromNative for RangeToInclusive<T> where T: IntoValueFromNative {}

impl Object for Range {}

unsafe impl private::ReprValue for Range {}

impl ReprValue for Range {}

impl TryConvert for Range {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Self::from_value(val).ok_or_else(|| {
            Error::new(
                Ruby::get_with(val).exception_type_error(),
                format!("no implicit conversion of {} into Range", unsafe {
                    val.classname()
                },),
            )
        })
    }
}
