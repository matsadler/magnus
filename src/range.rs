//! Types for working with Ruby ranges.

use std::{
    fmt,
    ops::{
        Deref, Range as StdRange, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive,
    },
    os::raw::{c_int, c_long},
};

use rb_sys::{rb_range_beg_len, rb_range_new};

use crate::{
    class,
    error::{protect, Error},
    exception,
    object::Object,
    r_struct::RStruct,
    try_convert::TryConvert,
    value::{private, ReprValue, Value, QNIL},
};

/// Wrapper type for a Value known to be an instance of Ruby's Range class.
///
/// All [`Value`] methods should be available on this type through [`Deref`],
/// but some may be missed by this documentation.
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
            .filter(|_| val.is_kind_of(class::range()))
            .map(Self)
    }

    /// Create a new `Range`.
    ///
    /// Returns `Err` if `beg` and `end` are not comparable.
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
    pub fn new<T, U>(beg: T, end: U, excl: bool) -> Result<Self, Error>
    where
        T: Into<Value>,
        U: Into<Value>,
    {
        protect(|| unsafe {
            Self(RStruct::from_rb_value_unchecked(rb_range_new(
                beg.into().as_rb_value(),
                end.into().as_rb_value(),
                excl as c_int,
            )))
        })
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

impl Deref for Range {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.deref()
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

impl From<Range> for Value {
    fn from(val: Range) -> Self {
        *val
    }
}

impl<T> From<StdRange<T>> for Value
where
    T: Into<Value>,
{
    fn from(value: StdRange<T>) -> Self {
        *Range::new(value.start, value.end, true).unwrap()
    }
}

impl<T> From<RangeFrom<T>> for Value
where
    T: Into<Value>,
{
    fn from(value: RangeFrom<T>) -> Self {
        *Range::new(value.start, QNIL, false).unwrap()
    }
}

impl From<RangeFull> for Value {
    fn from(_: RangeFull) -> Self {
        *Range::new(QNIL, QNIL, false).unwrap()
    }
}

impl<T> From<RangeInclusive<T>> for Value
where
    T: Into<Value>,
{
    fn from(value: RangeInclusive<T>) -> Self {
        let (start, end) = value.into_inner();
        *Range::new(start, end, false).unwrap()
    }
}

impl<T> From<RangeTo<T>> for Value
where
    T: Into<Value>,
{
    fn from(value: RangeTo<T>) -> Self {
        *Range::new(QNIL, value.end, true).unwrap()
    }
}

impl<T> From<RangeToInclusive<T>> for Value
where
    T: Into<Value>,
{
    fn from(value: RangeToInclusive<T>) -> Self {
        *Range::new(QNIL, value.end, false).unwrap()
    }
}

impl Object for Range {}

unsafe impl private::ReprValue for Range {
    fn to_value(self) -> Value {
        *self
    }

    unsafe fn from_value_unchecked(val: Value) -> Self {
        Self(RStruct::from_value_unchecked(val))
    }
}

impl ReprValue for Range {}

impl TryConvert for Range {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Self::from_value(val).ok_or_else(|| {
            Error::new(
                exception::type_error(),
                format!("no implicit conversion of {} into Range", unsafe {
                    val.classname()
                },),
            )
        })
    }
}
