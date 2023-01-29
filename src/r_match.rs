use std::{fmt, ops::Deref, os::raw::c_int};

use rb_sys::{
    rb_reg_backref_number, rb_reg_last_match, rb_reg_match_last, rb_reg_match_post,
    rb_reg_match_pre, rb_reg_nth_defined, rb_reg_nth_match, ruby_value_type, VALUE,
};

use crate::{
    error::{protect, Error},
    exception,
    into_value::IntoValue,
    object::Object,
    r_string::{IntoRString, RString},
    ruby_handle::RubyHandle,
    try_convert::TryConvert,
    value::{private, NonZeroValue, ReprValue, Value, QNIL},
};

/// A Value pointer to a RMatch struct, Ruby's internal representation of the
/// MatchData returned from a regex match.
///
/// All [`Value`] methods should be available on this type through [`Deref`],
/// but some may be missed by this documentation.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RMatch(NonZeroValue);

impl RMatch {
    /// Return `Some(RMatch)` if `val` is a `RMatch`, `None` otherwise.
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            (val.rb_type() == ruby_value_type::RUBY_T_MATCH)
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        Self(NonZeroValue::new_unchecked(Value::new(val)))
    }

    /// Returns whether the `n`th capture group is set.
    ///
    /// Returns `Some(true)` when there is an `n`th capture and it has a value.
    /// Returns `Some(false)` when there is an `n`th capture but it is empty.
    /// Returns `None` when there is no `n`th capture.
    ///
    /// This function is similar to [`nth_match`](Self::nth_match), but can be
    /// used to avoid allocating a Ruby string if the value of the capture is
    /// not needed.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{backref_get, RRegexp};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let regexp = RRegexp::new(".([a-z])([a-z]*)([0-9])?", Default::default()).unwrap();
    /// regexp.reg_match("ex").unwrap();
    /// let match_data = backref_get().unwrap();
    /// // 0th group is the whole match
    /// assert_eq!(match_data.nth_defined(0), Some(true));
    /// // the `([a-z])` group
    /// assert_eq!(match_data.nth_defined(1), Some(true));
    /// // the `([a-z]*)` group
    /// assert_eq!(match_data.nth_defined(2), Some(true));
    /// // the `([0-9])?` group
    /// assert_eq!(match_data.nth_defined(3), Some(false));
    /// // no 4th group
    /// assert_eq!(match_data.nth_defined(4), None);
    /// ```
    pub fn nth_defined(self, n: isize) -> Option<bool> {
        let value = unsafe { Value::new(rb_reg_nth_defined(n as c_int, self.as_rb_value())) };
        value.try_convert().unwrap() // conversion to Option<bool> is infallible
    }

    /// Returns the string captured by the `n`th capture group.
    ///
    /// Returns `None` when there is no `n`th capture.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{backref_get, RRegexp};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let regexp = RRegexp::new(".([a-z])([a-z]*)([0-9])?", Default::default()).unwrap();
    /// regexp.reg_match("ex").unwrap();
    /// let match_data = backref_get().unwrap();
    /// // 0th group is the whole match
    /// assert_eq!(match_data.nth_match(0).map(|s| s.to_string().unwrap()), Some(String::from("ex")));
    /// // the `([a-z])` group
    /// assert_eq!(match_data.nth_match(1).map(|s| s.to_string().unwrap()), Some(String::from("x")));
    /// // the `([a-z]*)` group
    /// assert_eq!(match_data.nth_match(2).map(|s| s.to_string().unwrap()), Some(String::from("")));
    /// // the `([0-9])?` group
    /// assert_eq!(match_data.nth_match(3).map(|s| s.to_string().unwrap()), None);
    /// // no 4th group
    /// assert_eq!(match_data.nth_match(4).map(|s| s.to_string().unwrap()), None);
    /// ```
    pub fn nth_match(self, n: isize) -> Option<RString> {
        let value = unsafe { Value::new(rb_reg_nth_match(n as c_int, self.as_rb_value())) };
        (!value.is_nil()).then(|| unsafe { RString::from_rb_value_unchecked(value.as_rb_value()) })
    }

    /// Returns the index for the named capture group.
    ///
    /// Returns `Err` if there's is no named capture group with the given name.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{backref_get, RRegexp};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let regexp = RRegexp::new("Hello, (?<subject>.*)!", Default::default()).unwrap();
    /// regexp.reg_match("Hello, World!").unwrap();
    /// let match_data = backref_get().unwrap();
    /// assert_eq!(match_data.backref_number("subject").unwrap(), 1);
    /// assert!(match_data.backref_number("foo").is_err());
    /// ```
    pub fn backref_number<T>(self, name: T) -> Result<usize, Error>
    where
        T: IntoRString,
    {
        let name = name.into_r_string();
        let mut n = 0;
        protect(|| {
            n = unsafe { rb_reg_backref_number(self.as_rb_value(), name.as_rb_value()) as usize };
            QNIL
        })?;
        Ok(n)
    }

    /// Returns the string matched.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{backref_get, RRegexp};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let regexp = RRegexp::new("b(.)r", Default::default()).unwrap();
    /// regexp.reg_match("foo bar baz").unwrap();
    ///
    /// let match_data = backref_get().unwrap();
    /// assert_eq!(match_data.matched().to_string().unwrap(), "bar");
    /// ```
    pub fn matched(self) -> RString {
        unsafe { RString::from_rb_value_unchecked(rb_reg_last_match(self.as_rb_value())) }
    }

    /// Returns the string before the segment matched.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{backref_get, RRegexp};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let regexp = RRegexp::new("b(.)r", Default::default()).unwrap();
    /// regexp.reg_match("foo bar baz").unwrap();
    ///
    /// let match_data = backref_get().unwrap();
    /// assert_eq!(match_data.pre().to_string().unwrap(), "foo ");
    /// ```
    pub fn pre(self) -> RString {
        unsafe { RString::from_rb_value_unchecked(rb_reg_match_pre(self.as_rb_value())) }
    }

    /// Returns the string after the segment matched.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{backref_get, RRegexp};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let regexp = RRegexp::new("b(.)r", Default::default()).unwrap();
    /// regexp.reg_match("foo bar baz").unwrap();
    ///
    /// let match_data = backref_get().unwrap();
    /// assert_eq!(match_data.post().to_string().unwrap(), " baz");
    /// ```
    pub fn post(self) -> RString {
        unsafe { RString::from_rb_value_unchecked(rb_reg_match_post(self.as_rb_value())) }
    }

    /// Returns the last capture.
    ///
    /// Returns `None` if there are no capture groups.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{backref_get, RRegexp};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let regexp = RRegexp::new("(.)oo b(.)r ba(.)", Default::default()).unwrap();
    /// regexp.reg_match("foo bar baz").unwrap();
    ///
    /// let match_data = backref_get().unwrap();
    /// assert_eq!(match_data.last().unwrap().to_string().unwrap(), "z");
    /// ```
    pub fn last(self) -> Option<RString> {
        let value = unsafe { Value::new(rb_reg_match_last(self.as_rb_value())) };
        (!value.is_nil()).then(|| unsafe { RString::from_rb_value_unchecked(value.as_rb_value()) })
    }
}

impl Deref for RMatch {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
    }
}

impl fmt::Display for RMatch {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for RMatch {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl IntoValue for RMatch {
    fn into_value_with(self, _: &RubyHandle) -> Value {
        *self
    }
}

impl From<RMatch> for Value {
    fn from(val: RMatch) -> Self {
        *val
    }
}

impl Object for RMatch {}

unsafe impl private::ReprValue for RMatch {
    fn to_value(self) -> Value {
        *self
    }

    unsafe fn from_value_unchecked(val: Value) -> Self {
        Self(NonZeroValue::new_unchecked(val))
    }
}

impl ReprValue for RMatch {}

impl TryConvert for RMatch {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Self::from_value(val).ok_or_else(|| {
            Error::new(
                exception::type_error(),
                format!("no implicit conversion of {} into MatchData", unsafe {
                    val.classname()
                },),
            )
        })
    }
}
