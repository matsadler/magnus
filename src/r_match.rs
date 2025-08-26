use std::{fmt, os::raw::c_int};

use rb_sys::{
    VALUE, rb_reg_backref_number, rb_reg_last_match, rb_reg_match_last, rb_reg_match_post,
    rb_reg_match_pre, rb_reg_nth_defined, rb_reg_nth_match, ruby_value_type,
};

use crate::{
    Ruby,
    error::{Error, protect},
    into_value::IntoValue,
    object::Object,
    r_string::{IntoRString, RString},
    try_convert::TryConvert,
    value::{
        NonZeroValue, ReprValue, Value,
        private::{self, ReprValue as _},
    },
};

/// A Value pointer to a RMatch struct, Ruby's internal representation of the
/// MatchData returned from a regex match.
///
/// See the [`ReprValue`] and [`Object`] traits for additional methods
/// available on this type.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RMatch(NonZeroValue);

impl RMatch {
    /// Return `Some(RMatch)` if `val` is a `RMatch`, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{RMatch, eval};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(RMatch::from_value(eval(r#""foo".match(/o/)"#).unwrap()).is_some());
    /// assert!(RMatch::from_value(eval(r#""o""#).unwrap()).is_none());
    /// ```
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            (val.rb_type() == ruby_value_type::RUBY_T_MATCH)
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        unsafe { Self(NonZeroValue::new_unchecked(Value::new(val))) }
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
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let regexp = ruby.reg_new(".([a-z])([a-z]*)([0-9])?", Default::default())?;
    ///     regexp.reg_match("ex")?;
    ///     let match_data = ruby.backref_get().unwrap();
    ///     // 0th group is the whole match
    ///     assert_eq!(match_data.nth_defined(0), Some(true));
    ///     // the `([a-z])` group
    ///     assert_eq!(match_data.nth_defined(1), Some(true));
    ///     // the `([a-z]*)` group
    ///     assert_eq!(match_data.nth_defined(2), Some(true));
    ///     // the `([0-9])?` group
    ///     assert_eq!(match_data.nth_defined(3), Some(false));
    ///     // no 4th group
    ///     assert_eq!(match_data.nth_defined(4), None);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn nth_defined(self, n: isize) -> Option<bool> {
        let value = unsafe { Value::new(rb_reg_nth_defined(n as c_int, self.as_rb_value())) };
        Option::<bool>::try_convert(value).unwrap() // infallible
    }

    /// Returns the string captured by the `n`th capture group.
    ///
    /// Returns `None` when there is no `n`th capture.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let regexp = ruby.reg_new(".([a-z])([a-z]*)([0-9])?", Default::default())?;
    ///     regexp.reg_match("ex")?;
    ///     let match_data = ruby.backref_get().unwrap();
    ///     // 0th group is the whole match
    ///     assert_eq!(
    ///         match_data.nth_match(0).map(|s| s.to_string().unwrap()),
    ///         Some(String::from("ex"))
    ///     );
    ///     // the `([a-z])` group
    ///     assert_eq!(
    ///         match_data.nth_match(1).map(|s| s.to_string().unwrap()),
    ///         Some(String::from("x"))
    ///     );
    ///     // the `([a-z]*)` group
    ///     assert_eq!(
    ///         match_data.nth_match(2).map(|s| s.to_string().unwrap()),
    ///         Some(String::from(""))
    ///     );
    ///     // the `([0-9])?` group
    ///     assert_eq!(
    ///         match_data.nth_match(3).map(|s| s.to_string().unwrap()),
    ///         None
    ///     );
    ///     // no 4th group
    ///     assert_eq!(
    ///         match_data.nth_match(4).map(|s| s.to_string().unwrap()),
    ///         None
    ///     );
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
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
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let regexp = ruby.reg_new("Hello, (?<subject>.*)!", Default::default())?;
    ///     regexp.reg_match("Hello, World!")?;
    ///     let match_data = ruby.backref_get().unwrap();
    ///     assert_eq!(match_data.backref_number("subject")?, 1);
    ///     assert!(match_data.backref_number("foo").is_err());
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn backref_number<T>(self, name: T) -> Result<usize, Error>
    where
        T: IntoRString,
    {
        let handle = Ruby::get_with(self);
        let name = name.into_r_string_with(&handle);
        let mut n = 0;
        protect(|| unsafe {
            n = rb_reg_backref_number(self.as_rb_value(), name.as_rb_value()) as usize;
            handle.qnil()
        })?;
        Ok(n)
    }

    /// Returns the string matched.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let regexp = ruby.reg_new("b(.)r", Default::default())?;
    ///     regexp.reg_match("foo bar baz")?;
    ///
    ///     let match_data = ruby.backref_get().unwrap();
    ///     assert_eq!(match_data.matched().to_string()?, "bar");
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn matched(self) -> RString {
        unsafe { RString::from_rb_value_unchecked(rb_reg_last_match(self.as_rb_value())) }
    }

    /// Returns the string before the segment matched.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let regexp = ruby.reg_new("b(.)r", Default::default())?;
    ///     regexp.reg_match("foo bar baz")?;
    ///
    ///     let match_data = ruby.backref_get().unwrap();
    ///     assert_eq!(match_data.pre().to_string()?, "foo ");
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn pre(self) -> RString {
        unsafe { RString::from_rb_value_unchecked(rb_reg_match_pre(self.as_rb_value())) }
    }

    /// Returns the string after the segment matched.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let regexp = ruby.reg_new("b(.)r", Default::default())?;
    ///     regexp.reg_match("foo bar baz")?;
    ///
    ///     let match_data = ruby.backref_get().unwrap();
    ///     assert_eq!(match_data.post().to_string()?, " baz");
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
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
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let regexp = ruby.reg_new("(.)oo b(.)r ba(.)", Default::default())?;
    ///     regexp.reg_match("foo bar baz")?;
    ///
    ///     let match_data = ruby.backref_get().unwrap();
    ///     assert_eq!(match_data.last().unwrap().to_string()?, "z");
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn last(self) -> Option<RString> {
        let value = unsafe { Value::new(rb_reg_match_last(self.as_rb_value())) };
        (!value.is_nil()).then(|| unsafe { RString::from_rb_value_unchecked(value.as_rb_value()) })
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
    #[inline]
    fn into_value_with(self, _: &Ruby) -> Value {
        self.0.get()
    }
}

impl Object for RMatch {}

unsafe impl private::ReprValue for RMatch {}

impl ReprValue for RMatch {}

impl TryConvert for RMatch {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Self::from_value(val).ok_or_else(|| {
            Error::new(
                Ruby::get_with(val).exception_type_error(),
                format!("no implicit conversion of {} into MatchData", unsafe {
                    val.classname()
                },),
            )
        })
    }
}
