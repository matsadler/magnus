//! Types for working with Ruby’s Regexp class.

use std::{
    fmt,
    ops::Deref,
    os::raw::{c_char, c_int, c_long, c_uint},
};

use rb_sys::{rb_enc_reg_new, rb_reg_new_str, ruby_value_type, VALUE};

use crate::{
    encoding::{EncodingCapable, RbEncoding},
    error::{protect, Error},
    exception,
    try_convert::TryConvert,
    value::{private, NonZeroValue, ReprValue, Value},
    RString,
};

/// A Value pointer to a RRegexp struct, Ruby's internal representation of
/// regular expressions.
///
/// All [`Value`] methods should be available on this type through [`Deref`],
/// but some may be missed by this documentation.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RRegexp(NonZeroValue);

impl RRegexp {
    /// Return `Some(RRegexp)` if `val` is a `RRegexp`, `None` otherwise.
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            (val.rb_type() == ruby_value_type::RUBY_T_REGEXP)
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    #[inline]
    unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        Self(NonZeroValue::new_unchecked(Value::new(val)))
    }

    /// Create a new `Regexp` from the Rust string `pattern`.
    ///
    /// The encoding of the Ruby regexp will be UTF-8.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, r_regexp::Opts, RRegexp};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let regexp = RRegexp::new("foo", Opts::new().ignorecase()).unwrap();
    /// let res: bool = eval!(r#"regexp == /foo/i"#, regexp).unwrap();
    /// assert!(res);
    /// ```
    pub fn new(pattern: &str, opts: Opts) -> Result<Self, Error> {
        protect(|| unsafe {
            Self::from_rb_value_unchecked(rb_enc_reg_new(
                pattern.as_ptr() as *const c_char,
                pattern.len() as c_long,
                RbEncoding::utf8().as_ptr(),
                opts.0 as c_int,
            ))
        })
    }

    /// Create a new `Regexp` from the Ruby string `pattern`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, r_regexp::Opts, RRegexp, RString};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let regexp = RRegexp::new_str(RString::new("foo"), Opts::new().ignorecase()).unwrap();
    /// let res: bool = eval!(r#"regexp == /foo/i"#, regexp).unwrap();
    /// assert!(res);
    /// ```
    pub fn new_str(pattern: RString, opts: Opts) -> Result<Self, Error> {
        protect(|| unsafe {
            Self::from_rb_value_unchecked(rb_reg_new_str(pattern.as_rb_value(), opts.0 as c_int))
        })
    }
}

impl Deref for RRegexp {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
    }
}

impl fmt::Display for RRegexp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for RRegexp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl EncodingCapable for RRegexp {}

impl From<RRegexp> for Value {
    fn from(val: RRegexp) -> Self {
        *val
    }
}

unsafe impl private::ReprValue for RRegexp {
    fn to_value(self) -> Value {
        *self
    }

    unsafe fn from_value_unchecked(val: Value) -> Self {
        Self(NonZeroValue::new_unchecked(val))
    }
}

impl ReprValue for RRegexp {}

impl TryConvert for RRegexp {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Self::from_value(val).ok_or_else(|| {
            Error::new(
                exception::type_error(),
                format!("no implicit conversion of {} into Regexp", unsafe {
                    val.classname()
                },),
            )
        })
    }
}

/// Options for creating [`RRegexp`].
#[derive(Clone, Copy)]
pub struct Opts(c_uint);

impl Opts {
    /// Ignore case.
    pub const IGNORECASE: Self = Self::new().ignorecase();
    /// Ignore whitespace and comments in the pattern.
    pub const EXTEND: Self = Self::new().extend();
    /// Treat a newline as a character matched by `.`
    pub const MULTILINE: Self = Self::new().multiline();

    /// Create a new blank regexp `Opts`.
    pub const fn new() -> Self {
        Self(rb_sys::ONIG_OPTION_NONE)
    }

    /// Ignore case.
    ///
    /// Equivalent to `/pattern/i` in Ruby.
    pub const fn ignorecase(self) -> Self {
        Self(self.0 | rb_sys::ONIG_OPTION_IGNORECASE)
    }

    /// Ignore whitespace and comments in the pattern.
    ///
    /// Equivalent to `/pattern/x` in Ruby.
    pub const fn extend(self) -> Self {
        Self(self.0 | rb_sys::ONIG_OPTION_EXTEND)
    }

    /// Treat a newline as a character matched by `.`
    ///
    /// Equivalent to `/pattern/m` in Ruby.
    pub const fn multiline(self) -> Self {
        Self(self.0 | rb_sys::ONIG_OPTION_MULTILINE)
    }

    // undocumented in Ruby
    #[allow(missing_docs)]
    pub const fn dotall(self) -> Self {
        Self(self.0 | rb_sys::ONIG_OPTION_DOTALL)
    }

    // undocumented in Ruby
    #[allow(missing_docs)]
    pub const fn singleline(self) -> Self {
        Self(self.0 | rb_sys::ONIG_OPTION_SINGLELINE)
    }

    // undocumented in Ruby
    #[allow(missing_docs)]
    pub const fn find_longest(self) -> Self {
        Self(self.0 | rb_sys::ONIG_OPTION_FIND_LONGEST)
    }

    // undocumented in Ruby
    #[allow(missing_docs)]
    pub const fn find_not_empty(self) -> Self {
        Self(self.0 | rb_sys::ONIG_OPTION_FIND_NOT_EMPTY)
    }

    // undocumented in Ruby
    #[allow(missing_docs)]
    pub const fn negate_singleline(self) -> Self {
        Self(self.0 | rb_sys::ONIG_OPTION_NEGATE_SINGLELINE)
    }

    // undocumented in Ruby
    #[allow(missing_docs)]
    pub const fn dont_capture_group(self) -> Self {
        Self(self.0 | rb_sys::ONIG_OPTION_DONT_CAPTURE_GROUP)
    }

    // undocumented in Ruby
    #[allow(missing_docs)]
    pub const fn capture_group(self) -> Self {
        Self(self.0 | rb_sys::ONIG_OPTION_CAPTURE_GROUP)
    }

    // undocumented in Ruby
    #[allow(missing_docs)]
    pub const fn notbol(self) -> Self {
        Self(self.0 | rb_sys::ONIG_OPTION_NOTBOL)
    }

    // undocumented in Ruby
    #[allow(missing_docs)]
    pub const fn noteol(self) -> Self {
        Self(self.0 | rb_sys::ONIG_OPTION_NOTEOL)
    }

    // undocumented in Ruby
    #[allow(missing_docs)]
    pub const fn notbos(self) -> Self {
        Self(self.0 | rb_sys::ONIG_OPTION_NOTBOS)
    }

    // undocumented in Ruby
    #[allow(missing_docs)]
    pub const fn noteos(self) -> Self {
        Self(self.0 | rb_sys::ONIG_OPTION_NOTEOS)
    }

    // undocumented in Ruby
    #[allow(missing_docs)]
    pub const fn ascii_range(self) -> Self {
        Self(self.0 | rb_sys::ONIG_OPTION_ASCII_RANGE)
    }

    // undocumented in Ruby
    #[allow(missing_docs)]
    pub const fn posix_bracket_all_range(self) -> Self {
        Self(self.0 | rb_sys::ONIG_OPTION_POSIX_BRACKET_ALL_RANGE)
    }

    // undocumented in Ruby
    #[allow(missing_docs)]
    pub const fn word_bound_all_range(self) -> Self {
        Self(self.0 | rb_sys::ONIG_OPTION_WORD_BOUND_ALL_RANGE)
    }

    // undocumented in Ruby
    #[allow(missing_docs)]
    pub const fn newline_crlf(self) -> Self {
        Self(self.0 | rb_sys::ONIG_OPTION_NEWLINE_CRLF)
    }
}

impl Default for Opts {
    fn default() -> Self {
        Self::new()
    }
}
