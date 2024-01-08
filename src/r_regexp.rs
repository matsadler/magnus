//! Types for working with Ruby’s Regexp class.

use std::{
    fmt,
    os::raw::{c_char, c_int, c_long, c_uint},
};

use rb_sys::{
    rb_enc_reg_new, rb_reg_match, rb_reg_new_str, rb_reg_options, ruby_value_type, VALUE,
};

use crate::{
    encoding::EncodingCapable,
    error::{protect, Error},
    into_value::IntoValue,
    r_string::{IntoRString, RString},
    try_convert::TryConvert,
    value::{
        private::{self, ReprValue as _},
        NonZeroValue, ReprValue, Value,
    },
    Ruby,
};

/// # `RRegexp`
///
/// Functions that can be used to create Ruby `Regexp`s.
///
/// See also the [`RRegexp`] type.
impl Ruby {
    /// Create a new `Regexp` from the Rust string `pattern`.
    ///
    /// The encoding of the Ruby regexp will be UTF-8.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{r_regexp::Opts, rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let regexp = ruby.reg_new("foo", Opts::new().ignorecase())?;
    ///     rb_assert!(ruby, r#"regexp == /foo/i"#, regexp);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn reg_new(&self, pattern: &str, opts: Opts) -> Result<RRegexp, Error> {
        protect(|| unsafe {
            RRegexp::from_rb_value_unchecked(rb_enc_reg_new(
                pattern.as_ptr() as *const c_char,
                pattern.len() as c_long,
                self.utf8_encoding().as_ptr(),
                opts.0 as c_int,
            ))
        })
    }
}

/// A Value pointer to a RRegexp struct, Ruby's internal representation of
/// regular expressions.
///
/// See the [`ReprValue`] trait for additional methods available on this type.
/// See [`Ruby`](Ruby#rregexp) for methods to create an `RRegexp`.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RRegexp(NonZeroValue);

impl RRegexp {
    /// Return `Some(RRegexp)` if `val` is a `RRegexp`, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RRegexp};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(RRegexp::from_value(eval("/f(.)o/").unwrap()).is_some());
    /// assert!(RRegexp::from_value(eval(r#""f*""#).unwrap()).is_none());
    /// ```
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
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread. See [`Ruby::reg_new`] for the
    /// non-panicking version.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(deprecated)]
    /// use magnus::{r_regexp::Opts, rb_assert, RRegexp};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let regexp = RRegexp::new("foo", Opts::new().ignorecase()).unwrap();
    /// rb_assert!(r#"regexp == /foo/i"#, regexp);
    /// ```
    #[cfg_attr(
        not(feature = "old-api"),
        deprecated(note = "please use `Ruby::reg_new` instead")
    )]
    #[inline]
    pub fn new(pattern: &str, opts: Opts) -> Result<Self, Error> {
        get_ruby!().reg_new(pattern, opts)
    }

    /// Create a new `Regexp` from the Ruby string `pattern`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{r_regexp::Opts, rb_assert, RRegexp, RString};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let regexp = RRegexp::new_str(RString::new("foo"), Opts::new().ignorecase()).unwrap();
    /// rb_assert!(r#"regexp == /foo/i"#, regexp);
    /// ```
    pub fn new_str(pattern: RString, opts: Opts) -> Result<Self, Error> {
        protect(|| unsafe {
            Self::from_rb_value_unchecked(rb_reg_new_str(pattern.as_rb_value(), opts.0 as c_int))
        })
    }

    /// Returns the index (in characters) of the first match in `s`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::RRegexp;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let regexp = RRegexp::new("x", Default::default()).unwrap();
    /// assert_eq!(regexp.reg_match("text").unwrap(), Some(2));
    /// assert_eq!(regexp.reg_match("test").unwrap(), None);
    /// ```
    pub fn reg_match<T>(self, s: T) -> Result<Option<usize>, Error>
    where
        T: IntoRString,
    {
        let s = s.into_r_string_with(&Ruby::get_with(self));
        protect(|| unsafe { Value::new(rb_reg_match(self.as_rb_value(), s.as_rb_value())) })
            .and_then(TryConvert::try_convert)
    }

    /// Returns the options set for `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RRegexp};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let regexp: RRegexp = eval("/x/i").unwrap();
    /// assert!(regexp.options().is_ignorecase());
    /// assert!(!regexp.options().is_multiline());
    ///
    /// let regexp: RRegexp = eval("/x/m").unwrap();
    /// assert!(!regexp.options().is_ignorecase());
    /// assert!(regexp.options().is_multiline());
    /// ```
    pub fn options(self) -> Opts {
        unsafe { Opts(rb_reg_options(self.as_rb_value()) as c_uint) }
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

impl IntoValue for RRegexp {
    #[inline]
    fn into_value_with(self, _: &Ruby) -> Value {
        self.0.get()
    }
}

unsafe impl private::ReprValue for RRegexp {}

impl ReprValue for RRegexp {}

impl TryConvert for RRegexp {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Self::from_value(val).ok_or_else(|| {
            Error::new(
                Ruby::get_with(val).exception_type_error(),
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

    /// Return `true` if the `ignorecase` option is set, `false` otherwise.
    pub const fn is_ignorecase(self) -> bool {
        self.0 & rb_sys::ONIG_OPTION_IGNORECASE != 0
    }

    /// Return `true` if the `extend` option is set, `false` otherwise.
    pub const fn is_extend(self) -> bool {
        self.0 & rb_sys::ONIG_OPTION_EXTEND != 0
    }

    /// Return `true` if the `multiline` option is set, `false` otherwise.
    pub const fn is_multiline(self) -> bool {
        self.0 & rb_sys::ONIG_OPTION_MULTILINE != 0
    }

    /// Return `true` if the `dotall` option is set, `false` otherwise.
    pub const fn is_dotall(self) -> bool {
        self.0 & rb_sys::ONIG_OPTION_DOTALL != 0
    }

    /// Return `true` if the `singleline` option is set, `false` otherwise.
    pub const fn is_singleline(self) -> bool {
        self.0 & rb_sys::ONIG_OPTION_SINGLELINE != 0
    }

    /// Return `true` if the `find_longest` option is set, `false` otherwise.
    pub const fn is_find_longest(self) -> bool {
        self.0 & rb_sys::ONIG_OPTION_FIND_LONGEST != 0
    }

    /// Return `true` if the `find_not_empty` option is set, `false` otherwise.
    pub const fn is_find_not_empty(self) -> bool {
        self.0 & rb_sys::ONIG_OPTION_FIND_NOT_EMPTY != 0
    }

    /// Return `true` if the `negate_singleline` option is set, `false`
    /// otherwise.
    pub const fn is_negate_singleline(self) -> bool {
        self.0 & rb_sys::ONIG_OPTION_NEGATE_SINGLELINE != 0
    }

    /// Return `true` if the `dont_capture_group` option is set, `false`
    /// otherwise.
    pub const fn is_dont_capture_group(self) -> bool {
        self.0 & rb_sys::ONIG_OPTION_DONT_CAPTURE_GROUP != 0
    }

    /// Return `true` if the `capture_group` option is set, `false` otherwise.
    pub const fn is_capture_group(self) -> bool {
        self.0 & rb_sys::ONIG_OPTION_CAPTURE_GROUP != 0
    }

    /// Return `true` if the `notbol` option is set, `false` otherwise.
    pub const fn is_notbol(self) -> bool {
        self.0 & rb_sys::ONIG_OPTION_NOTBOL != 0
    }

    /// Return `true` if the `noteol` option is set, `false` otherwise.
    pub const fn is_noteol(self) -> bool {
        self.0 & rb_sys::ONIG_OPTION_NOTEOL != 0
    }

    /// Return `true` if the `notbos` option is set, `false` otherwise.
    pub const fn is_notbos(self) -> bool {
        self.0 & rb_sys::ONIG_OPTION_NOTBOS != 0
    }

    /// Return `true` if the `noteos` option is set, `false` otherwise.
    pub const fn is_noteos(self) -> bool {
        self.0 & rb_sys::ONIG_OPTION_NOTEOS != 0
    }

    /// Return `true` if the `ascii_range` option is set, `false` otherwise.
    pub const fn is_ascii_range(self) -> bool {
        self.0 & rb_sys::ONIG_OPTION_ASCII_RANGE != 0
    }

    /// Return `true` if the `posix_bracket_all_range` option is set, `false`
    /// otherwise.
    pub const fn is_posix_bracket_all_range(self) -> bool {
        self.0 & rb_sys::ONIG_OPTION_POSIX_BRACKET_ALL_RANGE != 0
    }

    /// Return `true` if the `word_bound_all_range` option is set, `false`
    /// otherwise.
    pub const fn is_word_bound_all_range(self) -> bool {
        self.0 & rb_sys::ONIG_OPTION_WORD_BOUND_ALL_RANGE != 0
    }

    /// Return `true` if the `newline_crlf` option is set, `false` otherwise.
    pub const fn is_newline_crlf(self) -> bool {
        self.0 & rb_sys::ONIG_OPTION_NEWLINE_CRLF != 0
    }
}

impl Default for Opts {
    fn default() -> Self {
        Self::new()
    }
}

impl From<Opts> for i32 {
    fn from(val: Opts) -> i32 {
        val.0 as i32
    }
}
