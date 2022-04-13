//! Types for working with Ruby’s String class.

use std::{
    borrow::Cow,
    fmt, io,
    ops::Deref,
    os::raw::{c_char, c_long},
    path::{Path, PathBuf},
    ptr::{self, NonNull},
    slice, str,
};

use crate::{
    debug_assert_value,
    encoding::{self, EncodingCapable, RbEncoding},
    error::{protect, Error},
    exception,
    object::Object,
    ruby_sys::{
        self, rb_str_buf_append, rb_str_buf_new, rb_str_cat, rb_str_conv_enc, rb_str_new,
        rb_str_new_frozen, rb_str_new_shared, rb_str_to_str, rb_utf8_str_new,
        rb_utf8_str_new_static, ruby_rstring_flags, ruby_value_type, VALUE,
    },
    try_convert::TryConvert,
    value::{private, NonZeroValue, ReprValue, Value},
};

#[cfg(ruby_gte_3_0)]
use crate::ruby_sys::{rb_str_to_interned_str, ruby_rstring_consts::RSTRING_EMBED_LEN_SHIFT};

#[cfg(ruby_lt_3_0)]
use crate::ruby_sys::ruby_rstring_flags::RSTRING_EMBED_LEN_SHIFT;

/// A Value pointer to a RString struct, Ruby's internal representation of
/// strings.
///
/// All [`Value`] methods should be available on this type through [`Deref`],
/// but some may be missed by this documentation.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RString(NonZeroValue);

impl RString {
    /// Return `Some(RString)` if `val` is a `RString`, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RString};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(RString::from_value(eval(r#""example""#).unwrap()).is_some());
    /// assert!(RString::from_value(eval(":example").unwrap()).is_none());
    /// ```
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            (val.rb_type() == ruby_value_type::RUBY_T_STRING)
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    pub(crate) fn ref_from_value(val: &Value) -> Option<&Self> {
        unsafe {
            (val.rb_type() == ruby_value_type::RUBY_T_STRING)
                .then(|| &*(val as *const _ as *const RString))
        }
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        Self(NonZeroValue::new_unchecked(Value::new(val)))
    }

    fn as_internal(self) -> NonNull<ruby_sys::RString> {
        // safe as inner value is NonZero
        unsafe { NonNull::new_unchecked(self.0.get().as_rb_value() as *mut _) }
    }

    /// Create a new Ruby string from the Rust string `s`.
    ///
    /// The encoding of the Ruby string will be UTF-8.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RString};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let val = RString::new("example");
    /// let res: bool = eval!(r#"val == "example""#, val).unwrap();
    /// assert!(res);
    /// ```
    pub fn new(s: &str) -> Self {
        let len = s.len();
        let ptr = s.as_ptr();
        unsafe {
            Self::from_rb_value_unchecked(rb_utf8_str_new(ptr as *const c_char, len as c_long))
        }
    }

    /// Implementation detail of [`r_string`].
    #[doc(hidden)]
    #[inline]
    pub unsafe fn new_lit(ptr: *const c_char, len: c_long) -> Self {
        Self::from_rb_value_unchecked(rb_utf8_str_new_static(ptr, len))
    }

    /// Create a new Ruby string with capacity `n`.
    ///
    /// The encoding will be set to ASCII-8BIT (aka BINARY). See also
    /// [`with_capacity`](RString::with_capacity).
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RString};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let buf = RString::buf_new(4096);
    /// buf.cat(&[13, 14, 10, 13, 11, 14, 14, 15]);
    /// let res: bool = eval!(r#"buf == "\r\x0E\n\r\v\x0E\x0E\x0F""#, buf).unwrap();
    /// assert!(res);
    /// ```
    pub fn buf_new(n: usize) -> Self {
        unsafe { Self::from_rb_value_unchecked(rb_str_buf_new(n as c_long)) }
    }

    /// Create a new Ruby string with capacity `n`.
    ///
    /// The encoding will be set to UTF-8. See also
    /// [`buf_new`](RString::buf_new).
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RString};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let s = RString::with_capacity(9);
    /// s.cat("foo");
    /// s.cat("bar");
    /// s.cat("baz");
    /// let res: bool = eval!(r#"s == "foobarbaz""#, s).unwrap();
    /// assert!(res);
    /// ```
    pub fn with_capacity(n: usize) -> Self {
        let s = Self::buf_new(n);
        s.enc_associate(encoding::Index::utf8()).unwrap();
        s
    }

    /// Create a new Ruby string from the Rust slice `s`.
    ///
    /// The encoding of the Ruby string will be set to ASCII-8BIT (aka BINARY).
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RString};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let buf = RString::from_slice(&[13, 14, 10, 13, 11, 14, 14, 15]);
    /// let res: bool = eval!(r#"buf == "\r\x0E\n\r\v\x0E\x0E\x0F""#, buf).unwrap();
    /// assert!(res);
    /// ```
    pub fn from_slice(s: &[u8]) -> Self {
        let len = s.len();
        let ptr = s.as_ptr();
        unsafe { Self::from_rb_value_unchecked(rb_str_new(ptr as *const c_char, len as c_long)) }
    }

    /// Create a new Ruby string from the Rust char `c`.
    ///
    /// The encoding of the Ruby string will be UTF-8.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RString};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let c = RString::from_char('a');
    /// let res: bool = eval!(r#"c == "a""#, c).unwrap();
    /// assert!(res);
    /// ```
    ///
    /// ```
    /// use magnus::{eval, RString};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let c = RString::from_char('🦀');
    /// let res: bool = eval!(r#"c == "🦀""#, c).unwrap();
    /// assert!(res);
    /// ```
    pub fn from_char(c: char) -> Self {
        let mut buf = [0; 4];
        Self::new(c.encode_utf8(&mut buf[..]))
    }

    /// Create a new Ruby string that shares the same backing data as `s`.
    ///
    /// Both string objects will point at the same underlying data until one is
    /// modified, and only then will the data be duplicated. This operation is
    /// cheep, and useful for cases where you may need to modify a string, but
    /// don't want to mutate a value passed to your function.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RString};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let s = RString::new("example");
    /// let dup = RString::new_shared(s);
    /// let res: bool = eval!("s == dup", s, dup).unwrap();
    /// assert!(res);
    /// // mutating one doesn't mutate both
    /// dup.cat("foo");
    /// let res: bool = eval!("s != dup", s, dup).unwrap();
    /// assert!(res);
    /// ```
    pub fn new_shared(s: Self) -> Self {
        unsafe { Self::from_rb_value_unchecked(rb_str_new_shared(s.as_rb_value())) }
    }

    /// Create a new Ruby string that is a frozen copy of `s`.
    ///
    /// This can be used to get a copy of a string that is guranteed not to be
    /// modified while you are referencing it.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RString};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let orig = RString::new("example");
    /// let frozen = RString::new_frozen(orig);
    /// let res: bool = eval!(r#"frozen == "example""#, frozen).unwrap();
    /// assert!(res);
    /// // mutating original doesn't impact the frozen copy
    /// orig.cat("foo");
    /// let res: bool = eval!(r#"frozen == "example""#, frozen).unwrap();
    /// assert!(res);
    /// ```
    pub fn new_frozen(s: Self) -> Self {
        unsafe { Self::from_rb_value_unchecked(rb_str_new_frozen(s.as_rb_value())) }
    }

    /// Return `self` as a slice of bytes.
    ///
    /// # Safety
    ///
    /// This is directly viewing memory owned and managed by Ruby. Ruby may
    /// modify or free the memory backing the returned slice, the caller must
    /// ensure this does not happen.
    ///
    /// Ruby must not be allowed to garbage collect or modify `self` while a
    /// refrence to the slice is held.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::RString;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let s = RString::new("example");
    /// // safe as we don't give Ruby the chance to mess with the string while
    /// // we hold a refrence to the slice.
    /// unsafe { assert_eq!(s.as_slice(), [101, 120, 97, 109, 112, 108, 101]) };
    /// ```
    pub unsafe fn as_slice(&self) -> &[u8] {
        self.as_slice_unconstrained()
    }

    unsafe fn as_slice_unconstrained<'a>(self) -> &'a [u8] {
        #[cfg(ruby_gte_3_1)]
        unsafe fn embedded_ary_ptr(rstring: RString) -> *const u8 {
            &rstring.as_internal().as_ref().as_.embed.ary as *const _ as *const u8
        }

        #[cfg(ruby_lt_3_1)]
        unsafe fn embedded_ary_ptr(rstring: RString) -> *const u8 {
            &rstring.as_internal().as_ref().as_.ary as *const _ as *const u8
        }

        debug_assert_value!(self);
        let r_basic = self.r_basic_unchecked();
        let mut f = r_basic.as_ref().flags;
        if (f & ruby_rstring_flags::RSTRING_NOEMBED as VALUE) != 0 {
            let h = self.as_internal().as_ref().as_.heap;
            slice::from_raw_parts(h.ptr as *const u8, h.len as usize)
        } else {
            f &= ruby_rstring_flags::RSTRING_EMBED_LEN_MASK as VALUE;
            f >>= RSTRING_EMBED_LEN_SHIFT as VALUE;
            slice::from_raw_parts(embedded_ary_ptr(self), f as usize)
        }
    }

    /// Returns true if the encoding for this string is UTF-8 or US-ASCII,
    /// false otherwise.
    ///
    /// The encoding on a Ruby String is just a label, it provides no guarantee
    /// that the String really is valid UTF-8.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RString};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let s: RString = eval!(r#""café""#).unwrap();
    /// assert!(s.is_utf8_compatible_encoding());
    /// ```
    ///
    /// ```
    /// use magnus::{eval, RString};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let s: RString = eval!(r#""café".encode("ISO-8859-1")"#).unwrap();
    /// assert!(!s.is_utf8_compatible_encoding());
    /// ```
    pub fn is_utf8_compatible_encoding(self) -> bool {
        let encindex = self.enc_get();
        // us-ascii is a 100% compatible subset of utf8
        encindex == encoding::Index::utf8() || encindex == encoding::Index::usascii()
    }

    /// Returns a new string by reencoding `self` from its current encoding to
    /// UTF-8.
    #[deprecated(
        since = "0.3.0",
        note = "please use `r_string.conv_enc(RbEncoding::utf8())` instead"
    )]
    pub fn encode_utf8(self) -> Result<Self, Error> {
        self.conv_enc(RbEncoding::utf8())
    }

    /// Returns a new string by reencoding `self` from its current encoding to
    /// the given `enc`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{encoding::RbEncoding, eval, RString};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let s: RString = eval!(r#""café".encode("ISO-8859-1")"#).unwrap();
    /// // safe as we don't give Ruby the chance to mess with the string while
    /// // we hold a refrence to the slice.
    /// unsafe { assert_eq!(s.as_slice(), &[99, 97, 102, 233]) };
    /// let e = s.conv_enc(RbEncoding::utf8()).unwrap();
    /// unsafe { assert_eq!(e.as_slice(), &[99, 97, 102, 195, 169]) };
    /// ```
    pub fn conv_enc<T>(self, enc: T) -> Result<Self, Error>
    where
        T: Into<RbEncoding>,
    {
        unsafe {
            protect(|| {
                Value::new(rb_str_conv_enc(
                    self.as_rb_value(),
                    ptr::null_mut(),
                    enc.into().as_ptr(),
                ))
            })
            .map(|v| Self::from_rb_value_unchecked(v.as_rb_value()))
        }
    }

    /// Returns a Rust `&str` reference to the value of `self`.
    ///
    /// Errors if `self`'s encoding is not UTF-8 (or US-ASCII), or if the
    /// string is not valid UTF-8.
    ///
    /// # Safety
    ///
    /// This is directly viewing memory owned and managed by Ruby. Ruby may
    /// modify or free the memory backing the returned str, the caller must
    /// ensure this does not happen.
    ///
    /// Ruby must not be allowed to garbage collect or modify `self` while a
    /// refrence to the str is held.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::RString;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let s = RString::new("example");
    /// // safe as we don't give Ruby the chance to mess with the string while
    /// // we hold a refrence to the slice.
    /// unsafe { assert_eq!(s.as_str().unwrap(), "example") };
    /// ```
    pub unsafe fn as_str(&self) -> Result<&str, Error> {
        self.as_str_unconstrained()
    }

    pub(crate) unsafe fn as_str_unconstrained<'a>(self) -> Result<&'a str, Error> {
        if !self.is_utf8_compatible_encoding() {
            let enc = RbEncoding::from(self.enc_get());
            return Err(Error::new(
                exception::encoding_error(),
                format!("expected utf-8, got {}", enc.name()),
            ));
        }
        str::from_utf8(self.as_slice_unconstrained())
            .map_err(|e| Error::new(exception::encoding_error(), format!("{}", e)))
    }

    /// Returns `self` as a Rust string, ignoring the Ruby encoding and
    /// dropping any non-UTF-8 characters. If `self` is valid UTF-8 this will
    /// return a `&str` reference.
    ///
    /// # Safety
    ///
    /// This may return a direct view of memory owned and managed by Ruby. Ruby
    /// may modify or free the memory backing the returned str, the caller must
    /// ensure this does not happen.
    ///
    /// Ruby must not be allowed to garbage collect or modify `self` while a
    /// refrence to the str is held.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::RString;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let s = RString::new("example");
    /// // safe as we don't give Ruby the chance to mess with the string while
    /// // we hold a refrence to the slice.
    /// unsafe { assert_eq!(s.to_string_lossy(), "example") };
    /// ```
    #[allow(clippy::wrong_self_convention)]
    pub unsafe fn to_string_lossy(&self) -> Cow<'_, str> {
        String::from_utf8_lossy(self.as_slice())
    }

    /// Returns `self` as an owned Rust `String`. The Ruby string will be
    /// reencoded as UTF-8 if required. Errors if the string can not be encoded
    /// as UTF-8.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::RString;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let s = RString::new("example");
    /// assert_eq!(s.to_string().unwrap(), "example");
    /// ```
    pub fn to_string(self) -> Result<String, Error> {
        let utf8 = if self.is_utf8_compatible_encoding() {
            self
        } else {
            self.conv_enc(RbEncoding::utf8())?
        };
        str::from_utf8(unsafe { utf8.as_slice() })
            .map(ToOwned::to_owned)
            .map_err(|e| Error::new(exception::encoding_error(), format!("{}", e)))
    }

    /// Converts `self` to a [`char`]. Errors if the string is more than one
    /// character or can not be encoded as UTF-8.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::RString;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let s = RString::new("a");
    /// assert_eq!(s.to_char().unwrap(), 'a');
    /// ```
    pub fn to_char(self) -> Result<char, Error> {
        let utf8 = if self.is_utf8_compatible_encoding() {
            self
        } else {
            self.conv_enc(RbEncoding::utf8())?
        };
        unsafe {
            str::from_utf8(utf8.as_slice())
                .map_err(|e| Error::new(exception::encoding_error(), format!("{}", e)))?
                .parse()
                .map_err(|e| {
                    Error::new(
                        exception::type_error(),
                        format!("could not convert string to char, {}", e),
                    )
                })
        }
    }

    /// Returns whether `self` is a frozen interned string. Interned strings
    /// are usually string literals with the in files with the
    /// `# frozen_string_literal: true` 'magic comment'.
    ///
    /// Interned strings won't be garbage collected or modified, so should be
    /// safe to store on the heap or hold a `&str` refrence to. See
    /// [`as_interned_str`](RString::as_interned_str).
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RString};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let s: RString = eval!(r#"
    /// ## frozen_string_literal: true
    ///
    /// "example"
    /// "#).unwrap();
    /// assert!(s.is_interned());
    /// ```
    ///
    /// ```
    /// use magnus::{eval, RString};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let s: RString = eval!(r#""example""#).unwrap();
    /// assert!(!s.is_interned());
    /// ```
    pub fn is_interned(self) -> bool {
        unsafe {
            self.r_basic_unchecked().as_ref().flags & ruby_rstring_flags::RSTRING_FSTR as VALUE != 0
        }
    }

    /// Returns `Some(FString)` if self is interned, `None` otherwise.
    ///
    /// Interned strings won't be garbage collected or modified, so should be
    /// safe to store on the heap or hold a `&str` refrence to. The `FString`
    /// type returned by this function provides a way to encode this property
    /// into the type system, and provides safe methods to access the string
    /// as a `&str` or slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RString};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let s: RString = eval!(r#"
    /// ## frozen_string_literal: true
    ///
    /// "example"
    /// "#).unwrap();
    /// assert!(s.as_interned_str().is_some());
    /// ```
    ///
    /// ```
    /// use magnus::{eval, RString};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let s: RString = eval!(r#""example""#).unwrap();
    /// assert!(s.as_interned_str().is_none());
    /// ```
    pub fn as_interned_str(self) -> Option<FString> {
        self.is_interned().then(|| FString(self))
    }

    /// Interns self and returns a [`FString`]. Be aware that once interned a
    /// string will never be garbage collected.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RString};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let fstring = RString::new("example").to_interned_str();
    /// assert_eq!(fstring.as_str().unwrap(), "example");
    /// ```
    #[cfg(ruby_gte_3_0)]
    pub fn to_interned_str(self) -> FString {
        unsafe {
            FString(RString::from_rb_value_unchecked(rb_str_to_interned_str(
                self.as_rb_value(),
            )))
        }
    }

    /// Mutate `self`, adding `other` to the end. Errors if `self` and
    /// other`'s encodings are not compatible.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::RString;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let a = RString::new("foo");
    /// let b = RString::new("bar");
    /// a.append(b).unwrap();
    /// assert_eq!(a.to_string().unwrap(), "foobar");
    /// ```
    pub fn append(self, other: Self) -> Result<(), Error> {
        unsafe {
            protect(|| Value::new(rb_str_buf_append(self.as_rb_value(), other.as_rb_value())))?;
        }
        Ok(())
    }

    /// Mutate `self`, adding `buf` to the end.
    ///
    /// Note: This ignore's `self`'s encoding, and may result in `self`
    /// containing invalid bytes for its encoding. It's assumed this will more
    /// often be used with ASCII-8BIT (aka BINARY) encoded strings. See
    /// [`buf_new`](RString::buf_new) and [`from_slice`](RString::from_slice).
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RString};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let buf = RString::buf_new(4096);
    /// buf.cat(&[102, 111, 111]);
    /// buf.cat("bar");
    /// assert_eq!(buf.to_string().unwrap(), "foobar");
    /// ```
    pub fn cat<T: AsRef<[u8]>>(self, buf: T) {
        let buf = buf.as_ref();
        let len = buf.len();
        let ptr = buf.as_ptr();
        unsafe {
            rb_str_cat(self.as_rb_value(), ptr as *const c_char, len as c_long);
        }
    }
}

impl Deref for RString {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
    }
}

impl fmt::Display for RString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for RString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl EncodingCapable for RString {}

impl io::Write for RString {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let len = buf.len();
        self.cat(buf);
        Ok(len)
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

impl From<&str> for RString {
    fn from(val: &str) -> Self {
        RString::new(val)
    }
}

impl From<String> for RString {
    fn from(val: String) -> Self {
        RString::new(&val)
    }
}

impl From<RString> for Value {
    fn from(val: RString) -> Self {
        *val
    }
}

impl From<&str> for Value {
    fn from(val: &str) -> Self {
        RString::new(val).into()
    }
}

impl From<String> for Value {
    fn from(val: String) -> Self {
        val.as_str().into()
    }
}

impl From<char> for Value {
    fn from(val: char) -> Self {
        RString::from_char(val).into()
    }
}

#[cfg(unix)]
impl From<&Path> for Value {
    fn from(val: &Path) -> Self {
        use std::os::unix::ffi::OsStrExt;
        RString::from_slice(val.as_os_str().as_bytes()).into()
    }
}

#[cfg(not(unix))]
impl From<&Path> for Value {
    fn from(val: &Path) -> Self {
        RString::new(val.to_string_lossy().as_ref()).into()
    }
}

impl From<PathBuf> for Value {
    fn from(val: PathBuf) -> Self {
        val.as_path().into()
    }
}

impl Object for RString {}

unsafe impl private::ReprValue for RString {
    fn to_value(self) -> Value {
        *self
    }

    unsafe fn from_value_unchecked(val: Value) -> Self {
        Self(NonZeroValue::new_unchecked(val))
    }
}

impl ReprValue for RString {}

impl TryConvert for RString {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        unsafe {
            match Self::from_value(*val) {
                Some(i) => Ok(i),
                None => protect(|| {
                    debug_assert_value!(val);
                    Value::new(rb_str_to_str(val.as_rb_value()))
                })
                .map(|res| Self::from_rb_value_unchecked(res.as_rb_value())),
            }
        }
    }
}

/// FString contains an RString known to be interned.
///
/// Interned strings won't be garbage collected or modified, so should be
/// safe to store on the heap or hold a `&str` refrence to. `FString` provides
/// a way to encode this property into the type system, and provides safe
/// methods to access the string as a `&str` or slice.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct FString(RString);

impl FString {
    /// Returns the interned string as a [`RString`].
    pub fn as_r_string(self) -> RString {
        self.0
    }

    /// Returns the interned string as a slice of bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RString};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let s: RString = eval!(r#"
    /// ## frozen_string_literal: true
    ///
    /// "example"
    /// "#).unwrap();
    /// let fstring = s.as_interned_str().unwrap();
    /// assert_eq!(fstring.as_slice(), &[101, 120, 97, 109, 112, 108, 101]);
    /// ```
    pub fn as_slice(self) -> &'static [u8] {
        unsafe { self.as_r_string().as_slice_unconstrained() }
    }

    /// Returns the interned string as a &str. Errors if the string contains
    /// invliad UTF-8.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RString};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let s: RString = eval!(r#"# frozen_string_literal: true
    /// "example"
    /// "#).unwrap();
    /// let fstring = s.as_interned_str().unwrap();
    /// assert_eq!(fstring.as_str().unwrap(), "example");
    /// ```
    pub fn as_str(self) -> Result<&'static str, Error> {
        unsafe { self.as_r_string().as_str_unconstrained() }
    }

    /// Returns interned string as a Rust string, ignoring the Ruby encoding
    /// and dropping any non-UTF-8 characters. If the string is valid UTF-8
    /// this will return a `&str` reference.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RString};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let s: RString = eval!(r#"
    /// ## frozen_string_literal: true
    ///
    /// "example"
    /// "#).unwrap();
    /// let fstring = s.as_interned_str().unwrap();
    /// assert_eq!(fstring.to_string_lossy(), "example");
    /// ```
    pub fn to_string_lossy(self) -> Cow<'static, str> {
        String::from_utf8_lossy(self.as_slice())
    }
}

impl Deref for FString {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.deref()
    }
}

impl fmt::Display for FString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.as_r_string().to_s_infallible() })
    }
}

impl fmt::Debug for FString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_r_string().inspect())
    }
}

impl From<FString> for Value {
    fn from(val: FString) -> Self {
        *val.as_r_string()
    }
}

unsafe impl private::ReprValue for FString {
    fn to_value(self) -> Value {
        *self
    }

    unsafe fn from_value_unchecked(val: Value) -> Self {
        Self(RString::from_value_unchecked(val))
    }
}

impl ReprValue for FString {}

/// Create a [`RString`] from a Rust str literal.
///
/// # Examples
///
/// ```
/// use magnus::{eval, r_string};
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// let s = r_string!("Hello, world!");
/// let res: bool = eval!(r#"s == "Hello, world!""#, s).unwrap();
/// assert!(res);
/// ```
#[macro_export]
macro_rules! r_string {
    ($lit:expr) => {{
        let s = concat!($lit, "\0");
        let len = s.len() - 1;
        unsafe { $crate::RString::new_lit(s.as_ptr() as *const _, len as _) }
    }};
}
