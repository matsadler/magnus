//! Types and functions for working with encodings.
//!
//! This module defines 3 types for working with encodings, these types can
//! be converted back and forth with [`From`]/[`Into`] like so:
//! ``` text
//! Encoding <-> RbEncoding <-> Index
//!       |______________________^
//! ```
//! Many functions that require an encoding take their arguments as
//! `Into<RbEncoding>` or `Into<Index>` to ease working with the different
//! types. The type specified for the `Into` conversion hints at the type the
//! function natively works with, and thus will avoid any conversion cost.
//!
//! [`Encoding`] and [`RbEncoding`] both implement [`TryConvert`] and
//! [`IntoValue`] so can be used as parameters and return values in functions
//! bound to Ruby. Both convert from either an instance of `Encoding` or a
//! string of an encoding name, and convert to an instance of `Encoding`.

use std::{
    ffi::{CStr, CString, c_char, c_int},
    fmt,
    ops::Range,
    ptr::{self, NonNull},
};

use rb_sys::{
    rb_ascii8bit_encindex, rb_ascii8bit_encoding, rb_default_external_encoding,
    rb_default_internal_encoding, rb_enc_ascget, rb_enc_associate_index, rb_enc_check,
    rb_enc_codelen, rb_enc_codepoint_len, rb_enc_compatible, rb_enc_copy, rb_enc_default_external,
    rb_enc_default_internal, rb_enc_fast_mbclen, rb_enc_find, rb_enc_find_index,
    rb_enc_from_encoding, rb_enc_from_index, rb_enc_get_index, rb_enc_mbclen,
    rb_enc_precise_mbclen, rb_enc_set_index, rb_enc_to_index, rb_enc_uint_chr, rb_encoding,
    rb_filesystem_encindex, rb_filesystem_encoding, rb_find_encoding, rb_locale_encindex,
    rb_locale_encoding, rb_to_encoding, rb_to_encoding_index, rb_usascii_encindex,
    rb_usascii_encoding, rb_utf8_encindex, rb_utf8_encoding,
};

use crate::{
    Ruby,
    error::{Error, protect},
    into_value::IntoValue,
    object::Object,
    r_string::RString,
    try_convert::TryConvert,
    value::{
        NonZeroValue, ReprValue, Value,
        private::{self, ReprValue as _},
    },
};

/// # `Encoding`
///
/// Functions to access pre-defined Encodings.
///
/// See also the [`Encoding`] type.
impl Ruby {
    /// Returns the default internal encoding as a Ruby object.
    ///
    /// This is the encoding used for anything out-of-process, such as reading
    /// from files or sockets.
    pub fn enc_default_external(&self) -> Encoding {
        Encoding::from_value(Value::new(unsafe { rb_enc_default_external() })).unwrap()
    }

    /// Returns the default external encoding as a Ruby object.
    ///
    /// If set, any out-of-process data is transcoded from the default external
    /// encoding to the default internal encoding.
    pub fn enc_default_internal(&self) -> Option<Encoding> {
        Encoding::from_value(Value::new(unsafe { rb_enc_default_internal() }))
    }
}

/// Wrapper type for a Value known to be an instance of Ruby's Encoding class.
///
/// This is the representation of an encoding exposed to Ruby code.
///
/// See the [`ReprValue`] and [`Object`] traits for additional methods
/// available on this type. See [`Ruby`](Ruby#encoding) for methods to get an
/// `Encoding`.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Encoding(NonZeroValue);

impl Encoding {
    /// Return `Some(Encoding)` if `val` is an `Encoding`, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{encoding::Encoding, eval};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(Encoding::from_value(eval("Encoding::US_ASCII").unwrap()).is_some());
    /// assert!(Encoding::from_value(eval("nil").unwrap()).is_none());
    /// ```
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            val.is_kind_of(Ruby::get_with(val).class_encoding())
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    /// Returns the default internal encoding as a Ruby object.
    ///
    /// This is the encoding used for anything out-of-process, such as reading
    /// from files or sockets.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread. See
    /// [`Ruby::enc_default_external`] for the non-panicking version.
    #[deprecated(note = "please use `Ruby::enc_default_external` instead")]
    #[cfg(feature = "old-api")]
    #[cfg_attr(docsrs, doc(cfg(feature = "old-api")))]
    #[inline]
    pub fn default_external() -> Self {
        get_ruby!().enc_default_external()
    }

    /// Returns the default external encoding as a Ruby object.
    ///
    /// If set, any out-of-process data is transcoded from the default external
    /// encoding to the default internal encoding.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread. See
    /// [`Ruby::enc_default_internal`] for the non-panicking version.
    #[deprecated(note = "please use `Ruby::enc_default_internal` instead")]
    #[cfg(feature = "old-api")]
    #[cfg_attr(docsrs, doc(cfg(feature = "old-api")))]
    #[inline]
    pub fn default_internal() -> Option<Self> {
        get_ruby!().enc_default_internal()
    }
}

impl fmt::Display for Encoding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for Encoding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl From<Encoding> for Index {
    fn from(val: Encoding) -> Self {
        let i = unsafe { rb_to_encoding_index(val.as_rb_value()) };
        if i == -1 {
            panic!("got encoding index -1");
        }
        Index(i)
    }
}

impl From<Encoding> for RbEncoding {
    fn from(val: Encoding) -> Self {
        let ptr = unsafe { rb_find_encoding(val.as_rb_value()) };
        RbEncoding::new(ptr).expect("got NULL rb_encoding")
    }
}

impl IntoValue for Encoding {
    #[inline]
    fn into_value_with(self, _: &Ruby) -> Value {
        self.0.get()
    }
}

impl Object for Encoding {}

unsafe impl private::ReprValue for Encoding {}

impl ReprValue for Encoding {}

impl TryConvert for Encoding {
    fn try_convert(val: Value) -> Result<Self, Error> {
        if let Some(enc) = Self::from_value(val) {
            return Ok(enc);
        }
        RbEncoding::try_convert(val).map(Into::into)
    }
}

/// # `RbEncoding`
///
/// Functions to access pre-defined encodings.
///
/// See also the [`RbEncoding`] type.
impl Ruby {
    /// Returns the encoding that represents ASCII-8BIT a.k.a. binary.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     assert_eq!(ruby.ascii8bit_encoding().name(), "ASCII-8BIT");
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn ascii8bit_encoding(&self) -> RbEncoding {
        RbEncoding::new(unsafe { rb_ascii8bit_encoding() }).unwrap()
    }

    /// Returns the encoding that represents UTF-8.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     assert_eq!(ruby.utf8_encoding().name(), "UTF-8");
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn utf8_encoding(&self) -> RbEncoding {
        RbEncoding::new(unsafe { rb_utf8_encoding() }).unwrap()
    }

    /// Returns the encoding that represents US-ASCII.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     assert_eq!(ruby.usascii_encoding().name(), "US-ASCII");
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn usascii_encoding(&self) -> RbEncoding {
        RbEncoding::new(unsafe { rb_usascii_encoding() }).unwrap()
    }

    /// Returns the encoding that represents the process' current locale.
    ///
    /// This is dynamic. If you change the process' locale that should also
    /// change the return value of this function.
    pub fn locale_encoding(&self) -> RbEncoding {
        RbEncoding::new(unsafe { rb_locale_encoding() }).unwrap()
    }

    /// Returns the filesystem encoding.
    ///
    /// This is the encoding that Ruby expects data from the OS' file system
    /// to be encoded as, such as directory names.
    pub fn filesystem_encoding(&self) -> RbEncoding {
        RbEncoding::new(unsafe { rb_filesystem_encoding() }).unwrap()
    }

    /// Returns the default external encoding.
    ///
    /// This is the encoding used for anything out-of-process, such as reading
    /// from files or sockets.
    pub fn default_external_encoding(&self) -> RbEncoding {
        RbEncoding::new(unsafe { rb_default_external_encoding() }).unwrap()
    }

    /// Returns the default internal encoding.
    ///
    /// If set, any out-of-process data is transcoded from the default external
    /// encoding to the default internal encoding.
    pub fn default_internal_encoding(&self) -> Option<RbEncoding> {
        RbEncoding::new(unsafe { rb_default_internal_encoding() })
    }

    /// Returns the encoding with the name or alias `name`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     assert_eq!(ruby.find_encoding("BINARY").unwrap().name(), "ASCII-8BIT");
    ///     assert_eq!(ruby.find_encoding("UTF-8").unwrap().name(), "UTF-8");
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn find_encoding(&self, name: &str) -> Option<RbEncoding> {
        let name = CString::new(name).unwrap();
        let ptr = unsafe { rb_enc_find(name.as_ptr()) };
        RbEncoding::new(ptr)
    }
}

/// Ruby's internal encoding type.
///
/// This type contains the data for an encoding, and is used with operations
/// such as converting a string from one encoding to another, or reading a
/// string character by character.
///
/// See [`Ruby`](Ruby#rbencoding) for methods to get an `RbEncoding`.
#[repr(transparent)]
pub struct RbEncoding(NonNull<rb_encoding>);

impl RbEncoding {
    pub(crate) fn new(inner: *mut rb_encoding) -> Option<Self> {
        NonNull::new(inner).map(Self)
    }

    fn ruby(&self) -> Ruby {
        // self can only be created on a Ruby thread, and can't be
        // sent/referenced across threads, so we must be on a Ruby thread, so
        // this is safe
        unsafe { Ruby::get_unchecked() }
    }

    /// Returns the encoding that represents ASCII-8BIT a.k.a. binary.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread. See
    /// [`Ruby::ascii8bit_encoding`] for the non-panicking version.
    #[deprecated(note = "please use `Ruby::ascii8bit_encoding` instead")]
    #[cfg(feature = "old-api")]
    #[cfg_attr(docsrs, doc(cfg(feature = "old-api")))]
    #[inline]
    pub fn ascii8bit() -> Self {
        get_ruby!().ascii8bit_encoding()
    }

    /// Returns the encoding that represents UTF-8.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread. See [`Ruby::utf8_encoding`]
    /// for the non-panicking version.
    #[deprecated(note = "please use `Ruby::utf8_encoding` instead")]
    #[cfg(feature = "old-api")]
    #[cfg_attr(docsrs, doc(cfg(feature = "old-api")))]
    #[inline]
    pub fn utf8() -> Self {
        get_ruby!().utf8_encoding()
    }

    /// Returns the encoding that represents US-ASCII.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread. See [`Ruby::usascii_encoding`]
    /// for the non-panicking version.
    #[deprecated(note = "please use `Ruby::usascii_encoding` instead")]
    #[cfg(feature = "old-api")]
    #[cfg_attr(docsrs, doc(cfg(feature = "old-api")))]
    #[inline]
    pub fn usascii() -> Self {
        get_ruby!().usascii_encoding()
    }

    /// Returns the encoding that represents the process' current locale.
    ///
    /// This is dynamic. If you change the process' locale that should also
    /// change the return value of this function.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread. See [`Ruby::locale_encoding`]
    /// for the non-panicking version.
    #[deprecated(note = "please use `Ruby::locale_encoding` instead")]
    #[cfg(feature = "old-api")]
    #[cfg_attr(docsrs, doc(cfg(feature = "old-api")))]
    #[inline]
    pub fn locale() -> Self {
        get_ruby!().locale_encoding()
    }

    /// Returns the filesystem encoding.
    ///
    /// This is the encoding that Ruby expects data from the OS' file system
    /// to be encoded as, such as directory names.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread. See
    /// [`Ruby::filesystem_encoding`] for the non-panicking version.
    #[deprecated(note = "please use `Ruby::filesystem_encoding` instead")]
    #[cfg(feature = "old-api")]
    #[cfg_attr(docsrs, doc(cfg(feature = "old-api")))]
    #[inline]
    pub fn filesystem() -> Self {
        get_ruby!().filesystem_encoding()
    }

    /// Returns the default external encoding.
    ///
    /// This is the encoding used for anything out-of-process, such as reading
    /// from files or sockets.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread. See
    /// [`Ruby::default_external_encoding`] for the non-panicking version.
    #[deprecated(note = "please use `Ruby::default_external_encoding` instead")]
    #[cfg(feature = "old-api")]
    #[cfg_attr(docsrs, doc(cfg(feature = "old-api")))]
    #[inline]
    pub fn default_external() -> Self {
        get_ruby!().default_external_encoding()
    }

    /// Returns the default internal encoding.
    ///
    /// If set, any out-of-process data is transcoded from the default external
    /// encoding to the default internal encoding.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread. See
    /// [`Ruby::default_internal_encoding`] for the non-panicking version.
    #[deprecated(note = "please use `Ruby::default_internal_encoding` instead")]
    #[cfg(feature = "old-api")]
    #[cfg_attr(docsrs, doc(cfg(feature = "old-api")))]
    #[inline]
    pub fn default_internal() -> Option<Self> {
        get_ruby!().default_internal_encoding()
    }

    /// Returns the encoding with the name or alias `name`.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread. See [`Ruby::find_encoding`]
    /// for the non-panicking version.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(deprecated)]
    /// use magnus::encoding::RbEncoding;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert_eq!(RbEncoding::find("UTF-8").unwrap().name(), "UTF-8");
    /// assert_eq!(RbEncoding::find("BINARY").unwrap().name(), "ASCII-8BIT");
    /// ```
    #[deprecated(note = "please use `Ruby::find_encoding` instead")]
    #[cfg(feature = "old-api")]
    #[cfg_attr(docsrs, doc(cfg(feature = "old-api")))]
    #[inline]
    pub fn find(name: &str) -> Option<Self> {
        get_ruby!().find_encoding(name)
    }

    pub(crate) fn as_ptr(&self) -> *mut rb_encoding {
        self.0.as_ptr()
    }

    /// Returns the canonical name of the encoding.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     assert_eq!(ruby.utf8_encoding().name(), "UTF-8");
    ///     assert_eq!(ruby.find_encoding("UTF-16").unwrap().name(), "UTF-16");
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the name is not valid UTF-8. Encoding names are expected to
    /// be ASCII only.
    pub fn name(&self) -> &str {
        unsafe { CStr::from_ptr(self.0.as_ref().name).to_str().unwrap() }
    }

    /// Returns the minimum number of bytes the encoding needs to represent a
    /// single character.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     assert_eq!(ruby.usascii_encoding().mbminlen(), 1);
    ///     assert_eq!(ruby.utf8_encoding().mbminlen(), 1);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn mbminlen(&self) -> usize {
        unsafe { self.0.as_ref().min_enc_len as usize }
    }

    /// Returns the maximum number of bytes the encoding may need to represent
    /// a single character.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     assert_eq!(ruby.usascii_encoding().mbmaxlen(), 1);
    ///     assert_eq!(ruby.utf8_encoding().mbmaxlen(), 4);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn mbmaxlen(&self) -> usize {
        unsafe { self.0.as_ref().max_enc_len as usize }
    }

    /// Returns the number of bytes of the first character in `slice`.
    ///
    /// If the first byte of `slice` is mid way through a character this will
    /// return the number of bytes until the next character boundry.
    ///
    /// If the slice ends before the last byte of the character this will
    /// return the number of bytes until the end of the slice.
    ///
    /// See also [`fast_mbclen`](RbEncoding::fast_mbclen) and
    /// [`precise_mbclen`](RbEncoding::precise_mbclen).
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{
    ///     Error, Ruby,
    ///     encoding::{EncodingCapable, RbEncoding},
    /// };
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let s = ruby.str_new("🦀 café");
    ///     let encoding: RbEncoding = s.enc_get().into();
    ///     let mut chars = 0;
    ///
    ///     unsafe {
    ///         let mut bytes = s.as_slice();
    ///         assert_eq!(bytes.len(), 10);
    ///
    ///         while !bytes.is_empty() {
    ///             chars += 1;
    ///             let len = encoding.mbclen(bytes);
    ///             bytes = &bytes[len..];
    ///         }
    ///     }
    ///
    ///     assert_eq!(chars, 6);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn mbclen(&self, slice: &[u8]) -> usize {
        let Range { start: p, end: e } = slice.as_ptr_range();
        unsafe { rb_enc_mbclen(p as *const c_char, e as *const c_char, self.as_ptr()) as usize }
    }

    /// Returns the number of bytes of the first character in `slice`.
    ///
    /// If the first byte of `slice` is mid way through a character this will
    /// return the number of bytes until the next character boundary.
    ///
    /// If the slice ends before the last byte of the character this will
    /// return the theoretical number of bytes until the end of the character,
    /// which will be past the end of the slice. If the string has been read
    /// from an IO source this may indicate more data needs to be read.
    ///
    /// See also [`mbclen`](RbEncoding::mbclen) and
    /// [`precise_mbclen`](RbEncoding::precise_mbclen).
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{
    ///     Error, Ruby,
    ///     encoding::{EncodingCapable, RbEncoding},
    /// };
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let s = ruby.str_new("🦀 café");
    ///     let encoding: RbEncoding = s.enc_get().into();
    ///     let mut chars = 0;
    ///
    ///     unsafe {
    ///         let mut bytes = s.as_slice();
    ///         assert_eq!(bytes.len(), 10);
    ///
    ///         while !bytes.is_empty() {
    ///             chars += 1;
    ///             let len = encoding.fast_mbclen(bytes);
    ///             bytes = &bytes[len..];
    ///         }
    ///     }
    ///
    ///     assert_eq!(chars, 6);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn fast_mbclen(&self, slice: &[u8]) -> usize {
        let Range { start: p, end: e } = slice.as_ptr_range();
        unsafe {
            rb_enc_fast_mbclen(p as *const c_char, e as *const c_char, self.as_ptr()) as usize
        }
    }

    /// Returns the number of bytes of the first character in `slice`.
    ///
    /// See also [`mbclen`](RbEncoding::mbclen) and
    /// [`fast_mbclen`](RbEncoding::fast_mbclen).
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{
    ///     Error, Ruby,
    ///     encoding::{EncodingCapable, MbcLen, RbEncoding},
    /// };
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let s = ruby.str_new("🦀 café");
    ///     let encoding: RbEncoding = s.enc_get().into();
    ///     let mut chars = 0;
    ///
    ///     unsafe {
    ///         let mut bytes = s.as_slice();
    ///         assert_eq!(bytes.len(), 10);
    ///
    ///         while !bytes.is_empty() {
    ///             chars += 1;
    ///             match encoding.precise_mbclen(bytes) {
    ///                 MbcLen::CharFound(len) => bytes = &bytes[len..],
    ///                 MbcLen::NeedMore(len) => panic!("Met end of string expecting {} bytes", len),
    ///                 MbcLen::Invalid => panic!("corrupted string"),
    ///             }
    ///         }
    ///     }
    ///
    ///     assert_eq!(chars, 6);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn precise_mbclen(&self, slice: &[u8]) -> MbcLen {
        let Range { start: p, end: e } = slice.as_ptr_range();
        let r =
            unsafe { rb_enc_precise_mbclen(p as *const c_char, e as *const c_char, self.as_ptr()) };
        if 0 < r {
            MbcLen::CharFound(r as usize)
        } else if r < -1 {
            MbcLen::NeedMore((-1 - r) as usize)
        } else if r == -1 {
            MbcLen::Invalid
        } else {
            unreachable!()
        }
    }

    /// If the first character in `slice` is included in ASCII return it and
    /// its encoded length in `slice`, otherwise returns None.
    ///
    /// Typically the length will be 1, but some encodings such as UTF-16 will
    /// encode ASCII characters in 2 bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{
    ///     Error, Ruby,
    ///     encoding::{EncodingCapable, RbEncoding},
    /// };
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let s = ruby.str_new("example");
    ///     let encoding: RbEncoding = s.enc_get().into();
    ///     let mut chars = Vec::new();
    ///
    ///     unsafe {
    ///         let mut bytes = s.as_slice();
    ///
    ///         while !bytes.is_empty() {
    ///             match encoding.ascget(bytes) {
    ///                 Some((char, len)) => {
    ///                     chars.push(char);
    ///                     bytes = &bytes[len..];
    ///                 }
    ///                 None => panic!("string not ASCII"),
    ///             }
    ///         }
    ///     }
    ///
    ///     assert_eq!(chars, [101, 120, 97, 109, 112, 108, 101]);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn ascget(&self, slice: &[u8]) -> Option<(u8, usize)> {
        let Range { start: p, end: e } = slice.as_ptr_range();
        let mut len = 0;
        let c = unsafe {
            rb_enc_ascget(
                p as *const c_char,
                e as *const c_char,
                &mut len as *mut _,
                self.as_ptr(),
            )
        };
        if len == 0 {
            panic!("{:?}", slice);
        }
        (c > -1).then_some((c as u8, len as usize))
    }

    /// Returns the codepoint and length in bytes of the first character in
    /// `slice`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{
    ///     Error, Ruby,
    ///     encoding::{EncodingCapable, RbEncoding},
    /// };
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let s = ruby.str_new("🦀 café");
    ///     let encoding: RbEncoding = s.enc_get().into();
    ///     let mut codepoints = Vec::new();
    ///
    ///     unsafe {
    ///         let mut bytes = s.as_slice();
    ///
    ///         while !bytes.is_empty() {
    ///             let (codepoint, len) = encoding.codepoint_len(bytes)?;
    ///             codepoints.push(codepoint);
    ///             bytes = &bytes[len..];
    ///         }
    ///     }
    ///
    ///     assert_eq!(codepoints, [129408, 32, 99, 97, 102, 233]);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn codepoint_len(&self, slice: &[u8]) -> Result<(u32, usize), Error> {
        let Range { start: p, end: e } = slice.as_ptr_range();
        let mut len = 0;
        let mut c = 0;
        protect(|| unsafe {
            c = rb_enc_codepoint_len(
                p as *const c_char,
                e as *const c_char,
                &mut len as *mut _,
                self.as_ptr(),
            );
            self.ruby().qnil()
        })?;
        Ok((c, len as usize))
    }

    /// Returns the number of bytes required to represent the code point `code`
    /// in the encoding of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     assert_eq!(ruby.utf8_encoding().codelen(97)?, 1);
    ///     assert_eq!(ruby.utf8_encoding().codelen(129408)?, 4);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn codelen(&self, code: u32) -> Result<usize, Error> {
        let handle = self.ruby();
        let code = code
            .try_into()
            .map_err(|e: <usize as TryInto<c_int>>::Error| {
                Error::new(handle.exception_arg_error(), e.to_string())
            })?;
        let mut len = 0;
        protect(|| {
            unsafe { len = rb_enc_codelen(code, self.as_ptr()) as usize };
            handle.qnil()
        })?;
        Ok(len)
    }

    /// Encode the codepoint `code` as a series of bytes in the encoding `self`
    /// and return the result as a Ruby string.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby, eval};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let c = ruby.usascii_encoding().chr(97)?;
    ///     let res: bool = eval!(ruby, r#"c == "a""#, c)?;
    ///     assert!(res);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    ///
    /// ```
    /// use magnus::{Error, Ruby, eval};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let c = ruby.utf8_encoding().chr(129408)?;
    ///     let res: bool = eval!(ruby, r#"c == "🦀""#, c)?;
    ///     assert!(res);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn chr(&self, code: u32) -> Result<RString, Error> {
        protect(|| unsafe {
            RString::from_rb_value_unchecked(rb_enc_uint_chr(code, self.as_ptr()))
        })
    }

    /// Returns `true` if the first character in `slice` is a newline in the
    /// encoding `self`, `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     assert!(ruby.utf8_encoding().is_mbc_newline(&[10]));
    ///     assert!(!ruby.utf8_encoding().is_mbc_newline(&[32]));
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn is_mbc_newline(&self, slice: &[u8]) -> bool {
        let Range { start: p, end: e } = slice.as_ptr_range();
        unsafe {
            self.0.as_ref().is_mbc_newline.unwrap()(p as *const _, e as *const _, self.as_ptr())
                != 0
        }
    }

    /// Returns whether the given codepoint `code` is of the character type
    /// `ctype` in the encoding `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby, encoding::CType};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     assert!(ruby.utf8_encoding().is_code_ctype(9, CType::Space)); // "\t"
    ///     assert!(ruby.utf8_encoding().is_code_ctype(32, CType::Space)); // " "
    ///     assert!(!ruby.utf8_encoding().is_code_ctype(65, CType::Space)); // "A"
    ///     assert!(ruby.utf8_encoding().is_code_ctype(65, CType::Alnum)); // "A"
    ///     assert!(ruby.utf8_encoding().is_code_ctype(65, CType::Upper)); // "A"
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn is_code_ctype(&self, code: u32, ctype: CType) -> bool {
        unsafe { self.0.as_ref().is_code_ctype.unwrap()(code, ctype as _, self.as_ptr()) != 0 }
    }
}

/// Return value for [`RbEncoding::precise_mbclen`].
pub enum MbcLen {
    /// Found a valid char, value is the char's length.
    CharFound(usize),
    /// The slice ended before the end of the current char. Value is the
    /// theoretical total length of the char.
    NeedMore(usize),
    /// The bytes at the start of the slice are not valid for the encoding.
    Invalid,
}

/// A character type.
#[repr(u32)]
#[derive(Debug, Copy, Clone)]
pub enum CType {
    /// Newline.
    Newline = 0,
    /// Alphabetical.
    Alpha = 1,
    /// Blank.
    Blank = 2,
    /// Control.
    Cntrl = 3,
    /// Digit.
    Digit = 4,
    /// Graph.
    Graph = 5,
    /// Lowercase.
    Lower = 6,
    /// Printable.
    Print = 7,
    /// Punctuation.
    Punct = 8,
    /// Whitespace.
    Space = 9,
    /// Uppercase.
    Upper = 10,
    /// Xdigit.
    Xdigit = 11,
    /// Word.
    Word = 12,
    /// Alphanumeric.
    Alnum = 13,
    /// ASCII.
    Ascii = 14,
}

impl From<RbEncoding> for Encoding {
    fn from(val: RbEncoding) -> Self {
        Encoding::from_value(Value::new(unsafe { rb_enc_from_encoding(val.as_ptr()) })).unwrap()
    }
}

impl From<RbEncoding> for Index {
    fn from(val: RbEncoding) -> Self {
        Index(unsafe { rb_enc_to_index(val.as_ptr()) })
    }
}

impl IntoValue for RbEncoding {
    #[inline]
    fn into_value_with(self, handle: &Ruby) -> Value {
        Encoding::from(self).into_value_with(handle)
    }
}

impl TryConvert for RbEncoding {
    fn try_convert(val: Value) -> Result<Self, Error> {
        let mut ptr = ptr::null_mut();
        protect(|| unsafe {
            ptr = rb_to_encoding(val.as_rb_value());
            Ruby::get_with(val).qnil()
        })?;
        Ok(Self::new(ptr).unwrap())
    }
}

/// # Encoding Index
///
/// Functions to access pre-defined encodings.
///
/// See also the [`encoding::Index`](Index) type.
impl Ruby {
    /// Returns the index for ASCII-8BIT a.k.a. binary.
    pub fn ascii8bit_encindex(&self) -> Index {
        Index(unsafe { rb_ascii8bit_encindex() })
    }

    /// Returns the index for UTF-8.
    pub fn utf8_encindex(&self) -> Index {
        Index(unsafe { rb_utf8_encindex() })
    }

    /// Returns the index for US-ASCII.
    pub fn usascii_encindex(&self) -> Index {
        Index(unsafe { rb_usascii_encindex() })
    }

    /// Returns the index for the process' current locale encoding.
    ///
    /// This is dynamic. If you change the process' locale that should also
    /// change the return value of this function.
    pub fn locale_encindex(&self) -> Index {
        Index(unsafe { rb_locale_encindex() })
    }

    /// Returns the index for filesystem encoding.
    ///
    /// This is the encoding that Ruby expects data from the OS' file system
    /// to be encoded as, such as directory names.
    pub fn filesystem_encindex(&self) -> Index {
        Index(unsafe { rb_filesystem_encindex() })
    }

    /// Returns the index for the encoding with the name or alias `name`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     assert!(ruby.find_encindex("UTF-8").is_ok());
    ///     assert!(ruby.find_encindex("BINARY").is_ok());
    ///     assert!(ruby.find_encindex("none").is_err());
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn find_encindex(&self, name: &str) -> Result<Index, Error> {
        let name = CString::new(name).unwrap();
        let mut i = 0;
        protect(|| {
            unsafe { i = rb_enc_find_index(name.as_ptr()) };
            self.qnil()
        })?;
        if i == -1 {
            return Err(Error::new(
                self.exception_runtime_error(),
                format!("Encoding {:?} exists, but can not be loaded", name),
            ));
        }
        Ok(Index(i))
    }
}

/// The index of an encoding in Ruby's internal encodings table.
///
/// This is the type Ruby uses to label encoding capable types, so is used with
/// operations that require reading or setting that label.
///
/// See [`Ruby`](Ruby#encoding-index) for methods to get an `encoding::Index`.
#[derive(Clone, Copy, Eq, PartialEq)]
#[repr(transparent)]
pub struct Index(c_int);

impl Index {
    /// Returns the index for ASCII-8BIT a.k.a. binary.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread. See
    /// [`Ruby::ascii8bit_encindex`] for the non-panicking version.
    #[deprecated(note = "please use `Ruby::ascii8bit_encindex` instead")]
    #[cfg(feature = "old-api")]
    #[cfg_attr(docsrs, doc(cfg(feature = "old-api")))]
    #[inline]
    pub fn ascii8bit() -> Self {
        get_ruby!().ascii8bit_encindex()
    }

    /// Returns the index for UTF-8.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread. See [`Ruby::utf8_encindex`]
    /// for the non-panicking version.
    #[deprecated(note = "please use `Ruby::utf8_encindex` instead")]
    #[cfg(feature = "old-api")]
    #[cfg_attr(docsrs, doc(cfg(feature = "old-api")))]
    #[inline]
    pub fn utf8() -> Self {
        get_ruby!().utf8_encindex()
    }

    /// Returns the index for US-ASCII.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread. See [`Ruby::usascii_encindex`]
    /// for the non-panicking version.
    #[deprecated(note = "please use `Ruby::usascii_encindex` instead")]
    #[cfg(feature = "old-api")]
    #[cfg_attr(docsrs, doc(cfg(feature = "old-api")))]
    #[inline]
    pub fn usascii() -> Self {
        get_ruby!().usascii_encindex()
    }

    /// Returns the index for the process' current locale encoding.
    ///
    /// This is dynamic. If you change the process' locale that should also
    /// change the return value of this function.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread. See [`Ruby::locale_encindex`]
    /// for the non-panicking version.
    #[deprecated(note = "please use `Ruby::locale_encindex` instead")]
    #[cfg(feature = "old-api")]
    #[cfg_attr(docsrs, doc(cfg(feature = "old-api")))]
    #[inline]
    pub fn locale() -> Self {
        get_ruby!().locale_encindex()
    }

    /// Returns the index for filesystem encoding.
    ///
    /// This is the encoding that Ruby expects data from the OS' file system
    /// to be encoded as, such as directory names.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread. See
    /// [`Ruby::filesystem_encindex`] for the non-panicking version.
    #[deprecated(note = "please use `Ruby::filesystem_encindex` instead")]
    #[cfg(feature = "old-api")]
    #[cfg_attr(docsrs, doc(cfg(feature = "old-api")))]
    #[inline]
    pub fn filesystem() -> Self {
        get_ruby!().filesystem_encindex()
    }

    /// Returns the index for the encoding with the name or alias `name`.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread. See [`Ruby::find_encindex`]
    /// for the non-panicking version.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(deprecated)]
    /// use magnus::encoding;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(encoding::Index::find("UTF-8").is_ok());
    /// assert!(encoding::Index::find("BINARY").is_ok());
    /// assert!(encoding::Index::find("none").is_err());
    /// ```
    #[deprecated(note = "please use `Ruby::find_encindex` instead")]
    #[cfg(feature = "old-api")]
    #[cfg_attr(docsrs, doc(cfg(feature = "old-api")))]
    #[inline]
    pub fn find(name: &str) -> Result<Self, Error> {
        get_ruby!().find_encindex(name)
    }

    pub(crate) fn to_int(self) -> c_int {
        self.0
    }
}

impl From<Index> for RbEncoding {
    fn from(val: Index) -> Self {
        RbEncoding::new(unsafe { rb_enc_from_index(val.to_int()) }).expect("no encoding for index")
    }
}

impl TryConvert for Index {
    fn try_convert(val: Value) -> Result<Self, Error> {
        let i = unsafe { rb_to_encoding_index(val.as_rb_value()) };
        if i == -1 && RString::from_value(val).is_some() {
            return Err(Error::new(
                Ruby::get_with(val).exception_runtime_error(),
                format!("ArgumentError: unknown encoding name - {}", val),
            ));
        } else if i == -1 {
            return TryConvert::try_convert(RString::try_convert(val)?.as_value());
        }
        Ok(Index(i))
    }
}

/// Possible states of how a string matches its encoding.
#[repr(u32)]
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum Coderange {
    /// It is unknown if the string is valid for its encoding.
    Unknown = 0,
    /// The string is entirely within the 0 to 127 ASCII range.
    SevenBit = 1048576,
    /// The string is valid for its encoding.
    Valid = 2097152,
    /// The string holds values that are invalid for its encoding.
    Broken = 3145728,
}

/// Trait that marks Ruby types cable of having an encoding.
pub trait EncodingCapable: ReprValue + Copy {
    /// Get the encoding of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby, encoding::EncodingCapable};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     assert!(ruby.str_new("example").enc_get() == ruby.utf8_encindex());
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    fn enc_get(self) -> Index {
        let i = unsafe { rb_enc_get_index(self.as_rb_value()) };
        if i == -1 {
            panic!("{} not encoding capable", self.as_value());
        }
        Index(i)
    }

    /// Set `self`'s encoding.
    ///
    /// Returns `Err` if `self` is frozen or the encoding can not be loaded.
    ///
    /// See also [`EncodingCapable::enc_associate`].
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby, encoding::EncodingCapable};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let s = ruby.str_new("example");
    ///     assert!(s.enc_get() == ruby.utf8_encindex());
    ///     s.enc_set(ruby.usascii_encindex())?;
    ///     assert!(s.enc_get() == ruby.usascii_encindex());
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    fn enc_set<T>(self, enc: T) -> Result<(), Error>
    where
        T: Into<Index>,
    {
        protect(|| unsafe {
            rb_enc_set_index(self.as_rb_value(), enc.into().to_int());
            Ruby::get_with(self).qnil()
        })?;
        Ok(())
    }

    /// Set `self`'s encoding, along with performing additional fix-up `self`'s
    /// contents.
    ///
    /// For example, Ruby's strings contain an additional terminating null byte
    /// hidden from Ruby, but allowing for easy c string interop. This method
    /// will adjust the length of that terminating char depending on the
    /// encoding.
    ///
    /// Returns `Err` if `self` is frozen or the encoding can not be loaded.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby, encoding::EncodingCapable};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let s = ruby.str_new("example");
    ///     assert!(s.enc_get() == ruby.utf8_encindex());
    ///     s.enc_associate(ruby.usascii_encindex())?;
    ///     assert!(s.enc_get() == ruby.usascii_encindex());
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    fn enc_associate<T>(self, enc: T) -> Result<(), Error>
    where
        T: Into<Index>,
    {
        protect(|| {
            Value::new(unsafe { rb_enc_associate_index(self.as_rb_value(), enc.into().to_int()) })
        })?;
        Ok(())
    }
}

/// Returns the common encoding between `v1` and `v2`, or `None`.
///
/// Returns `None` if there is no common compatible encoding.
///
/// See also [`check`].
///
/// # Examples
///
/// ```
/// use magnus::{Error, Ruby, encoding, prelude::*};
///
/// fn example(ruby: &Ruby) -> Result<(), Error> {
///     let a = ruby.str_new("a");
///     let b = ruby.str_new("b");
///
///     assert!(a.enc_get() == ruby.utf8_encindex());
///     b.enc_set(ruby.usascii_encindex())?;
///
///     assert_eq!(encoding::compatible(a, b).unwrap().name(), "UTF-8");
///
///     Ok(())
/// }
/// # Ruby::init(example).unwrap()
/// ```
pub fn compatible<T, U>(v1: T, v2: U) -> Option<RbEncoding>
where
    T: EncodingCapable,
    U: EncodingCapable,
{
    RbEncoding::new(unsafe { rb_enc_compatible(v1.as_rb_value(), v2.as_rb_value()) })
}

/// Returns the common encoding between `v1` and `v2`, or `Err`.
///
/// Returns `Err` if there is no common compatible encoding.
///
/// See also [`compatible`].
///
/// # Examples
///
/// ```
/// use magnus::{Error, Ruby, encoding, prelude::*};
///
/// fn example(ruby: &Ruby) -> Result<(), Error> {
///     let a = ruby.str_new("a");
///     let b = ruby.str_new("b");
///
///     assert!(a.enc_get() == ruby.utf8_encindex());
///     b.enc_set(ruby.usascii_encindex())?;
///
///     assert_eq!(encoding::check(a, b)?.name(), "UTF-8");
///
///     Ok(())
/// }
/// # Ruby::init(example).unwrap()
/// ```
pub fn check<T, U>(v1: T, v2: U) -> Result<RbEncoding, Error>
where
    T: EncodingCapable,
    U: EncodingCapable,
{
    let mut ptr = ptr::null_mut();
    protect(|| unsafe {
        ptr = rb_enc_check(v1.as_rb_value(), v2.as_rb_value());
        Ruby::get_with(v1).qnil()
    })?;
    Ok(RbEncoding::new(ptr).unwrap())
}

/// Compies the encoding from `src` to `dst`.
///
/// This does not reconcode `dst.`
///
/// Similar to [`EncodingCapable::enc_associate`], except takes the encoding of
/// `src` rather than an encoding object or index.
///
/// # Examples
///
/// ```
/// use magnus::{Error, Ruby, encoding, prelude::*};
///
/// fn example(ruby: &Ruby) -> Result<(), Error> {
///     let a = ruby.str_new("a");
///     assert!(a.enc_get() == ruby.utf8_encindex());
///     let b = ruby.str_new("b");
///     assert!(b.enc_get() == ruby.utf8_encindex());
///
///     a.enc_set(ruby.usascii_encindex())?;
///     encoding::copy(b, a)?;
///
///     assert!(b.enc_get() == ruby.usascii_encindex());
///
///     Ok(())
/// }
/// # Ruby::init(example).unwrap()
/// ```
pub fn copy<T, U>(dst: T, src: U) -> Result<(), Error>
where
    T: EncodingCapable,
    U: EncodingCapable,
{
    protect(|| unsafe {
        rb_enc_copy(dst.as_rb_value(), src.as_rb_value());
        Ruby::get_with(dst).qnil()
    })?;
    Ok(())
}
