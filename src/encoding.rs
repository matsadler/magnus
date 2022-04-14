//! Types and functions for working with encodings.
//!
//! This module defines 3 types for working with encodings, these types can
//! be converted back and forth with [`From`]/[`Into`] like so:
//! ``` text
//! Encoding <-> RbEncoding <-> Index
//!       |______________________^
//! ```
//! Many functions that require an encoding take thier arguments as
//! `Into<RbEncoding>` or `Into<Index>` to ease working with the different
//! types. The type specified for the `Into` conversion hints at the type the
//! function nativly works with, and thus will avoid any conversion cost.
//!
//! [`Encoding`] and [`RbEncoding`] both implement [`TryConvert`] and
//! `Into<Value>` so can be used as parameters and return values in functions
//! bound to Ruby. Both convert from either an instance of `Encoding` or a
//! string of an encoding name, and convert to an instance of `Encoding`.

use std::{
    ffi::{CStr, CString},
    fmt,
    ops::Deref,
    os::raw::c_int,
    ptr::{self, NonNull},
};

use crate::{
    class,
    error::{protect, Error},
    exception,
    object::Object,
    r_string::RString,
    ruby_sys::{
        rb_ascii8bit_encindex, rb_ascii8bit_encoding, rb_default_external_encoding,
        rb_default_internal_encoding, rb_enc_associate_index, rb_enc_check, rb_enc_compatible,
        rb_enc_default_external, rb_enc_default_internal, rb_enc_find, rb_enc_find_index,
        rb_enc_from_encoding, rb_enc_from_index, rb_enc_get_index, rb_enc_set_index,
        rb_enc_to_index, rb_encoding, rb_filesystem_encindex, rb_filesystem_encoding,
        rb_find_encoding, rb_locale_encindex, rb_locale_encoding, rb_to_encoding,
        rb_to_encoding_index, rb_usascii_encindex, rb_usascii_encoding, rb_utf8_encindex,
        rb_utf8_encoding,
    },
    try_convert::TryConvert,
    value::{private, NonZeroValue, ReprValue, Value, QNIL},
};

/// Wrapper type for a Value known to be an instance of Ruby's Encoding class.
///
/// This is the representation of an encoding exposed to Ruby code.
///
/// All [`Value`] methods should be available on this type through [`Deref`],
/// but some may be missed by this documentation.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Encoding(NonZeroValue);

impl Encoding {
    /// Return `Some(Encoding)` if `val` is an `Encoding`, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, encoding::Encoding};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(Encoding::from_value(eval("Encoding::US_ASCII").unwrap()).is_some());
    /// assert!(Encoding::from_value(eval("nil").unwrap()).is_none());
    /// ```
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            val.is_kind_of(class::encoding())
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    /// Returns the default internal encoding as a Ruby object.
    ///
    /// This is the encoding used for anything out-of-process, such as reading
    /// from files or sockets.
    pub fn default_external() -> Self {
        Self::from_value(Value::new(unsafe { rb_enc_default_external() })).unwrap()
    }

    /// Returns the default external encoding as a Ruby object.
    ///
    /// If set, any out-of-process data is transcoded from the default external
    /// encoding to the default internal encoding.
    pub fn default_internal() -> Option<Self> {
        Self::from_value(Value::new(unsafe { rb_enc_default_internal() }))
    }
}

impl Deref for Encoding {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
    }
}

impl fmt::Display for Encoding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for Encoding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.deref().inspect())
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

impl From<Encoding> for Value {
    fn from(val: Encoding) -> Self {
        *val
    }
}

impl Object for Encoding {}

unsafe impl private::ReprValue for Encoding {
    fn to_value(self) -> Value {
        *self
    }

    unsafe fn from_value_unchecked(val: Value) -> Self {
        Self(NonZeroValue::new_unchecked(val))
    }
}

impl ReprValue for Encoding {}

impl TryConvert for Encoding {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        if let Some(enc) = Self::from_value(*val) {
            return Ok(enc);
        }
        RbEncoding::try_convert(val).map(Into::into)
    }
}

/// Ruby's internal encoding type.
///
/// This type contains the data for an encoding, and is used with operations
/// such as converting a string from one encoding to another, or reading a
/// string character by character.
#[repr(transparent)]
pub struct RbEncoding(NonNull<rb_encoding>);

impl RbEncoding {
    fn new(inner: *mut rb_encoding) -> Option<Self> {
        NonNull::new(inner).map(Self)
    }

    /// Returns the encoding that represents ASCII-8BIT a.k.a. binary.
    pub fn ascii8bit() -> Self {
        Self::new(unsafe { rb_ascii8bit_encoding() }).unwrap()
    }

    /// Returns the encoding that represents UTF-8.
    pub fn utf8() -> Self {
        Self::new(unsafe { rb_utf8_encoding() }).unwrap()
    }

    /// Returns the encoding that represents US-ASCII.
    pub fn usascii() -> Self {
        Self::new(unsafe { rb_usascii_encoding() }).unwrap()
    }

    /// Returns the encoding that represents the process' current locale.
    ///
    /// This is dynamic. If you change the process' locale that should also
    /// change the return value of this function.
    pub fn locale() -> Self {
        Self::new(unsafe { rb_locale_encoding() }).unwrap()
    }

    /// Returns the filesystem encoding.
    ///
    /// This is the encoding that Ruby expects data from the OS' file system
    /// to be encoded as, such as directory names.
    pub fn filesystem() -> Self {
        Self::new(unsafe { rb_filesystem_encoding() }).unwrap()
    }

    /// Returns the default external encoding.
    ///
    /// This is the encoding used for anything out-of-process, such as reading
    /// from files or sockets.
    pub fn default_external() -> Self {
        Self::new(unsafe { rb_default_external_encoding() }).unwrap()
    }

    /// Returns the default internal encoding.
    ///
    /// If set, any out-of-process data is transcoded from the default external
    /// encoding to the default internal encoding.
    pub fn default_internal() -> Option<Self> {
        Self::new(unsafe { rb_default_internal_encoding() })
    }

    /// Returns the encoding with the name or alias `name`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, encoding::RbEncoding};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert_eq!(RbEncoding::find("UTF-8").unwrap().name(), "UTF-8");
    /// assert_eq!(RbEncoding::find("BINARY").unwrap().name(), "ASCII-8BIT");
    /// ```
    pub fn find(name: &str) -> Option<Self> {
        let name = CString::new(name).unwrap();
        let ptr = unsafe { rb_enc_find(name.as_ptr()) };
        Self::new(ptr)
    }

    pub(crate) fn as_ptr(&self) -> *mut rb_encoding {
        self.0.as_ptr()
    }

    /// Returns the canonical name of the encoding.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, encoding::RbEncoding};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert_eq!(RbEncoding::utf8().name(), "UTF-8");
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
    /// use magnus::{eval, encoding::RbEncoding};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert_eq!(RbEncoding::utf8().mbminlen(), 1);
    /// assert_eq!(RbEncoding::find("UTF-16").unwrap().mbminlen(), 2);
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
    /// use magnus::{eval, encoding::RbEncoding};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert_eq!(RbEncoding::usascii().mbmaxlen(), 1);
    /// assert_eq!(RbEncoding::utf8().mbmaxlen(), 4);
    /// ```
    pub fn mbmaxlen(&self) -> usize {
        unsafe { self.0.as_ref().max_enc_len as usize }
    }
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

impl From<RbEncoding> for Value {
    fn from(val: RbEncoding) -> Self {
        *Encoding::from(val)
    }
}

impl TryConvert for RbEncoding {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        let mut ptr = ptr::null_mut();
        protect(|| {
            ptr = unsafe { rb_to_encoding(val.as_rb_value()) };
            *QNIL
        })?;
        Ok(Self::new(ptr).unwrap())
    }
}

/// The index of an encoding in Ruby's internal encodings table.
///
/// This is the type Ruby uses to label encoding capable types, so is used with
/// operations that require reading or setting that label.
#[derive(Clone, Copy, Eq, PartialEq)]
#[repr(transparent)]
pub struct Index(c_int);

impl Index {
    /// Returns the index for ASCII-8BIT a.k.a. binary.
    pub fn ascii8bit() -> Self {
        Self(unsafe { rb_ascii8bit_encindex() })
    }

    /// Returns the index for UTF-8.
    pub fn utf8() -> Self {
        Self(unsafe { rb_utf8_encindex() })
    }

    /// Returns the index for US-ASCII.
    pub fn usascii() -> Self {
        Self(unsafe { rb_usascii_encindex() })
    }

    /// Returns the index for the process' current locale encoding.
    ///
    /// This is dynamic. If you change the process' locale that should also
    /// change the return value of this function.
    pub fn locale() -> Self {
        Self(unsafe { rb_locale_encindex() })
    }

    /// Returns the index for filesystem encoding.
    ///
    /// This is the encoding that Ruby expects data from the OS' file system
    /// to be encoded as, such as directory names.
    pub fn filesystem() -> Self {
        Self(unsafe { rb_filesystem_encindex() })
    }

    /// Returns the index for the encoding with the name or alias `name`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, encoding};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(encoding::Index::find("UTF-8").is_ok());
    /// assert!(encoding::Index::find("BINARY").is_ok());
    /// assert!(encoding::Index::find("none").is_err());
    /// ```
    pub fn find(name: &str) -> Result<Self, Error> {
        let name = CString::new(name).unwrap();
        let mut i = 0;
        protect(|| {
            i = unsafe { rb_enc_find_index(name.as_ptr()) };
            *QNIL
        })?;
        if i == -1 {
            return Err(Error::new(
                exception::runtime_error(),
                format!("Encoding {:?} exists, but can not be loaded", name),
            ));
        }
        Ok(Index(i))
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
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        let i = unsafe { rb_to_encoding_index(val.as_rb_value()) };
        if i == -1 && RString::from_value(*val).is_some() {
            return Err(Error::new(
                exception::runtime_error(),
                format!("ArgumentError: unknown encoding name - {}", val),
            ));
        } else if i == -1 {
            return RString::try_convert(val)?.try_convert();
        }
        Ok(Index(i))
    }
}

/// Trait that marks Ruby types cable of having an encoding.
pub trait EncodingCapable: Deref<Target = Value> {
    /// Get the encoding of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{encoding::{self, EncodingCapable}, RString};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(RString::new("example").enc_get() == encoding::Index::utf8());
    /// ```
    fn enc_get(&self) -> Index {
        let i = unsafe { rb_enc_get_index(self.as_rb_value()) };
        if i == -1 {
            panic!("{} not encoding capable", self.deref());
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
    /// use magnus::{encoding::{self, EncodingCapable}, RString};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let s = RString::new("example");
    /// assert!(s.enc_get() == encoding::Index::utf8());
    /// s.enc_set(encoding::Index::usascii());
    /// assert!(s.enc_get() == encoding::Index::usascii());
    /// ```
    fn enc_set<T>(&self, enc: T) -> Result<(), Error>
    where
        T: Into<Index>,
    {
        protect(|| {
            unsafe { rb_enc_set_index(self.as_rb_value(), enc.into().to_int()) };
            *QNIL
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
    /// use magnus::{encoding::{self, EncodingCapable}, RString};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let s = RString::new("example");
    /// assert!(s.enc_get() == encoding::Index::utf8());
    /// s.enc_associate(encoding::Index::usascii());
    /// assert!(s.enc_get() == encoding::Index::usascii());
    /// ```
    fn enc_associate<T>(&self, enc: T) -> Result<(), Error>
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
/// use magnus::{encoding::{self, EncodingCapable}, RString};
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// let a = RString::new("a");
/// let b = RString::new("b");
///
/// assert!(a.enc_get() == encoding::Index::utf8());
/// b.enc_set(encoding::Index::usascii());
///
/// assert_eq!(encoding::compatible(a, b).unwrap().name(), "UTF-8");
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
/// use magnus::{encoding::{self, EncodingCapable}, RString};
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// let a = RString::new("a");
/// let b = RString::new("b");
///
/// assert!(a.enc_get() == encoding::Index::utf8());
/// b.enc_set(encoding::Index::usascii());
///
/// assert_eq!(encoding::check(a, b).unwrap().name(), "UTF-8");
/// ```
pub fn check<T, U>(v1: T, v2: U) -> Result<RbEncoding, Error>
where
    T: EncodingCapable,
    U: EncodingCapable,
{
    let mut ptr = ptr::null_mut();
    protect(|| {
        ptr = unsafe { rb_enc_check(v1.as_rb_value(), v2.as_rb_value()) };
        *QNIL
    })?;
    Ok(RbEncoding::new(ptr).unwrap())
}
