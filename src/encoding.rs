//! Types and functions for working with encodings.

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
        rb_enc_copy, rb_enc_default_external, rb_enc_default_internal, rb_enc_find,
        rb_enc_find_index, rb_enc_from_encoding, rb_enc_from_index, rb_enc_get_index,
        rb_enc_set_index, rb_enc_to_index, rb_encoding, rb_filesystem_encindex,
        rb_filesystem_encoding, rb_find_encoding, rb_locale_encindex, rb_locale_encoding,
        rb_to_encoding, rb_to_encoding_index, rb_usascii_encindex, rb_usascii_encoding,
        rb_utf8_encindex, rb_utf8_encoding, VALUE,
    },
    try_convert::TryConvert,
    value::{private, NonZeroValue, ReprValue, Value, QNIL},
};

/// Wrapper type for a Value known to be an instance of Ruby's Encoding class.
///
/// All [`Value`] methods should be available on this type through [`Deref`],
/// but some may be missed by this documentation.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Encoding(NonZeroValue);

impl Encoding {
    /// Return `Some(Encoding)` if `val` is an `Encoding`, `None` otherwise.
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            val.is_kind_of(class::encoding())
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        Self(NonZeroValue::new_unchecked(Value::new(val)))
    }

    pub fn default_external() -> Self {
        unsafe { Self::from_rb_value_unchecked(rb_enc_default_external()) }
    }

    pub fn default_internal() -> Self {
        unsafe { Self::from_rb_value_unchecked(rb_enc_default_internal()) }
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

#[repr(transparent)]
pub struct RbEncoding(NonNull<rb_encoding>);

impl RbEncoding {
    fn new(inner: *mut rb_encoding) -> Option<Self> {
        NonNull::new(inner).map(Self)
    }

    pub fn ascii8bit() -> Self {
        Self::new(unsafe { rb_ascii8bit_encoding() }).unwrap()
    }

    pub fn utf8() -> Self {
        Self::new(unsafe { rb_utf8_encoding() }).unwrap()
    }

    pub fn usascii() -> Self {
        Self::new(unsafe { rb_usascii_encoding() }).unwrap()
    }

    pub fn locale() -> Self {
        Self::new(unsafe { rb_locale_encoding() }).unwrap()
    }

    pub fn filesystem() -> Self {
        Self::new(unsafe { rb_filesystem_encoding() }).unwrap()
    }

    pub fn default_external() -> Self {
        Self::new(unsafe { rb_default_external_encoding() }).unwrap()
    }

    pub fn default_internal() -> Self {
        Self::new(unsafe { rb_default_internal_encoding() }).unwrap()
    }

    pub fn find(name: &str) -> Option<Self> {
        let name = CString::new(name).unwrap();
        let ptr = unsafe { rb_enc_find(name.as_ptr()) };
        Self::new(ptr)
    }

    pub(crate) fn as_ptr(&self) -> *mut rb_encoding {
        self.0.as_ptr()
    }

    pub fn name(&self) -> &str {
        unsafe { CStr::from_ptr(self.0.as_ref().name).to_str().unwrap() }
    }

    pub fn mbminlen(&self) -> usize {
        unsafe { self.0.as_ref().min_enc_len as usize }
    }

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

#[derive(Clone, Copy, Eq, PartialEq)]
#[repr(transparent)]
pub struct Index(c_int);

impl Index {
    pub fn ascii8bit() -> Self {
        Self(unsafe { rb_ascii8bit_encindex() })
    }

    pub fn utf8() -> Self {
        Self(unsafe { rb_utf8_encindex() })
    }

    pub fn usascii() -> Self {
        Self(unsafe { rb_usascii_encindex() })
    }

    pub fn locale() -> Self {
        Self(unsafe { rb_locale_encindex() })
    }

    pub fn filesystem() -> Self {
        Self(unsafe { rb_filesystem_encindex() })
    }

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

pub trait EncodingCapable: Deref<Target = Value> {
    fn enc_get(&self) -> Index {
        let i = unsafe { rb_enc_get_index(self.as_rb_value()) };
        if i == -1 {
            panic!("{} not encoding capable", self.deref());
        }
        Index(i)
    }

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

pub fn compatible<T, U>(v1: T, v2: U) -> Option<RbEncoding>
where
    T: EncodingCapable,
    U: EncodingCapable,
{
    RbEncoding::new(unsafe { rb_enc_compatible(v1.as_rb_value(), v2.as_rb_value()) })
}

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

pub fn copy<T, U>(dst: T, src: U) -> Result<(), Error>
where
    T: EncodingCapable,
    U: EncodingCapable,
{
    protect(|| {
        unsafe { rb_enc_copy(dst.as_rb_value(), src.as_rb_value()) };
        *QNIL
    })?;
    Ok(())
}
