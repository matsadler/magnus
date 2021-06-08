use std::{
    borrow::Cow,
    ffi::CStr,
    fmt,
    ops::Deref,
    ptr::{self, NonNull},
    slice, str,
};

use crate::{
    debug_assert_value,
    error::{protect, Error},
    object::Object,
    ruby_sys::{
        self, rb_enc_get, rb_enc_get_index, rb_str_conv_enc, rb_str_to_str, rb_utf8_encindex,
        rb_utf8_encoding, ruby_rstring_consts, ruby_rstring_flags, ruby_value_type, VALUE,
    },
    try_convert::TryConvert,
    value::{NonZeroValue, Value},
};

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RString(NonZeroValue);

impl RString {
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

    /// # Safety
    ///
    /// Ruby may modify or free the memory backing the returned slice, the
    /// caller must ensure this does not happen.
    pub unsafe fn as_slice(&self) -> &[u8] {
        self.as_slice_unconstrained()
    }

    unsafe fn as_slice_unconstrained<'a>(self) -> &'a [u8] {
        debug_assert_value!(self);
        let r_basic = self.r_basic_unchecked();
        let mut f = r_basic.as_ref().flags;
        if (f & ruby_rstring_flags::RSTRING_NOEMBED as VALUE) != 0 {
            let h = self.as_internal().as_ref().as_.heap;
            slice::from_raw_parts(h.ptr as *const u8, h.len as usize)
        } else {
            f &= ruby_rstring_flags::RSTRING_EMBED_LEN_MASK as VALUE;
            f >>= ruby_rstring_consts::RSTRING_EMBED_LEN_SHIFT as VALUE;
            slice::from_raw_parts(
                &self.as_internal().as_ref().as_.ary as *const _ as *const u8,
                f as usize,
            )
        }
    }

    pub fn is_utf8_encoding(self) -> bool {
        unsafe { rb_enc_get_index(self.as_rb_value()) == rb_utf8_encindex() }
    }

    pub fn encode_utf8(self) -> Result<Self, Error> {
        unsafe {
            protect(|| {
                Value::new(rb_str_conv_enc(
                    self.as_rb_value(),
                    ptr::null_mut(),
                    rb_utf8_encoding(),
                ))
            })
            .map(|v| Self::from_rb_value_unchecked(v.as_rb_value()))
        }
    }

    /// # Safety
    ///
    /// Ruby may modify or free the memory backing the returned str, the caller
    /// must ensure this does not happen.
    pub unsafe fn as_str(&self) -> Result<&str, Error> {
        self.as_str_unconstrained()
    }

    pub(crate) unsafe fn as_str_unconstrained<'a>(self) -> Result<&'a str, Error> {
        if !self.is_utf8_encoding() {
            let enc = rb_enc_get(self.as_rb_value());
            let name = CStr::from_ptr((*enc).name).to_string_lossy();
            return Err(Error::encoding_error(format!(
                "expected utf-8, got {}",
                name
            )));
        }
        str::from_utf8(self.as_slice_unconstrained())
            .map_err(|e| Error::encoding_error(format!("{}", e)))
    }

    /// # Safety
    ///
    /// Ruby may modify or free the memory backing the returned str, the caller
    /// must ensure this does not happen.
    pub unsafe fn to_string_lossy(&self) -> Cow<'_, str> {
        String::from_utf8_lossy(self.as_slice())
    }

    pub fn to_string(self) -> Result<String, Error> {
        let utf8 = if self.is_utf8_encoding() {
            self
        } else {
            self.encode_utf8()?
        };
        str::from_utf8(unsafe { utf8.as_slice() })
            .map(ToOwned::to_owned)
            .map_err(|e| Error::encoding_error(format!("{}", e)))
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

impl From<RString> for Value {
    fn from(val: RString) -> Self {
        *val
    }
}

impl Object for RString {}

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
