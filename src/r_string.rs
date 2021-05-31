use std::{
    borrow::Cow,
    ffi::CStr,
    fmt,
    mem::transmute,
    ops::Deref,
    ptr::{self, NonNull},
    slice, str,
};

use crate::{
    debug_assert_value,
    error::{protect, Error},
    object::Object,
    r_basic::RBasic,
    ruby_sys::{
        self, rb_enc_get, rb_enc_get_index, rb_str_conv_enc, rb_str_to_str, rb_utf8_encindex,
        rb_utf8_encoding, ruby_rstring_consts, ruby_rstring_flags, ruby_value_type, VALUE,
    },
    try_convert::TryConvert,
    value::Value,
};

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RString(pub(crate) VALUE);

impl RString {
    /// # Safety
    ///
    /// val must not have been GC'd, return value must be kept on stack or
    /// otherwise protected from the GC.
    pub unsafe fn from_value(val: &Value) -> Option<Self> {
        let r_basic = RBasic::from_value(val)?;
        (r_basic.builtin_type() == ruby_value_type::RUBY_T_STRING).then(|| Self(val.into_inner()))
    }

    pub(crate) unsafe fn ref_from_value(val: &Value) -> Option<&Self> {
        let r_basic = RBasic::from_value(val)?;
        (r_basic.builtin_type() == ruby_value_type::RUBY_T_STRING).then(|| transmute(val))
    }

    // TODO: use or remove
    #[allow(dead_code)]
    pub(crate) fn as_internal(&self) -> NonNull<ruby_sys::RString> {
        // safe as to get self we need to have gone through ::from_value()
        // where val is vaild as an RBasic, which rules out NULL
        unsafe { NonNull::new_unchecked(self.0 as *mut _) }
    }

    pub unsafe fn as_slice(&self) -> &[u8] {
        debug_assert_value!(self);
        let r_basic = RBasic::from_value(self).unwrap();
        let mut f = r_basic.flags();
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

    pub unsafe fn is_utf8_encoding(&self) -> bool {
        rb_enc_get_index(self.into_inner()) == rb_utf8_encindex()
    }

    pub unsafe fn encode_utf8(&self) -> Result<Self, Error> {
        protect(|| {
            Value::new(rb_str_conv_enc(
                self.into_inner(),
                ptr::null_mut(),
                rb_utf8_encoding(),
            ))
        })
        .map(|v| Self(v.into_inner()))
    }

    pub unsafe fn as_str(&self) -> Result<&str, Error> {
        if !self.is_utf8_encoding() {
            let enc = rb_enc_get(self.into_inner());
            let name = CStr::from_ptr((*enc).name).to_string_lossy();
            return Err(Error::encoding_error(format!(
                "expected utf-8, got {}",
                name
            )));
        }
        str::from_utf8(self.as_slice()).map_err(|e| Error::encoding_error(format!("{}", e)))
    }

    pub unsafe fn to_string_lossy(&self) -> Cow<'_, str> {
        String::from_utf8_lossy(self.as_slice())
    }

    pub unsafe fn to_string(&self) -> Result<String, Error> {
        let utf8 = if self.is_utf8_encoding() {
            *self
        } else {
            self.encode_utf8()?
        };
        str::from_utf8(utf8.as_slice())
            .map(ToOwned::to_owned)
            .map_err(|e| Error::encoding_error(format!("{}", e)))
    }
}

impl Deref for RString {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        let self_ptr = self as *const Self;
        let value_ptr = self_ptr as *const Self::Target;
        // we just got this pointer from &self, so we know it's valid to deref
        unsafe { &*value_ptr }
    }
}

impl fmt::Display for RString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for RString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.inspect() })
    }
}

impl From<RString> for Value {
    fn from(val: RString) -> Self {
        *val
    }
}

impl Object for RString {}

impl TryConvert<'_> for RString {
    unsafe fn try_convert(val: &Value) -> Result<Self, Error> {
        match Self::from_value(&val) {
            Some(i) => Ok(i),
            None => protect(|| {
                debug_assert_value!(val);
                Value::new(rb_str_to_str(val.into_inner()))
            })
            .map(|res| Self(res.into_inner())),
        }
    }
}
