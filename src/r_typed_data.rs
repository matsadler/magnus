use std::{
    ffi::{c_void, CString},
    ops::Deref,
    ptr::{self, NonNull},
};

use crate::{
    debug_assert_value,
    error::Error,
    object::Object,
    protect,
    r_basic::RBasic,
    r_class::RClass,
    ruby_sys::{
        self, rb_check_typeddata, rb_data_type_struct__bindgen_ty_1, rb_data_type_t,
        rb_data_typed_object_wrap, rbimpl_typeddata_flags, ruby_value_type, size_t, VALUE,
    },
    try_convert::{TryConvert, TryConvertToRust},
    value::{Qnil, Value},
};

#[repr(transparent)]
pub struct RTypedData(VALUE);

impl RTypedData {
    /// # Safety
    ///
    /// val must not have been GC'd, return value must be kept on stack or
    /// otherwise protected from the GC.
    pub unsafe fn from_value(val: &Value) -> Option<Self> {
        let r_basic = RBasic::from_value(val)?;
        (r_basic.builtin_type() == ruby_value_type::RUBY_T_DATA)
            .then(|| unsafe {
                NonNull::new_unchecked(val.into_inner() as *mut ruby_sys::RTypedData)
            })
            .and_then(|typed_data| {
                (typed_data.as_ref().typed_flag == 1).then(|| Self(val.into_inner()))
            })
    }

    // TODO: use or remove
    #[allow(dead_code)]
    pub(crate) fn as_internal(&self) -> NonNull<ruby_sys::RTypedData> {
        // safe as to get self we need to have gone through ::from_value()
        // where val is vaild as an RBasic, which rules out NULL
        unsafe { NonNull::new_unchecked(self.0 as *mut _) }
    }
}

impl Deref for RTypedData {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        let self_ptr = self as *const Self;
        let value_ptr = self_ptr as *const Self::Target;
        // we just got this pointer from &self, so we know it's valid to deref
        unsafe { &*value_ptr }
    }
}

impl From<RTypedData> for Value {
    fn from(val: RTypedData) -> Self {
        *val
    }
}

impl Object for RTypedData {}

pub trait TypedData
where
    Self: Sized,
{
    const NAME: &'static str;
    /// set true if a mark function is provided (default false).
    const MARK: bool = false;
    /// set true if a size function is provided (default false).
    const SIZE: bool = false;
    /// set true if a compact function is provided (default false).
    const COMPACT: bool = false;
    const FREE_IMMEDIATLY: bool = false;
    const WB_PROTECTED: bool = false;
    const FROZEN_SHAREABLE: bool = false;

    fn class() -> RClass;

    fn data_type() -> &'static rb_data_type_t;

    #[allow(clippy::boxed_local, unused_variables)]
    fn free(data: Box<Self>) {}

    #[allow(unused_variables)]
    fn mark(data: &mut Self) {}

    #[allow(unused_variables)]
    fn size(data: &mut Self) -> usize {
        0
    }

    #[allow(unused_variables)]
    fn compact(data: &mut Self) {}

    /// # Safety
    ///
    /// val must not have been GC'd
    unsafe fn from_value(val: &Value) -> Option<&Self> {
        debug_assert_value!(val);
        let mut res = None;
        let _ = protect(|| {
            res = (rb_check_typeddata(val.into_inner(), Self::data_type() as *const _)
                as *const Self)
                .as_ref();
            *Qnil::new()
        });
        res
    }

    fn into_value(self) -> Value {
        let boxed = Box::new(self);
        let value_ptr = unsafe {
            rb_data_typed_object_wrap(
                Self::class().into_inner(),
                Box::into_raw(boxed) as *mut _,
                Self::data_type() as *const _,
            )
        };
        Value::new(value_ptr)
    }

    #[doc(hidden)]
    fn build_data_type() -> rb_data_type_t {
        #[allow(clippy::unnecessary_cast)]
        let mut flags = 0 as VALUE;
        if Self::FREE_IMMEDIATLY {
            flags |= rbimpl_typeddata_flags::RUBY_TYPED_FREE_IMMEDIATELY as VALUE;
        }
        if Self::WB_PROTECTED {
            flags |= rbimpl_typeddata_flags::RUBY_TYPED_FROZEN_SHAREABLE as VALUE;
        }
        if Self::FROZEN_SHAREABLE {
            flags |= rbimpl_typeddata_flags::RUBY_TYPED_WB_PROTECTED as VALUE;
        }
        let dmark = Self::MARK.then(|| Self::extern_mark as _);
        let dfree = Some(Self::extern_free as _);
        let dsize = Self::SIZE.then(|| Self::extern_size as _);
        let dcompact = Self::COMPACT.then(|| Self::extern_compact as _);
        rb_data_type_t {
            wrap_struct_name: CString::new(Self::NAME).unwrap().into_raw() as _,
            function: rb_data_type_struct__bindgen_ty_1 {
                dmark,
                dfree,
                dsize,
                dcompact,
                reserved: [ptr::null_mut(); 1],
            },
            parent: ptr::null(),
            data: ptr::null_mut(),
            flags,
        }
    }

    #[doc(hidden)]
    unsafe extern "C" fn extern_free(ptr: *mut c_void) {
        Self::free(Box::from_raw(ptr as *mut _))
    }

    #[doc(hidden)]
    unsafe extern "C" fn extern_mark(ptr: *mut c_void) {
        let mut boxed = Box::<Self>::from_raw(ptr as *mut _);
        Self::mark(boxed.as_mut());
        Box::leak(boxed);
    }

    #[doc(hidden)]
    unsafe extern "C" fn extern_size(ptr: *const c_void) -> size_t {
        let mut boxed = Box::<Self>::from_raw(ptr as *mut _);
        let res = Self::size(boxed.as_mut());
        Box::leak(boxed);
        res as size_t
    }

    #[doc(hidden)]
    unsafe extern "C" fn extern_compact(ptr: *mut c_void) {
        let mut boxed = Box::<Self>::from_raw(ptr as *mut _);
        Self::compact(boxed.as_mut());
        Box::leak(boxed);
    }
}

impl<'a, T> TryConvert<'a> for &'a T
where
    T: TypedData,
{
    unsafe fn try_convert(val: &'a Value) -> Result<Self, Error> {
        // TODO add classes to error message
        T::from_value(val).ok_or_else(|| Error::type_error("no implicit conversion of {} into {}"))
    }
}
impl<'a, T> TryConvertToRust<'a> for &'a T where T: TypedData {}

impl<T> From<T> for Value
where
    T: TypedData,
{
    fn from(val: T) -> Self {
        val.into_value()
    }
}
