use std::{
    ffi::{c_void, CString},
    fmt,
    ops::Deref,
    ptr::{self, NonNull},
};

use crate::{
    debug_assert_value,
    error::{protect, Error},
    object::Object,
    r_class::RClass,
    ruby_sys::{
        self, rb_check_typeddata, rb_data_type_struct__bindgen_ty_1, rb_data_type_t,
        rb_data_typed_object_wrap, rbimpl_typeddata_flags, ruby_value_type, size_t, VALUE,
    },
    try_convert::TryConvert,
    value::{NonZeroValue, Qnil, Value},
};

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RTypedData(NonZeroValue);

impl RTypedData {
    /// # Safety
    ///
    /// val must not have been GC'd, return value must be kept on stack or
    /// otherwise protected from the GC.
    #[inline]
    pub unsafe fn from_value(val: Value) -> Option<Self> {
        (val.rb_type() == ruby_value_type::RUBY_T_DATA)
            .then(|| unsafe {
                NonNull::new_unchecked(val.as_rb_value() as *mut ruby_sys::RTypedData)
            })
            .and_then(|typed_data| {
                (typed_data.as_ref().typed_flag == 1)
                    .then(|| Self(NonZeroValue::new_unchecked(val)))
            })
    }
}

impl Deref for RTypedData {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
    }
}

impl fmt::Display for RTypedData {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for RTypedData {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.inspect() })
    }
}

impl From<RTypedData> for Value {
    fn from(val: RTypedData) -> Self {
        *val
    }
}

impl Object for RTypedData {}

pub type DataType = rb_data_type_t;

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

    fn data_type() -> &'static DataType;

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
    unsafe fn from_value<'a>(val: Value) -> Option<&'a Self> {
        debug_assert_value!(val);
        let mut res = None;
        let _ = protect(|| {
            res = (rb_check_typeddata(val.as_rb_value(), Self::data_type() as *const _)
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
                Self::class().as_rb_value(),
                Box::into_raw(boxed) as *mut _,
                Self::data_type() as *const _,
            )
        };
        Value::new(value_ptr)
    }

    #[doc(hidden)]
    fn build_data_type() -> DataType {
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
        DataType {
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

impl<T> TryConvert for &T
where
    T: TypedData,
{
    #[inline]
    unsafe fn try_convert(val: &Value) -> Result<Self, Error> {
        T::from_value(*val).ok_or_else(|| {
            Error::type_error(format!(
                "no implicit conversion of {} into {}",
                val.classname(),
                T::class()
            ))
        })
    }
}

impl<T> From<T> for Value
where
    T: TypedData,
{
    fn from(val: T) -> Self {
        val.into_value()
    }
}
