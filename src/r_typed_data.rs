use std::{
    ffi::{c_void, CString},
    fmt,
    marker::PhantomData,
    mem::size_of_val,
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
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            (val.rb_type() == ruby_value_type::RUBY_T_DATA)
                .then(|| NonNull::new_unchecked(val.as_rb_value() as *mut ruby_sys::RTypedData))
                .and_then(|typed_data| {
                    (typed_data.as_ref().typed_flag == 1)
                        .then(|| Self(NonZeroValue::new_unchecked(val)))
                })
        }
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
        write!(f, "{}", self.inspect())
    }
}

impl From<RTypedData> for Value {
    fn from(val: RTypedData) -> Self {
        *val
    }
}

impl Object for RTypedData {}

pub type DataType = rb_data_type_t;

impl DataType {
    pub fn builder<T>(name: &'static str) -> DataTypeBuilder<T>
    where
        T: DataTypeFunctions,
    {
        DataTypeBuilder::new(name)
    }
}

impl Drop for DataType {
    fn drop(&mut self) {
        unsafe {
            CString::from_raw(self.wrap_struct_name as *mut _);
        }
    }
}

pub trait DataTypeFunctions
where
    Self: Sized,
{
    fn free(self: Box<Self>) {}

    fn mark(&mut self) {}

    fn size(&self) -> usize {
        size_of_val(self)
    }

    fn compact(&mut self) {}

    /// # Safety
    ///
    /// `ptr` must be a vaild pointer to a `Box<Self>`, and must not be aliased
    /// This function will free the memory pointed to by `ptr`.
    unsafe extern "C" fn extern_free(ptr: *mut c_void) {
        Self::free(Box::from_raw(ptr as *mut _))
    }

    /// # Safety
    ///
    /// `ptr` must be a vaild pointer to a `Self`, and must not be aliased.
    unsafe extern "C" fn extern_mark(ptr: *mut c_void) {
        Self::mark(&mut *(ptr as *mut Self));
    }

    /// # Safety
    ///
    /// `ptr` must be a vaild pointer to a `Self`.
    unsafe extern "C" fn extern_size(ptr: *const c_void) -> size_t {
        Self::size(&*(ptr as *const Self)) as size_t
    }

    /// # Safety
    ///
    /// `ptr` must be a vaild pointer to a `Self`, and must not be aliased.
    unsafe extern "C" fn extern_compact(ptr: *mut c_void) {
        Self::compact(&mut *(ptr as *mut Self));
    }
}

pub struct DataTypeBuilder<T> {
    name: &'static str,
    mark: bool,
    size: bool,
    compact: bool,
    free_immediatly: bool,
    wb_protected: bool,
    frozen_shareable: bool,
    phantom: PhantomData<T>,
}

impl<T> DataTypeBuilder<T>
where
    T: DataTypeFunctions,
{
    pub fn new(name: &'static str) -> Self {
        Self {
            name,
            mark: false,
            size: false,
            compact: false,
            free_immediatly: false,
            wb_protected: false,
            frozen_shareable: false,
            phantom: Default::default(),
        }
    }

    pub fn mark(&mut self) {
        self.mark = true;
    }

    pub fn size(&mut self) {
        self.size = true;
    }

    pub fn compact(&mut self) {
        self.compact = true;
    }

    pub fn free_immediatly(&mut self) {
        self.free_immediatly = true;
    }

    pub fn wb_protected(&mut self) {
        self.wb_protected = true;
    }

    pub fn frozen_shareable(&mut self) {
        self.frozen_shareable = true;
    }

    pub fn build(self) -> DataType {
        let mut flags = 0_usize as VALUE;
        if self.free_immediatly {
            flags |= rbimpl_typeddata_flags::RUBY_TYPED_FREE_IMMEDIATELY as VALUE;
        }
        if self.wb_protected {
            flags |= rbimpl_typeddata_flags::RUBY_TYPED_FROZEN_SHAREABLE as VALUE;
        }
        if self.frozen_shareable {
            flags |= rbimpl_typeddata_flags::RUBY_TYPED_WB_PROTECTED as VALUE;
        }
        let dmark = self.mark.then(|| T::extern_mark as _);
        let dfree = Some(T::extern_free as _);
        let dsize = self.size.then(|| T::extern_size as _);
        let dcompact = self.compact.then(|| T::extern_compact as _);
        DataType {
            wrap_struct_name: CString::new(self.name).unwrap().into_raw() as _,
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
}

pub unsafe trait TypedData
where
    Self: Sized,
{
    fn class() -> RClass;

    fn data_type() -> &'static DataType;
}

impl<T> TryConvert for &T
where
    T: TypedData,
{
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        debug_assert_value!(val);
        unsafe {
            let mut res = None;
            let _ = protect(|| {
                res = (rb_check_typeddata(val.as_rb_value(), T::data_type() as *const _)
                    as *const T)
                    .as_ref();
                *Qnil::new()
            });
            res.ok_or_else(|| {
                Error::type_error(format!(
                    "no implicit conversion of {} into {}",
                    val.classname(),
                    T::class()
                ))
            })
        }
    }
}

impl<T> From<T> for Value
where
    T: TypedData,
{
    fn from(data: T) -> Self {
        let boxed = Box::new(data);
        let value_ptr = unsafe {
            rb_data_typed_object_wrap(
                T::class().as_rb_value(),
                Box::into_raw(boxed) as *mut _,
                T::data_type() as *const _,
            )
        };
        Value::new(value_ptr)
    }
}
