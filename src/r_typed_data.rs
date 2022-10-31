//! Types and Traits for wrapping Rust types as Ruby objects.
//!
//! This provides a Rust API to the `rb_data_typed_object_wrap` function from
//! Ruby's C API.

use std::{
    ffi::{c_void, CString},
    fmt,
    marker::PhantomData,
    mem::size_of_val,
    ops::Deref,
    panic::catch_unwind,
    ptr::{self, NonNull},
};

#[cfg(ruby_gte_3_0)]
use rb_sys::rbimpl_typeddata_flags::{self, RUBY_TYPED_FREE_IMMEDIATELY, RUBY_TYPED_WB_PROTECTED};
use rb_sys::{
    self, rb_check_typeddata, rb_data_type_struct__bindgen_ty_1, rb_data_type_t,
    rb_data_typed_object_wrap, ruby_value_type, size_t, VALUE,
};

#[cfg(ruby_lt_3_0)]
const RUBY_TYPED_FREE_IMMEDIATELY: u32 = 1;

#[cfg(ruby_lt_3_0)]
const RUBY_TYPED_WB_PROTECTED: u32 = rb_sys::ruby_fl_type::RUBY_FL_WB_PROTECTED as u32;

use crate::{
    class::RClass,
    debug_assert_value,
    error::{bug_from_panic, protect, Error},
    exception,
    object::Object,
    try_convert::TryConvert,
    value::{private, NonZeroValue, ReprValue, Value, QNIL},
};

/// A Value pointer to a RTypedData struct, Ruby’s internal representation of
/// objects that wrap foreign types.
///
/// All [`Value`] methods should be available on this type through [`Deref`],
/// but some may be missed by this documentation.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RTypedData(NonZeroValue);

impl RTypedData {
    /// Return `Some(RTypedData)` if `val` is a `RTypedData`, `None` otherwise.
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            (val.rb_type() == ruby_value_type::RUBY_T_DATA)
                .then(|| NonNull::new_unchecked(val.as_rb_value() as *mut rb_sys::RTypedData))
                .and_then(|typed_data| {
                    (typed_data.as_ref().typed_flag == 1)
                        .then(|| Self(NonZeroValue::new_unchecked(val)))
                })
        }
    }

    /// Wrap the Rust type `T` in a Ruby object.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{define_class, RTypedData};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// #[magnus::wrap(class = "Point")]
    /// struct Point {
    ///     x: isize,
    ///     y: isize,
    /// }
    ///
    /// let point_class = define_class("Point", Default::default()).unwrap();
    ///
    /// let value = RTypedData::wrap(Point { x: 4, y: 2 });
    /// assert!(value.is_kind_of(point_class));
    /// ```
    pub fn wrap<T>(data: T) -> Self
    where
        T: TypedData,
    {
        let boxed = Box::new(data);
        unsafe {
            let value_ptr = rb_data_typed_object_wrap(
                T::class().as_rb_value(),
                Box::into_raw(boxed) as *mut _,
                T::data_type().as_rb_data_type() as *const _,
            );
            Self(NonZeroValue::new_unchecked(Value::new(value_ptr)))
        }
    }

    /// Get a reference to the Rust type wrapped in the Ruby object `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{define_class, RTypedData};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// #[magnus::wrap(class = "Point")]
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Point {
    ///     x: isize,
    ///     y: isize,
    /// }
    ///
    /// let point_class = define_class("Point", Default::default()).unwrap();
    /// let value = RTypedData::wrap(Point { x: 4, y: 2 });
    ///
    /// assert_eq!(value.get::<Point>().unwrap(), &Point { x: 4, y: 2 });
    /// ```
    pub fn get<T>(&self) -> Result<&T, Error>
    where
        T: TypedData,
    {
        unsafe { self.get_unconstrained() }
    }

    /// Get a reference to the Rust type wrapped in the Ruby object `self`.
    ///
    /// # Safety
    ///
    /// This method can magic any lifetime needed out of thin air, even
    /// `'static`.
    unsafe fn get_unconstrained<'a, T>(self) -> Result<&'a T, Error>
    where
        T: TypedData,
    {
        debug_assert_value!(self);
        let mut res = None;
        let _ = protect(|| {
            res = (rb_check_typeddata(
                self.as_rb_value(),
                T::data_type().as_rb_data_type() as *const _,
            ) as *const T)
                .as_ref();
            QNIL
        });
        res.ok_or_else(|| {
            Error::new(
                exception::type_error(),
                format!(
                    "no implicit conversion of {} into {}",
                    self.classname(),
                    T::class()
                ),
            )
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
        write!(f, "{}", self.inspect())
    }
}

impl From<RTypedData> for Value {
    fn from(val: RTypedData) -> Self {
        *val
    }
}

impl Object for RTypedData {}

unsafe impl private::ReprValue for RTypedData {
    fn to_value(self) -> Value {
        *self
    }

    unsafe fn from_value_unchecked(val: Value) -> Self {
        Self(NonZeroValue::new_unchecked(val))
    }
}

impl ReprValue for RTypedData {}

/// A C struct containing metadata on a Rust type, for use with the
/// `rb_data_typed_object_wrap` API.
#[repr(transparent)]
pub struct DataType(rb_data_type_t);

impl DataType {
    /// Create a new `DataTypeBuilder`.
    ///
    /// `name` should be unique per wrapped type. It does not need to be a
    /// valid Ruby identifier.
    pub fn builder<T>(name: &'static str) -> DataTypeBuilder<T>
    where
        T: DataTypeFunctions,
    {
        DataTypeBuilder::new(name)
    }

    pub(crate) fn as_rb_data_type(&self) -> &rb_data_type_t {
        &self.0
    }
}

impl Drop for DataType {
    fn drop(&mut self) {
        unsafe {
            drop(CString::from_raw(self.0.wrap_struct_name as *mut _));
        }
    }
}

/// A helper trait used to define functions associated with a [`DataType`].
pub trait DataTypeFunctions
where
    Self: Send + Sized,
{
    /// Called when the Ruby wrapper object is garbage collected.
    ///
    /// This can be implemented to perform Ruby-specific clean up when your
    /// type is no longer referenced from Ruby, but it is likely easier to do
    /// this in a Drop implementation for your type.
    ///
    /// The default implementation simply drops `self`.
    ///
    /// This function **must not** panic. The process will abort if this
    /// function panics.
    fn free(self: Box<Self>) {}

    /// Called when Ruby marks this object as part of garbage collection.
    ///
    /// If your type contains any Ruby values you must mark each of those
    /// values in this function to avoid them being garbage collected.
    ///
    /// The default implementation does nothing.
    ///
    /// This function **must not** panic. The process will abort if this
    /// function panics.
    fn mark(&self) {}

    /// Called by Ruby to establish the memory size of this data, to optimise
    /// when garbage collection happens.
    ///
    /// The default implementation delegates to [`std::mem::size_of_val`].
    ///
    /// This function **must not** panic. The process will abort if this
    /// function panics.
    fn size(&self) -> usize {
        size_of_val(self)
    }

    /// Called during garbage collection.
    ///
    /// If your type contains any Ruby values that have been marked as moveable
    /// you must update them in this function.
    ///
    /// The default implementation does nothing.
    ///
    /// This function **must not** panic. The process will abort if this
    /// function panics.
    fn compact(&self) {}

    /// Extern wrapper for `free`. Don't define or call.
    ///
    /// # Safety
    ///
    /// `ptr` must be a vaild pointer to a `Box<Self>`, and must not be aliased
    /// This function will free the memory pointed to by `ptr`.
    ///
    /// This function must not panic.
    #[doc(hidden)]
    unsafe extern "C" fn extern_free(ptr: *mut c_void) {
        if let Err(e) = catch_unwind(|| Self::free(Box::from_raw(ptr as *mut _))) {
            bug_from_panic(e, "panic in DataTypeFunctions::free")
        }
    }

    /// Extern wrapper for `mark`. Don't define or call.
    ///
    /// # Safety
    ///
    /// `ptr` must be a vaild pointer to a `Self`, and must not be aliased.
    ///
    /// This function must not panic.
    #[doc(hidden)]
    unsafe extern "C" fn extern_mark(ptr: *mut c_void) {
        if let Err(e) = catch_unwind(|| Self::mark(&*(ptr as *mut Self))) {
            bug_from_panic(e, "panic in DataTypeFunctions::mark")
        }
    }

    /// Extern wrapper for `size`. Don't define or call.
    ///
    /// # Safety
    ///
    /// `ptr` must be a vaild pointer to a `Self`.
    ///
    /// This function must not panic.
    #[doc(hidden)]
    unsafe extern "C" fn extern_size(ptr: *const c_void) -> size_t {
        match catch_unwind(|| Self::size(&*(ptr as *const Self)) as size_t) {
            Ok(v) => v,
            Err(e) => bug_from_panic(e, "panic in DataTypeFunctions::size"),
        }
    }

    /// Extern wrapper for `compact`. Don't define or call.
    ///
    /// # Safety
    ///
    /// `ptr` must be a vaild pointer to a `Self`, and must not be aliased.
    ///
    /// This function must not panic.
    #[doc(hidden)]
    unsafe extern "C" fn extern_compact(ptr: *mut c_void) {
        if let Err(e) = catch_unwind(|| Self::compact(&*(ptr as *mut Self))) {
            bug_from_panic(e, "panic in DataTypeFunctions::compact")
        }
    }
}

/// A builder for [`DataType`].
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
    /// Create a new `DataTypeBuilder`.
    ///
    /// `name` should be unique per wrapped type. It does not need to be a
    /// valid Ruby identifier.
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

    /// Enable using the the `mark` function from `<T as DataTypeFunctions>`.
    pub fn mark(&mut self) {
        self.mark = true;
    }

    /// Enable using the the `size` function from `<T as DataTypeFunctions>`.
    pub fn size(&mut self) {
        self.size = true;
    }

    /// Enable using the the `compact` function from `<T as DataTypeFunctions>`.
    pub fn compact(&mut self) {
        self.compact = true;
    }

    /// Enable the 'free_immediatly' flag.
    ///
    /// This is safe to do as long as the `<T as DataTypeFunctions>::free`
    /// function or `T`'s drop function don't call Ruby in any way.
    ///
    /// If safe this should be enabled as this performs better and is more
    /// memory efficient.
    pub fn free_immediatly(&mut self) {
        self.free_immediatly = true;
    }

    /// Enable the 'write barrier protected' flag.
    ///
    /// You almost certainly don't want to enable this.
    pub fn wb_protected(&mut self) {
        self.wb_protected = true;
    }

    /// Enable the 'frozen_shareable' flag.
    ///
    /// Set this if your type is thread safe when the Ruby wrapper object is
    /// frozen.
    pub fn frozen_shareable(&mut self) {
        self.frozen_shareable = true;
    }

    /// Consume the builder and create a DataType.
    pub fn build(self) -> DataType {
        let mut flags = 0_usize as VALUE;
        if self.free_immediatly {
            flags |= RUBY_TYPED_FREE_IMMEDIATELY as VALUE;
        }
        if self.wb_protected {
            flags |= RUBY_TYPED_WB_PROTECTED as VALUE;
        }
        #[cfg(ruby_gte_3_0)]
        if self.frozen_shareable {
            flags |= rbimpl_typeddata_flags::RUBY_TYPED_FROZEN_SHAREABLE as VALUE;
        }
        let dmark = self.mark.then(|| T::extern_mark as _);
        let dfree = Some(T::extern_free as _);
        let dsize = self.size.then(|| T::extern_size as _);
        #[cfg(ruby_gte_2_7)]
        let dcompact = self.compact.then(|| T::extern_compact as _);
        DataType(rb_data_type_t {
            wrap_struct_name: CString::new(self.name).unwrap().into_raw() as _,
            function: rb_data_type_struct__bindgen_ty_1 {
                dmark,
                dfree,
                dsize,
                #[cfg(ruby_gte_2_7)]
                dcompact,
                #[cfg(ruby_gte_2_7)]
                reserved: [ptr::null_mut(); 1],
                #[cfg(ruby_lt_2_7)]
                reserved: [ptr::null_mut(); 2],
            },
            parent: ptr::null(),
            data: ptr::null_mut(),
            flags,
        })
    }
}

/// A trait for Rust types that can be used with the `rb_data_typed_object_wrap`
/// API.
///
/// # Safety
///
/// This trait is unsafe to impliment as the fields of [`DataType`] returned by
/// [`TypedData::data_type`] control low level behaviour that can go very wrong
/// if set incorrectly. Implimenting this trait is the only way a [`DataType`]
/// can be passed to Ruby and result in safety violations, [`DataType`] is
/// otherwise safe (but useless) to create.
///
/// The [`TypedData`](`derive@crate::TypedData`) or [`wrap`](`crate::wrap`) macros can
/// help implementing this trait more safely.
pub unsafe trait TypedData
where
    Self: Send + Sized,
{
    /// Should return the class for the Ruby object wrapping the Rust type.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{define_class, memoize, RClass};
    ///
    /// fn class() -> RClass {
    ///     *memoize!(RClass: define_class("Foo", Default::default()).unwrap())
    /// }
    /// ```
    fn class() -> RClass;

    /// Should return a static reference to a [`DataType`] with metadata about
    /// the wrapped type.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{memoize, r_typed_data::DataTypeBuilder, DataType, DataTypeFunctions};
    ///
    /// #[derive(DataTypeFunctions)]
    /// struct Foo();
    ///
    /// fn data_type() -> &'static DataType {
    ///     memoize!(DataType: DataTypeBuilder::<Foo>::new("foo").build())
    /// }
    /// ```
    fn data_type() -> &'static DataType;
}

impl<T> TryConvert for &T
where
    T: TypedData,
{
    fn try_convert(val: Value) -> Result<Self, Error> {
        unsafe {
            RTypedData::from_value(val)
                .ok_or_else(|| {
                    Error::new(
                        exception::type_error(),
                        format!(
                            "no implicit conversion of {} into {}",
                            val.classname(),
                            T::class()
                        ),
                    )
                })?
                .get_unconstrained()
        }
    }
}

impl<T> From<T> for Value
where
    T: TypedData,
{
    fn from(data: T) -> Self {
        RTypedData::wrap(data).into()
    }
}
