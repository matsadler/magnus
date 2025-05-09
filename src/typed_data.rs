//! Types and Traits for wrapping Rust types as Ruby objects.
//!
//! This, along with [`RTypedData`], provides a Rust API to the
//! `rb_data_typed_object_wrap` function from Ruby's C API.

use std::{
    collections::hash_map::DefaultHasher,
    ffi::{c_void, CStr},
    fmt,
    hash::Hasher,
    marker::PhantomData,
    mem::size_of_val,
    ops::Deref,
    panic::catch_unwind,
    ptr,
};

#[cfg(ruby_gte_3_0)]
use rb_sys::rbimpl_typeddata_flags::{self, RUBY_TYPED_FREE_IMMEDIATELY, RUBY_TYPED_WB_PROTECTED};
use rb_sys::{
    self, rb_data_type_struct__bindgen_ty_1, rb_data_type_t, rb_gc_writebarrier,
    rb_gc_writebarrier_unprotect, rb_obj_reveal, rb_singleton_class_attached,
    rb_singleton_class_clone, size_t, RTYPEDDATA_GET_DATA, VALUE,
};

#[cfg(ruby_lt_3_0)]
const RUBY_TYPED_FREE_IMMEDIATELY: u32 = 1;

#[cfg(ruby_lt_3_0)]
const RUBY_TYPED_WB_PROTECTED: u32 = rb_sys::ruby_fl_type::RUBY_FL_WB_PROTECTED as u32;

use crate::{
    class::RClass,
    error::{bug_from_panic, Error},
    gc::{self, Mark},
    into_value::IntoValue,
    object::Object,
    r_typed_data::RTypedData,
    scan_args::{get_kwargs, scan_args},
    try_convert::TryConvert,
    value::{
        private::{self, ReprValue as _},
        ReprValue, Value,
    },
    Ruby,
};

/// A C struct containing metadata on a Rust type, for use with the
/// `rb_data_typed_object_wrap` API.
#[repr(transparent)]
pub struct DataType(rb_data_type_t);

impl DataType {
    /// Create a new `DataTypeBuilder`.
    ///
    /// `name` should be unique per wrapped type. It does not need to be a
    /// valid Ruby identifier.
    ///
    /// See [`data_type_builder`](macro@crate::data_type_builder) to create a
    /// `DataTypeBuilder` with a `'static CStr` `name` from a string literal.
    pub const fn builder<T>(name: &'static CStr) -> DataTypeBuilder<T>
    where
        T: DataTypeFunctions,
    {
        DataTypeBuilder::new(name)
    }

    #[inline]
    pub(crate) fn as_rb_data_type(&self) -> &rb_data_type_t {
        &self.0
    }
}

unsafe impl Send for DataType {}
unsafe impl Sync for DataType {}

/// A helper trait used to define functions associated with a [`DataType`].
pub trait DataTypeFunctions
where
    Self: Send + Sized,
{
    /// Called when the Ruby wrapper object is garbage collected.
    ///
    /// This can be implemented to perform Ruby-specific clean up when your
    /// type is no longer referenced from Ruby, but it is likely easier to do
    /// this in a [`Drop`] implementation for your type.
    ///
    /// This function will always be called by Ruby on GC, it can not be opted
    /// out of.
    ///
    /// The default implementation simply drops `self`.
    ///
    /// If this function (or the [`Drop`] implementation for your type) call
    /// Ruby APIs you should not enable the `free_immediately` flag with the
    /// [`wrap`](macro@crate::wrap)/[`TypedData`](macro@crate::TypedData)
    /// macro or [`DataTypeBuilder::free_immediately`].
    ///
    /// This function **must not** panic. The process will abort if this
    /// function panics.
    fn free(self: Box<Self>) {}

    /// Called when Ruby marks this object as part of garbage collection.
    ///
    /// If your type contains any Ruby values you must mark each of those
    /// values in this function to avoid them being garbage collected.
    ///
    /// This function is only called when the `mark` flag is set with the
    /// [`wrap`](macro@crate::wrap)/[`TypedData`](macro@crate::TypedData)
    /// macro or [`DataTypeBuilder::mark`].
    ///
    /// The default implementation does nothing.
    ///
    /// This function **must not** panic. The process will abort if this
    /// function panics.
    fn mark(&self, #[allow(unused_variables)] marker: &gc::Marker) {}

    /// Called by Ruby to establish the memory size of this data, to optimise
    /// when garbage collection happens.
    ///
    /// This function is only called when the `size` flag is set with the
    /// [`wrap`](macro@crate::wrap)/[`TypedData`](macro@crate::TypedData)
    /// macro or [`DataTypeBuilder::mark`].
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
    /// If your type contains any Ruby values that you have marked as moveable
    /// in your [`mark`](Self::mark) function, you must update them in this
    /// function using [`gc::Compactor::location`].
    ///
    /// Ruby considers values are moveable if marked with the
    /// [`gc::Marker::mark_movable`] function. Other marking functions such as
    /// [`gc::Marker::mark`] will prevent values being moved.
    ///
    /// As it is only safe for this function to receive a shared `&self`
    /// reference, you must implement interior mutability to be able to update
    /// values. This is very hard to do correctly, and it is recommended to
    /// simply avoid using [`gc::Marker::mark_movable`] and `compact`.
    ///
    /// This function is only called when the `compact` flag is set with the
    /// [`wrap`](macro@crate::wrap)/[`TypedData`](macro@crate::TypedData)
    /// macro or [`DataTypeBuilder::mark`].
    ///
    /// The default implementation does nothing.
    ///
    /// This function **must not** panic. The process will abort if this
    /// function panics.
    fn compact(&self, #[allow(unused_variables)] compactor: &gc::Compactor) {}

    /// Extern wrapper for `free`. Don't define or call.
    ///
    /// # Safety
    ///
    /// `ptr` must be a valid pointer to a `Box<Self>`, and must not be aliased
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
    /// `ptr` must be a valid pointer to a `Self`, and must not be aliased.
    ///
    /// This function must not panic.
    #[doc(hidden)]
    unsafe extern "C" fn extern_mark(ptr: *mut c_void) {
        let marker = gc::Marker::new();
        if let Err(e) = catch_unwind(|| Self::mark(&*(ptr as *mut Self), &marker)) {
            bug_from_panic(e, "panic in DataTypeFunctions::mark")
        }
    }

    /// Extern wrapper for `size`. Don't define or call.
    ///
    /// # Safety
    ///
    /// `ptr` must be a valid pointer to a `Self`.
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
    /// `ptr` must be a valid pointer to a `Self`, and must not be aliased.
    ///
    /// This function must not panic.
    #[doc(hidden)]
    unsafe extern "C" fn extern_compact(ptr: *mut c_void) {
        let compactor = gc::Compactor::new();
        if let Err(e) = catch_unwind(|| Self::compact(&*(ptr as *mut Self), &compactor)) {
            bug_from_panic(e, "panic in DataTypeFunctions::compact")
        }
    }
}

/// A builder for [`DataType`].
pub struct DataTypeBuilder<T> {
    name: &'static CStr,
    mark: bool,
    size: bool,
    compact: bool,
    free_immediately: bool,
    wb_protected: bool,
    frozen_shareable: bool,
    phantom: PhantomData<T>,
}

/// Create a new [`DataTypeBuilder`].
///
/// `name` should be unique per wrapped type. It does not need to be a
/// valid Ruby identifier.
///
/// `data_type_builder!(Example, "example")` is equivalent to
/// `DataTypeBuilder::<Example>::new` with a `name` argument of `"example"` as
/// a `'static CStr`.
#[macro_export]
macro_rules! data_type_builder {
    ($t:ty, $name:literal) => {
        $crate::typed_data::DataTypeBuilder::<$t>::new(unsafe {
            std::ffi::CStr::from_bytes_with_nul_unchecked(concat!($name, "\0").as_bytes())
        })
    };
}

impl<T> DataTypeBuilder<T>
where
    T: DataTypeFunctions,
{
    /// Create a new `DataTypeBuilder`.
    ///
    /// `name` should be unique per wrapped type. It does not need to be a
    /// valid Ruby identifier.
    ///
    /// See [`data_type_builder`](macro@crate::data_type_builder) to create a
    /// `DataTypeBuilder` with a `'static CStr` `name` from a string literal.
    pub const fn new(name: &'static CStr) -> Self {
        Self {
            name,
            mark: false,
            size: false,
            compact: false,
            free_immediately: false,
            wb_protected: false,
            frozen_shareable: false,
            phantom: PhantomData,
        }
    }

    /// Enable using the the `mark` function from `<T as DataTypeFunctions>`.
    pub const fn mark(mut self) -> Self {
        self.mark = true;
        self
    }

    /// Enable using the the `size` function from `<T as DataTypeFunctions>`.
    pub const fn size(mut self) -> Self {
        self.size = true;
        self
    }

    /// Enable using the the `compact` function from `<T as DataTypeFunctions>`.
    pub const fn compact(mut self) -> Self {
        self.compact = true;
        self
    }

    /// Enable the 'free_immediately' flag.
    ///
    /// This is safe to do as long as the `<T as DataTypeFunctions>::free`
    /// function or `T`'s drop function don't call Ruby in any way.
    ///
    /// If safe this should be enabled as this performs better and is more
    /// memory efficient.
    pub const fn free_immediately(mut self) -> Self {
        self.free_immediately = true;
        self
    }

    /// Enable the 'write barrier protected' flag.
    ///
    /// Types that contain Ruby values by default do not participate in
    /// generational GC (they are scanned every GC). This flag asserts all
    /// operations that write Ruby values to this type are protected with
    /// write barriers (see [`Writebarrier::writebarrier`]) so this
    /// type can participate in generational GC.
    ///
    /// The write barrier is hard to get right. Magnus recommends you do not use
    /// this flag.
    pub const fn wb_protected(mut self) -> Self {
        self.wb_protected = true;
        self
    }

    /// Consume the builder and create a DataType.
    pub const fn build(self) -> DataType {
        let mut flags = 0_usize as VALUE;
        if self.free_immediately {
            flags |= RUBY_TYPED_FREE_IMMEDIATELY as VALUE;
        }
        if self.wb_protected || !self.mark {
            flags |= RUBY_TYPED_WB_PROTECTED as VALUE;
        }
        #[cfg(ruby_gte_3_0)]
        if self.frozen_shareable {
            flags |= rbimpl_typeddata_flags::RUBY_TYPED_FROZEN_SHAREABLE as VALUE;
        }
        let dmark = if self.mark {
            Some(T::extern_mark as _)
        } else {
            None
        };
        let dfree = Some(T::extern_free as _);
        let dsize = if self.size {
            Some(T::extern_size as _)
        } else {
            None
        };
        let dcompact = if self.compact {
            Some(T::extern_compact as _)
        } else {
            None
        };
        DataType(rb_data_type_t {
            wrap_struct_name: self.name.as_ptr() as _,
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
        })
    }
}

impl<T> DataTypeBuilder<T>
where
    T: DataTypeFunctions + Sync,
{
    /// Enable the 'frozen_shareable' flag.
    ///
    /// Set this if your type is thread safe when the Ruby wrapper object is
    /// frozen.
    pub const fn frozen_shareable(mut self) -> Self {
        self.frozen_shareable = true;
        self
    }
}

/// A trait for Rust types that can be used with the
/// `rb_data_typed_object_wrap` API.
///
/// # Safety
///
/// This trait is unsafe to implement as the fields of [`DataType`] returned by
/// [`TypedData::data_type`] control low level behaviour that can go very wrong
/// if set incorrectly. Implementing this trait is the only way a [`DataType`]
/// can be passed to Ruby and result in safety violations, [`DataType`] is
/// otherwise safe (but useless) to create.
///
/// The [`TypedData`](`derive@crate::TypedData`) or [`wrap`](`crate::wrap`)
/// macros can help implementing this trait more safely.
pub unsafe trait TypedData
where
    Self: Send + Sized,
{
    /// Should return the class for the Ruby object wrapping the Rust type.
    ///
    /// This can be overridden on a case by case basis by implementing
    /// [`TypedData::class_for`], but the result of this function will always
    /// be used in error messages if a value fails to convert to `Self`.
    ///
    /// If using [`class_for`](Self::class_for) it is advised to have this
    /// function return the superclass of those returned by `class_for`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{prelude::*, value::Lazy, RClass, Ruby, TypedData};
    /// # use magnus::DataType;
    ///
    /// struct Example();
    ///
    /// unsafe impl TypedData for Example {
    ///     fn class(ruby: &Ruby) -> RClass {
    ///         static CLASS: Lazy<RClass> = Lazy::new(|ruby| {
    ///             let class = ruby.define_class("Example", ruby.class_object()).unwrap();
    ///             class.undef_default_alloc_func();
    ///             class
    ///         });
    ///         ruby.get_inner(&CLASS)
    ///     }
    ///
    ///     // ...
    /// #   fn data_type() -> &'static DataType { unimplemented!() }
    /// }
    /// ```
    fn class(ruby: &Ruby) -> RClass;

    /// Should return a static reference to a [`DataType`] with metadata about
    /// the wrapped type.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{data_type_builder, DataType, DataTypeFunctions, TypedData};
    /// # use magnus::{RClass, Ruby};
    ///
    /// #[derive(DataTypeFunctions)]
    /// struct Example();
    ///
    /// unsafe impl TypedData for Example {
    /// #   fn class(_: &Ruby) -> RClass { unimplemented!() }
    ///     // ...
    ///
    ///     fn data_type() -> &'static DataType {
    ///         static DATA_TYPE: DataType = data_type_builder!(Example, "example").build();
    ///         &DATA_TYPE
    ///     }
    /// }
    /// ```
    fn data_type() -> &'static DataType;

    /// Used to customise the class wrapping a specific value of `Self`.
    ///
    /// The provided implementation simply returns the value of
    /// [`TypedData::class`].
    ///
    /// The classes returned by this function must be subclasses of
    /// `TypedData::class`. `TypedData::class` will always be used in error
    /// messages if a value fails to convert to `Self`.
    ///
    /// See also [`Obj::wrap_as`]/[`RTypedData::wrap_as`].
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{prelude::*, value::Lazy, RClass, Ruby, TypedData};
    /// # use magnus::DataType;
    ///
    /// enum Example {
    ///     A,
    ///     B,
    /// }
    ///
    /// unsafe impl TypedData for Example {
    /// #   fn class(_: &Ruby) -> RClass { unimplemented!() }
    /// #   fn data_type() -> &'static DataType { unimplemented!() }
    ///     // ...
    ///
    ///     fn class_for(ruby: &Ruby, value: &Self) -> RClass {
    ///         static A: Lazy<RClass> = Lazy::new(|ruby| {
    ///             let class = ruby.define_class("A", Example::class(ruby)).unwrap();
    ///             class.undef_default_alloc_func();
    ///             class
    ///         });
    ///         static B: Lazy<RClass> = Lazy::new(|ruby| {
    ///             let class = ruby.define_class("B", Example::class(ruby)).unwrap();
    ///             class.undef_default_alloc_func();
    ///             class
    ///         });
    ///         match value {
    ///             Self::A => ruby.get_inner(&A),
    ///             Self::B => ruby.get_inner(&B),
    ///         }
    ///     }
    /// }
    /// # let _ = (Example::A, Example::B);
    /// ```
    #[allow(unused_variables)]
    fn class_for(ruby: &Ruby, value: &Self) -> RClass {
        Self::class(ruby)
    }
}

impl<T> TryConvert for &T
where
    T: TypedData,
{
    fn try_convert(val: Value) -> Result<Self, Error> {
        let handle = Ruby::get_with(val);
        unsafe {
            RTypedData::from_value(val)
                .ok_or_else(|| {
                    Error::new(
                        handle.exception_type_error(),
                        format!(
                            "no implicit conversion of {} into {}",
                            val.classname(),
                            T::class(&handle)
                        ),
                    )
                })?
                .get_unconstrained()
        }
    }
}

impl<T> IntoValue for T
where
    T: TypedData,
{
    #[inline]
    fn into_value_with(self, handle: &Ruby) -> Value {
        handle.wrap(self).into_value_with(handle)
    }
}

/// A Ruby Object wrapping a Rust type `T`.
///
/// This is a Value pointer to a RTypedData struct, Ruby’s internal
/// representation of objects that wrap foreign types. Unlike [`RTypedData`] it
/// tracks the Rust type it should contains and errors early in [`TryConvert`]
/// if types don't match.
///
/// See the [`ReprValue`] and [`Object`] traits for additional methods
/// available on this type. See [`Ruby`](Ruby#typed_dataobj) for methods to
/// create a `typed_data::Obj`.
#[repr(transparent)]
pub struct Obj<T> {
    inner: RTypedData,
    phantom: PhantomData<T>,
}

impl<T> Copy for Obj<T> where T: TypedData {}

impl<T> Clone for Obj<T>
where
    T: TypedData,
{
    fn clone(&self) -> Self {
        *self
    }
}

/// # `typed_data::Obj`
///
/// Functions to wrap Rust data in a Ruby object.
///
/// See also [`RTypedData`](Ruby#rtypeddata) and the [`typed_data::Obj`](Obj)
/// type.
impl Ruby {
    /// Wrap the Rust type `T` in a Ruby object.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{prelude::*, Error, Ruby};
    ///
    /// #[magnus::wrap(class = "Point")]
    /// struct Point {
    ///     x: isize,
    ///     y: isize,
    /// }
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let point_class = ruby.define_class("Point", ruby.class_object())?;
    ///
    ///     let value = ruby.obj_wrap(Point { x: 4, y: 2 });
    ///     assert!(value.is_kind_of(point_class));
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap();
    /// # let _ = Point { x: 1, y: 2 }.x + Point { x: 3, y: 4 }.y;
    /// ```
    pub fn obj_wrap<T>(&self, data: T) -> Obj<T>
    where
        T: TypedData,
    {
        Obj {
            inner: self.wrap(data),
            phantom: PhantomData,
        }
    }

    /// Wrap the Rust type `T` in a Ruby object that is an instance of the
    /// given `class`.
    ///
    /// See also [`TypedData::class_for`].
    ///
    /// # Panics
    ///
    /// Panics if `class` is not a subclass of `<T as TypedData>::class()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{prelude::*, Error, Ruby};
    ///
    /// #[magnus::wrap(class = "Point")]
    /// struct Point {
    ///     x: isize,
    ///     y: isize,
    /// }
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let point_class = ruby.define_class("Point", ruby.class_object())?;
    ///     let point_sub_class = ruby.define_class("SubPoint", point_class)?;
    ///
    ///     let value = ruby.obj_wrap_as(Point { x: 4, y: 2 }, point_sub_class);
    ///     assert!(value.is_kind_of(point_sub_class));
    ///     assert!(value.is_kind_of(point_class));
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap();
    /// # let _ = Point { x: 1, y: 2 }.x + Point { x: 3, y: 4 }.y;
    /// ```
    ///
    /// Allowing a wrapped type to be subclassed from Ruby:
    ///
    /// (note, in this example `Point` does not have and does not call the
    /// `initialize` method, subclasses would need to override the class `new`
    /// method rather than `initialize`)
    ///
    /// ```
    /// use magnus::{function, method, prelude::*, typed_data, Error, RClass, Ruby, Value};
    ///
    /// #[magnus::wrap(class = "Point")]
    /// struct Point {
    ///     x: isize,
    ///     y: isize,
    /// }
    ///
    /// impl Point {
    ///     fn new(ruby: &Ruby, class: RClass, x: isize, y: isize) -> typed_data::Obj<Self> {
    ///         ruby.obj_wrap_as(Self { x, y }, class)
    ///     }
    /// }
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let point_class = ruby.define_class("Point", ruby.class_object())?;
    ///     point_class.define_singleton_method("new", method!(Point::new, 2))?;
    ///     point_class
    ///         .define_singleton_method("inherited", function!(RClass::undef_default_alloc_func, 1))?;
    ///
    ///     let value: Value = ruby.eval(
    ///         r#"
    ///           class SubPoint < Point
    ///           end
    ///           SubPoint.new(4, 2)
    ///         "#,
    ///     )?;
    ///
    ///     assert!(value.is_kind_of(ruby.class_object().const_get::<_, RClass>("SubPoint")?));
    ///     assert!(value.is_kind_of(point_class));
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap();
    /// # let _ = Point { x: 1, y: 2 }.x + Point { x: 3, y: 4 }.y;
    /// ```
    pub fn obj_wrap_as<T>(&self, data: T, class: RClass) -> Obj<T>
    where
        T: TypedData,
    {
        Obj {
            inner: self.wrap_as(data, class),
            phantom: PhantomData,
        }
    }
}

impl<T> Obj<T>
where
    T: TypedData,
{
    /// Wrap the Rust type `T` in a Ruby object.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread. See [`Ruby::obj_wrap`] for the
    /// non-panicking version.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(deprecated)]
    /// use magnus::{class, define_class, prelude::*, typed_data};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// #[magnus::wrap(class = "Point")]
    /// struct Point {
    ///     x: isize,
    ///     y: isize,
    /// }
    ///
    /// let point_class = define_class("Point", class::object()).unwrap();
    ///
    /// let value = typed_data::Obj::wrap(Point { x: 4, y: 2 });
    /// assert!(value.is_kind_of(point_class));
    /// # let _ = Point { x: 1, y: 2 }.x + Point { x: 3, y: 4 }.y;
    /// ```
    #[cfg_attr(
        not(feature = "old-api"),
        deprecated(note = "please use `Ruby::obj_wrap` instead")
    )]
    #[cfg_attr(docsrs, doc(cfg(feature = "old-api")))]
    #[inline]
    pub fn wrap(data: T) -> Self {
        get_ruby!().obj_wrap(data)
    }

    /// Wrap the Rust type `T` in a Ruby object that is an instance of the
    /// given `class`.
    ///
    /// See also [`TypedData::class_for`].
    ///
    /// # Panics
    ///
    /// Panics if `class` is not a subclass of `<T as TypedData>::class()`, or
    /// if called from a non-Ruby thread. See [`Ruby::obj_wrap_as`] for a
    /// version that can not be called from a non-Ruby thread, so will not
    /// panic for that reason.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(deprecated)]
    /// use magnus::{class, define_class, prelude::*, typed_data};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// #[magnus::wrap(class = "Point")]
    /// struct Point {
    ///     x: isize,
    ///     y: isize,
    /// }
    ///
    /// let point_class = define_class("Point", class::object()).unwrap();
    /// let point_sub_class = define_class("SubPoint", point_class).unwrap();
    ///
    /// let value = typed_data::Obj::wrap_as(Point { x: 4, y: 2 }, point_sub_class);
    /// assert!(value.is_kind_of(point_sub_class));
    /// assert!(value.is_kind_of(point_class));
    /// # let _ = Point { x: 1, y: 2 }.x + Point { x: 3, y: 4 }.y;
    /// ```
    ///
    /// Allowing a wrapped type to be subclassed from Ruby:
    ///
    /// (note, in this example `Point` does not have and does not call
    /// the `initialize` method, subclasses would need to override the class
    /// `new` method rather than `initialize`)
    ///
    /// ```
    /// # #![allow(deprecated)]
    /// use magnus::{
    ///     class, define_class, eval, function, method, prelude::*, typed_data, RClass, Value,
    /// };
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// #[magnus::wrap(class = "Point")]
    /// struct Point {
    ///     x: isize,
    ///     y: isize,
    /// }
    ///
    /// impl Point {
    ///     fn new(class: RClass, x: isize, y: isize) -> typed_data::Obj<Self> {
    ///         typed_data::Obj::wrap_as(Self { x, y }, class)
    ///     }
    /// }
    /// let point_class = define_class("Point", class::object()).unwrap();
    /// point_class
    ///     .define_singleton_method("new", method!(Point::new, 2))
    ///     .unwrap();
    /// point_class
    ///     .define_singleton_method("inherited", function!(RClass::undef_default_alloc_func, 1))
    ///     .unwrap();
    ///
    /// let value: Value = eval(
    ///     r#"
    ///       class SubPoint < Point
    ///       end
    ///       SubPoint.new(4, 2)
    ///     "#,
    /// )
    /// .unwrap();
    ///
    /// assert!(value.is_kind_of(class::object().const_get::<_, RClass>("SubPoint").unwrap()));
    /// assert!(value.is_kind_of(point_class));
    /// # let _ = Point { x: 1, y: 2 }.x + Point { x: 3, y: 4 }.y;
    /// ```
    #[cfg_attr(
        not(feature = "old-api"),
        deprecated(note = "please use `Ruby::obj_wrap_as` instead")
    )]
    #[cfg_attr(docsrs, doc(cfg(feature = "old-api")))]
    #[inline]
    pub fn wrap_as(data: T, class: RClass) -> Self {
        get_ruby!().obj_wrap_as(data, class)
    }
}

impl<T> Deref for Obj<T>
where
    T: TypedData,
{
    type Target = T;

    /// Dereference to the Rust type wrapped in the Ruby object `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby};
    ///
    /// #[magnus::wrap(class = "Point")]
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Point {
    ///     x: isize,
    ///     y: isize,
    /// }
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     ruby.define_class("Point", ruby.class_object())?;
    ///     let value = ruby.obj_wrap(Point { x: 4, y: 2 });
    ///
    ///     assert_eq!(&*value, &Point { x: 4, y: 2 });
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    fn deref(&self) -> &Self::Target {
        // Since we've already validated the inner during `TryConvert` via `RTypedData::get`, we
        // can skip the extra checks and libruby calls and just access the data directly.
        unsafe {
            let data_ptr = RTYPEDDATA_GET_DATA(self.inner.as_rb_value()) as *mut Self::Target;
            &*data_ptr
        }
    }
}

impl<T> fmt::Display for Obj<T>
where
    T: TypedData,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl<T> fmt::Debug for Obj<T>
where
    T: TypedData,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl<T> IntoValue for Obj<T>
where
    T: TypedData,
{
    #[inline]
    fn into_value_with(self, handle: &Ruby) -> Value {
        self.inner.into_value_with(handle)
    }
}

impl<T> From<Obj<T>> for RTypedData
where
    T: TypedData,
{
    fn from(val: Obj<T>) -> Self {
        val.inner
    }
}

impl<T> Object for Obj<T> where T: TypedData {}

unsafe impl<T> private::ReprValue for Obj<T> where T: TypedData {}

impl<T> ReprValue for Obj<T> where T: TypedData {}

impl<T> TryConvert for Obj<T>
where
    T: TypedData,
{
    fn try_convert(val: Value) -> Result<Self, Error> {
        let handle = Ruby::get_with(val);
        let inner = RTypedData::from_value(val).ok_or_else(|| {
            Error::new(
                handle.exception_type_error(),
                format!(
                    "no implicit conversion of {} into {}",
                    unsafe { val.classname() },
                    T::class(&handle)
                ),
            )
        })?;

        // check it really does contain a T
        inner.get::<T>()?;

        Ok(Self {
            inner,
            phantom: PhantomData,
        })
    }
}

/// A trait for types that can be used with the `rb_gc_writebarrier` API.
pub trait Writebarrier: ReprValue {
    /// Inform Ruby that `self` contains a reference to `new`.
    ///
    /// If you have a Rust type that contains Ruby values, and itself is
    /// wrapped as a Ruby object, and you choose to enable the `wb_protected`
    /// flag so that it can participate in generational GC then all operations
    /// that add a Ruby value to your data type must call this function.
    ///
    /// The write barrier is hard to get right. Magnus recommends you do not
    /// enable the `wb_protected` flag, and thus you don't need to use this function.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::cell::RefCell;
    ///
    /// use magnus::{
    ///     function, gc, method,
    ///     prelude::*,
    ///     typed_data::{Obj, Writebarrier},
    ///     value::Opaque,
    ///     DataTypeFunctions, Error, Ruby, TypedData, Value,
    /// };
    ///
    /// #[derive(TypedData)]
    /// #[magnus(class = "MyVec", free_immediately, mark, wb_protected)]
    /// struct MyVec {
    ///     values: RefCell<Vec<Opaque<Value>>>,
    /// }
    ///
    /// impl DataTypeFunctions for MyVec {
    ///     fn mark(&self, marker: &gc::Marker) {
    ///         marker.mark_slice(self.values.borrow().as_slice());
    ///     }
    /// }
    ///
    /// impl MyVec {
    ///     fn new() -> Self {
    ///         Self {
    ///             values: RefCell::new(Vec::new()),
    ///         }
    ///     }
    ///
    ///     fn push(ruby: &Ruby, rb_self: Obj<Self>, val: Value) -> Obj<Self> {
    ///         rb_self.values.borrow_mut().push(val.into());
    ///         rb_self.writebarrier(rb_self);
    ///         rb_self
    ///     }
    /// }
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let class = ruby.define_class("MyVec", ruby.class_object())?;
    ///     class.define_singleton_method("new", function!(MyVec::new, 0))?;
    ///     class.define_method("push", method!(MyVec::push, 1))?;
    ///
    ///     let _: Value = ruby.eval(
    ///         r#"
    ///             vec = MyVec.new
    ///             vec.push("test")
    ///             vec.push("example")
    ///         "#,
    ///     )?;
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap();
    /// ```
    fn writebarrier<T>(&self, young: T)
    where
        T: Mark,
    {
        unsafe { rb_gc_writebarrier(self.as_rb_value(), young.raw()) };
    }

    /// Opts `self` out of generational GC / write barrier protection.
    ///
    /// After calling this function `self` will not participate in generational
    /// GC and will always be scanned during a GC.
    /// See [`RTypedData::writebarrier`].
    fn writebarrier_unprotect<T, U>(&self) {
        unsafe { rb_gc_writebarrier_unprotect(self.as_rb_value()) };
    }
}

impl Writebarrier for RTypedData {}

impl<T> Writebarrier for Obj<T> where T: TypedData {}

/// Trait for a Ruby-compatible `#hash` method.
///
/// Automatically implemented for any type implementing [`std::hash::Hash`].
///
/// See also [`Dup`], [`Inspect`], [`IsEql`], and [`typed_data::Cmp`](Cmp).
///
/// # Examples
///
/// ```
/// use std::hash::Hasher;
///
/// use magnus::{
///     function, gc, method, prelude::*, typed_data, value::Opaque, DataTypeFunctions, Error,
///     Ruby, TypedData, Value,
/// };
///
/// #[derive(TypedData)]
/// #[magnus(class = "Pair", free_immediately, mark)]
/// struct Pair {
///     #[magnus(opaque_attr_reader)]
///     a: Opaque<Value>,
///     #[magnus(opaque_attr_reader)]
///     b: Opaque<Value>,
/// }
///
/// impl Pair {
///     fn new(a: Value, b: Value) -> Self {
///         Self {
///             a: a.into(),
///             b: b.into(),
///         }
///     }
/// }
///
/// impl DataTypeFunctions for Pair {
///     fn mark(&self, marker: &gc::Marker) {
///         marker.mark(self.a);
///         marker.mark(self.b);
///     }
/// }
///
/// impl std::hash::Hash for Pair {
///     fn hash<H: Hasher>(&self, state: &mut H) {
///         state.write_i64(
///             self.a()
///                 .hash()
///                 .expect("#hash should not fail")
///                 .to_i64()
///                 .expect("#hash result guaranteed to be <= i64"),
///         );
///         state.write_i64(
///             self.b()
///                 .hash()
///                 .expect("#hash should not fail")
///                 .to_i64()
///                 .expect("#hash result guaranteed to be <= i64"),
///         );
///     }
/// }
///
/// impl PartialEq for Pair {
///     fn eq(&self, other: &Self) -> bool {
///         self.a().eql(other.a()).unwrap_or(false) && self.b().eql(other.b()).unwrap_or(false)
///     }
/// }
///
/// impl Eq for Pair {}
///
/// fn example(ruby: &Ruby) -> Result<(), Error> {
///     let class = ruby.define_class("Pair", ruby.class_object())?;
///     class.define_singleton_method("new", function!(Pair::new, 2))?;
///     class.define_method("hash", method!(<Pair as typed_data::Hash>::hash, 0))?;
///     class.define_method("eql?", method!(<Pair as typed_data::IsEql>::is_eql, 1))?;
///
///     let a = Pair::new(
///         ruby.str_new("foo").as_value(),
///         ruby.integer_from_i64(1).as_value(),
///     );
///     let hash = ruby.hash_new();
///     hash.aset(a, "test value")?;
///
///     let b = Pair::new(
///         ruby.str_new("foo").as_value(),
///         ruby.integer_from_i64(1).as_value(),
///     );
///     assert_eq!("test value", hash.fetch::<_, String>(b)?);
///
///     let c = Pair::new(
///         ruby.str_new("bar").as_value(),
///         ruby.integer_from_i64(2).as_value(),
///     );
///     assert!(hash.get(c).is_none());
///
///     Ok(())
/// }
/// # Ruby::init(example).unwrap()
/// ```
pub trait Hash {
    // Docs at trait level.
    #![allow(missing_docs)]
    fn hash(&self) -> i64;
}

impl<T> Hash for T
where
    T: std::hash::Hash,
{
    fn hash(&self) -> i64 {
        let mut hasher = DefaultHasher::new();
        std::hash::Hash::hash(self, &mut hasher);
        // Ensure the Rust usize hash converts nicely to Ruby's expected range
        // if we return usize it'd truncate to 0 for anything negative.
        hasher.finish() as i64
    }
}

/// Trait for a Ruby-compatible `#eql?` method.
///
/// Automatically implemented for any type implementing [`Eq`] and
/// [`TryConvert`].
///
/// See also [`Dup`], [`Inspect`], [`typed_data::Cmp`](Cmp), and
/// [`typed_data::Hash`](Hash).
///
/// # Examples
///
/// ```
/// use std::hash::Hasher;
///
/// use magnus::{
///     function, gc, method, prelude::*, typed_data, value::Opaque, DataTypeFunctions, Error,
///     Ruby, TypedData, Value,
/// };
///
/// #[derive(TypedData)]
/// #[magnus(class = "Pair", free_immediately, mark)]
/// struct Pair {
///     #[magnus(opaque_attr_reader)]
///     a: Opaque<Value>,
///     #[magnus(opaque_attr_reader)]
///     b: Opaque<Value>,
/// }
///
/// impl Pair {
///     fn new(a: Value, b: Value) -> Self {
///         Self {
///             a: a.into(),
///             b: b.into(),
///         }
///     }
/// }
///
/// impl DataTypeFunctions for Pair {
///     fn mark(&self, marker: &gc::Marker) {
///         marker.mark(self.a);
///         marker.mark(self.b);
///     }
/// }
///
/// impl std::hash::Hash for Pair {
///     fn hash<H: Hasher>(&self, state: &mut H) {
///         state.write_i64(
///             self.a()
///                 .hash()
///                 .expect("#hash should not fail")
///                 .to_i64()
///                 .expect("#hash result guaranteed to be <= i64"),
///         );
///         state.write_i64(
///             self.b()
///                 .hash()
///                 .expect("#hash should not fail")
///                 .to_i64()
///                 .expect("#hash result guaranteed to be <= i64"),
///         );
///     }
/// }
///
/// impl PartialEq for Pair {
///     fn eq(&self, other: &Self) -> bool {
///         self.a().eql(other.a()).unwrap_or(false) && self.b().eql(other.b()).unwrap_or(false)
///     }
/// }
///
/// impl Eq for Pair {}
///
/// fn example(ruby: &Ruby) -> Result<(), Error> {
///     let class = ruby.define_class("Pair", ruby.class_object())?;
///     class.define_singleton_method("new", function!(Pair::new, 2))?;
///     class.define_method("hash", method!(<Pair as typed_data::Hash>::hash, 0))?;
///     class.define_method("eql?", method!(<Pair as typed_data::IsEql>::is_eql, 1))?;
///
///     let a = Pair::new(
///         ruby.str_new("foo").as_value(),
///         ruby.integer_from_i64(1).as_value(),
///     );
///     let hash = ruby.hash_new();
///     hash.aset(a, "test value")?;
///
///     let b = Pair::new(
///         ruby.str_new("foo").as_value(),
///         ruby.integer_from_i64(1).as_value(),
///     );
///     assert_eq!("test value", hash.fetch::<_, String>(b)?);
///
///     let c = Pair::new(
///         ruby.str_new("bar").as_value(),
///         ruby.integer_from_i64(2).as_value(),
///     );
///     assert!(hash.get(c).is_none());
///
///     Ok(())
/// }
/// # Ruby::init(example).unwrap()
/// ```
pub trait IsEql {
    // Docs at trait level.
    #![allow(missing_docs)]
    fn is_eql(&self, other: Value) -> bool;
}

impl<'a, T> IsEql for T
where
    T: Eq + 'a,
    &'a T: TryConvert,
{
    fn is_eql(&self, other: Value) -> bool {
        <&'a T>::try_convert(other)
            .map(|o| self == o)
            .unwrap_or(false)
    }
}

/// Trait for a Ruby-compatible `#<=>` method.
///
/// Automatically implemented for any type implementing [`PartialOrd`] and
/// [`TryConvert`].
///
/// See also [`Dup`], [`Inspect`], [`IsEql`] and [`typed_data::Hash`](Hash).
///
/// # Examples
///
/// ```
/// use std::cmp::Ordering;
///
/// use magnus::{
///     function, gc, method, prelude::*, rb_assert, typed_data, value::Opaque, DataTypeFunctions,
///     Error, Module, Ruby, TypedData, Value,
/// };
///
/// #[derive(TypedData)]
/// #[magnus(class = "Pair", free_immediately, mark)]
/// struct Pair {
///     #[magnus(opaque_attr_reader)]
///     a: Opaque<Value>,
///     #[magnus(opaque_attr_reader)]
///     b: Opaque<Value>,
/// }
///
/// impl Pair {
///     fn new(a: Value, b: Value) -> Self {
///         Self {
///             a: a.into(),
///             b: b.into(),
///         }
///     }
/// }
///
/// impl DataTypeFunctions for Pair {
///     fn mark(&self, marker: &gc::Marker) {
///         marker.mark(self.a);
///         marker.mark(self.b);
///     }
/// }
///
/// impl PartialEq for Pair {
///     fn eq(&self, other: &Self) -> bool {
///         self.a().eql(other.a()).unwrap_or(false) && self.b().eql(other.b()).unwrap_or(false)
///     }
/// }
///
/// impl PartialOrd for Pair {
///     fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
///         let a = self
///             .a()
///             .funcall("<=>", (other.a(),))
///             .ok()
///             .map(|o: i64| o.cmp(&0))?;
///         match a {
///             Ordering::Less | Ordering::Greater => Some(a),
///             Ordering::Equal => self
///                 .b()
///                 .funcall("<=>", (other.b(),))
///                 .ok()
///                 .map(|o: i64| o.cmp(&0)),
///         }
///     }
/// }
///
/// fn example(ruby: &Ruby) -> Result<(), Error> {
///     let class = ruby.define_class("Pair", ruby.class_object())?;
///     class.define_singleton_method("new", function!(Pair::new, 2))?;
///     class.define_method("<=>", method!(<Pair as typed_data::Cmp>::cmp, 1))?;
///     class.include_module(ruby.module_comparable())?;
///
///     let a = Pair::new(
///         ruby.str_new("foo").as_value(),
///         ruby.integer_from_i64(1).as_value(),
///     );
///     let b = Pair::new(
///         ruby.str_new("foo").as_value(),
///         ruby.integer_from_i64(2).as_value(),
///     );
///     rb_assert!(ruby, "a < b", a, b);
///
///     let b = Pair::new(
///         ruby.str_new("foo").as_value(),
///         ruby.integer_from_i64(2).as_value(),
///     );
///     let c = Pair::new(
///         ruby.str_new("bar").as_value(),
///         ruby.integer_from_i64(1).as_value(),
///     );
///     rb_assert!(ruby, "b > c", b, c);
///
///     let a = Pair::new(
///         ruby.str_new("foo").as_value(),
///         ruby.integer_from_i64(1).as_value(),
///     );
///     let b = Pair::new(
///         ruby.str_new("foo").as_value(),
///         ruby.integer_from_i64(2).as_value(),
///     );
///     rb_assert!(ruby, "(a <=> b) == -1", a, b);
///
///     Ok(())
/// }
/// # Ruby::init(example).unwrap()
/// ```
pub trait Cmp {
    // Docs at trait level.
    #![allow(missing_docs)]
    fn cmp(&self, other: Value) -> Option<i64>;
}

impl<'a, T> Cmp for T
where
    T: PartialOrd + 'a,
    &'a T: TryConvert,
{
    fn cmp(&self, other: Value) -> Option<i64> {
        <&'a T>::try_convert(other)
            .ok()
            .and_then(|o| self.partial_cmp(o))
            .map(|o| o as i64)
    }
}

/// Trait for a Ruby-compatible `#inspect` method.
///
/// Automatically implemented for any type implementing [`Debug`].
///
/// See also [`Dup`], [`IsEql`], [`typed_data::Cmp`](Cmp), and
/// [`typed_data::Hash`](Hash).
///
/// # Examples
///
/// ```
/// use std::fmt;
///
/// use magnus::{
///     function, gc, method, prelude::*, rb_assert, typed_data, value::Opaque, DataTypeFunctions,
///     Error, Ruby, TypedData, Value,
/// };
///
/// #[derive(TypedData)]
/// #[magnus(class = "Pair", free_immediately, mark)]
/// struct Pair {
///     #[magnus(opaque_attr_reader)]
///     a: Opaque<Value>,
///     #[magnus(opaque_attr_reader)]
///     b: Opaque<Value>,
/// }
///
/// impl Pair {
///     fn new(a: Value, b: Value) -> Self {
///         Self {
///             a: a.into(),
///             b: b.into(),
///         }
///     }
/// }
///
/// impl DataTypeFunctions for Pair {
///     fn mark(&self, marker: &gc::Marker) {
///         marker.mark(self.a);
///         marker.mark(self.b);
///     }
/// }
///
/// impl fmt::Debug for Pair {
///     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
///         f.debug_struct("Pair")
///             .field("a", &self.a())
///             .field("b", &self.b())
///             .finish()
///     }
/// }
///
/// fn example(ruby: &Ruby) -> Result<(), Error> {
///     let class = ruby.define_class("Pair", ruby.class_object())?;
///     class.define_singleton_method("new", function!(Pair::new, 2))?;
///     class.define_method(
///         "inspect",
///         method!(<Pair as typed_data::Inspect>::inspect, 0),
///     )?;
///
///     let pair = Pair::new(
///         ruby.str_new("foo").as_value(),
///         ruby.integer_from_i64(1).as_value(),
///     );
///     rb_assert!(ruby, r#"pair.inspect == "Pair { a: \"foo\", b: 1 }""#, pair);
///
///     Ok(())
/// }
/// # Ruby::init(example).unwrap()
/// ```
pub trait Inspect {
    // Docs at trait level.
    #![allow(missing_docs)]
    fn inspect(&self) -> String;
}

impl<T> Inspect for T
where
    T: fmt::Debug,
{
    fn inspect(&self) -> String {
        format!("{:?}", self)
    }
}

/// Trait for a Ruby-compatible `#dup` and `#clone` methods.
///
/// Automatically implemented for any type implementing [`Clone`].
///
/// See also [`Inspect`], [`IsEql`], [`typed_data::Cmp`](Cmp), and
/// [`typed_data::Hash`](Hash).
///
/// # Examples
///
/// ```
/// use magnus::{
///     function, gc, method, prelude::*, rb_assert, typed_data, value::Opaque, DataTypeFunctions,
///     Error, Ruby, TypedData, Value,
/// };
///
/// #[derive(TypedData, Clone)]
/// #[magnus(class = "Pair", free_immediately, mark)]
/// struct Pair {
///     a: Opaque<Value>,
///     b: Opaque<Value>,
/// }
///
/// impl Pair {
///     fn new(a: Value, b: Value) -> Self {
///         Self {
///             a: a.into(),
///             b: b.into(),
///         }
///     }
/// }
///
/// impl DataTypeFunctions for Pair {
///     fn mark(&self, marker: &gc::Marker) {
///         marker.mark(self.a);
///         marker.mark(self.b);
///     }
/// }
///
/// fn example(ruby: &Ruby) -> Result<(), Error> {
///     let class = ruby.define_class("Pair", ruby.class_object())?;
///     class.define_singleton_method("new", function!(Pair::new, 2))?;
///     class.define_method("dup", method!(<Pair as typed_data::Dup>::dup, 0))?;
///     class.define_method("clone", method!(<Pair as typed_data::Dup>::clone, -1))?;
///
///     let a = Pair::new(
///         ruby.str_new("foo").as_value(),
///         ruby.integer_from_i64(1).as_value(),
///     );
///     rb_assert!(ruby, "b = a.dup; a.object_id != b.object_id", a);
///
///     Ok(())
/// }
/// # Ruby::init(example).unwrap()
/// ```
pub trait Dup: Sized {
    // Docs at trait level.
    #![allow(missing_docs)]
    fn dup(&self) -> Self;
    fn clone(rbself: Obj<Self>, args: &[Value]) -> Result<Obj<Self>, Error>;
}

impl<T> Dup for T
where
    T: Clone + TypedData,
{
    fn dup(&self) -> Self {
        self.clone()
    }

    fn clone(rbself: Obj<Self>, args: &[Value]) -> Result<Obj<Self>, Error> {
        let args = scan_args::<(), (), (), (), _, ()>(args)?;
        let kwargs =
            get_kwargs::<_, (), (Option<Option<bool>>,), ()>(args.keywords, &[], &["freeze"])?;
        let (freeze,) = kwargs.optional;
        let freeze = freeze.flatten();

        let clone = Ruby::get_with(rbself).obj_wrap((*rbself).clone());
        let class_clone = unsafe { rb_singleton_class_clone(rbself.as_rb_value()) };
        unsafe { rb_obj_reveal(clone.as_rb_value(), class_clone) };
        unsafe { rb_singleton_class_attached(class_clone, clone.as_rb_value()) };
        match freeze {
            Some(true) => clone.freeze(),
            None if rbself.is_frozen() => clone.freeze(),
            _ => (),
        }
        Ok(clone)
    }
}
