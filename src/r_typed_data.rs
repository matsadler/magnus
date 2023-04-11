use std::{fmt, ptr::NonNull};

use rb_sys::{self, rb_check_typeddata, rb_data_typed_object_wrap, ruby_value_type};

use crate::{
    class::RClass,
    error::{protect, Error},
    into_value::IntoValue,
    module::Module,
    object::Object,
    typed_data::TypedData,
    value::{
        private::{self, ReprValue as _},
        NonZeroValue, ReprValue, Value,
    },
    Ruby,
};

/// # `RTypedData`
#[allow(missing_docs)]
impl Ruby {
    #[inline]
    pub fn wrap<T>(&self, data: T) -> RTypedData
    where
        T: TypedData,
    {
        let class = T::class_for(self, &data);
        self.wrap_as(data, class)
    }

    pub fn wrap_as<T>(&self, data: T, class: RClass) -> RTypedData
    where
        T: TypedData,
    {
        debug_assert!(
            class.is_inherited(T::class(self)),
            "{} is not a subclass of {}",
            class,
            T::class(self)
        );
        let boxed = Box::new(data);
        unsafe {
            let value_ptr = rb_data_typed_object_wrap(
                class.as_rb_value(),
                Box::into_raw(boxed) as *mut _,
                T::data_type().as_rb_data_type() as *const _,
            );
            RTypedData(NonZeroValue::new_unchecked(Value::new(value_ptr)))
        }
    }
}

/// A Value pointer to a RTypedData struct, Ruby’s internal representation of
/// objects that wrap foreign types.
///
/// See also [`typed_data::Obj`](crate::typed_data::Obj).
///
/// See the [`ReprValue`] and [`Object`] traits for additional methods
/// available on this type.
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
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{class, define_class, prelude::*, RTypedData};
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
    /// let value = RTypedData::wrap(Point { x: 4, y: 2 });
    /// assert!(value.is_kind_of(point_class));
    /// # let _ = Point { x: 1, y: 2 }.x + Point { x: 3, y: 4 }.y;
    /// ```
    #[cfg(feature = "friendly-api")]
    #[inline]
    pub fn wrap<T>(data: T) -> Self
    where
        T: TypedData,
    {
        get_ruby!().wrap(data)
    }

    /// Wrap the Rust type `T` in a Ruby object that is an instance of the
    /// given `class`.
    ///
    /// See also [`TypedData::class_for`].
    ///
    /// # Panics
    ///
    /// Panics if `class` is not a subclass of `<T as TypedData>::class()`, or
    /// if called from a non-Ruby thread.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{class, define_class, prelude::*, RTypedData};
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
    /// let value = RTypedData::wrap_as(Point { x: 4, y: 2 }, point_sub_class);
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
    /// use magnus::{
    ///     class, define_class, eval, function, method, prelude::*, RClass, RTypedData, Value,
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
    ///     fn new(class: RClass, x: isize, y: isize) -> RTypedData {
    ///         RTypedData::wrap_as(Self { x, y }, class)
    ///     }
    /// }
    ///
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
    ///     class SubPoint < Point
    ///     end
    ///     SubPoint.new(4, 2)
    /// "#,
    /// )
    /// .unwrap();
    ///
    /// assert!(value.is_kind_of(class::object().const_get::<_, RClass>("SubPoint").unwrap()));
    /// assert!(value.is_kind_of(point_class));
    /// # let _ = Point { x: 1, y: 2 }.x + Point { x: 3, y: 4 }.y;
    /// ```
    #[cfg(feature = "friendly-api")]
    #[inline]
    pub fn wrap_as<T>(data: T, class: RClass) -> Self
    where
        T: TypedData,
    {
        get_ruby!().wrap_as(data, class)
    }

    /// Get a reference to the Rust type wrapped in the Ruby object `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{class, define_class, RTypedData};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// #[magnus::wrap(class = "Point")]
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Point {
    ///     x: isize,
    ///     y: isize,
    /// }
    ///
    /// define_class("Point", class::object()).unwrap();
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
    pub(crate) unsafe fn get_unconstrained<'a, T>(self) -> Result<&'a T, Error>
    where
        T: TypedData,
    {
        debug_assert_value!(self);
        let handle = Ruby::get_with(self);
        let mut res = None;
        let _ = protect(|| {
            res = (rb_check_typeddata(
                self.as_rb_value(),
                T::data_type().as_rb_data_type() as *const _,
            ) as *const T)
                .as_ref();
            handle.qnil()
        });
        res.ok_or_else(|| {
            Error::new(
                handle.exception_type_error(),
                format!(
                    "no implicit conversion of {} into {}",
                    self.classname(),
                    T::class(&handle)
                ),
            )
        })
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

impl IntoValue for RTypedData {
    fn into_value_with(self, _: &Ruby) -> Value {
        self.0.get()
    }
}

impl Object for RTypedData {}

unsafe impl private::ReprValue for RTypedData {}

impl ReprValue for RTypedData {}
