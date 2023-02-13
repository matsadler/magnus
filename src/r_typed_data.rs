use std::{fmt, ptr::NonNull};

use rb_sys::{self, rb_check_typeddata, rb_data_typed_object_wrap, ruby_value_type};

use crate::{
    error::{protect, Error},
    exception,
    into_value::IntoValue,
    object::Object,
    ruby_handle::RubyHandle,
    typed_data::TypedData,
    value::{
        private::{self, ReprValue as _},
        NonZeroValue, ReprValue, Value, QNIL,
    },
};

impl RubyHandle {
    pub fn wrap<T>(&self, data: T) -> RTypedData
    where
        T: TypedData,
    {
        let class = T::class_for(&data);
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
    /// use magnus::{define_class, prelude::*, RTypedData};
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
    #[inline]
    pub fn wrap<T>(data: T) -> Self
    where
        T: TypedData,
    {
        get_ruby!().wrap(data)
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
    pub(crate) unsafe fn get_unconstrained<'a, T>(self) -> Result<&'a T, Error>
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
    fn into_value_with(self, _: &RubyHandle) -> Value {
        self.0.get()
    }
}

impl Object for RTypedData {}

unsafe impl private::ReprValue for RTypedData {
    fn as_value(self) -> Value {
        self.0.get()
    }

    unsafe fn from_value_unchecked(val: Value) -> Self {
        Self(NonZeroValue::new_unchecked(val))
    }
}

impl ReprValue for RTypedData {}
