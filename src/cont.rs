//! Types and functions for working with Ruby fibers.

use std::fmt;

use rb_sys::{rb_fiber_alive_p, rb_obj_is_fiber, Qtrue, VALUE};

use crate::{
    value::{private, NonZeroValue, ReprValue},
    Error, IntoValue, Object, Ruby, TryConvert, Value,
};

/// See the [`ReprValue`] and [`Object`] traits for additional methods
/// available on this type. See [`Ruby`](Ruby#proc) for methods to create a
/// `Proc`.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Fiber(NonZeroValue);

impl Fiber {
    /// Return `Some(Fiber)` if `val` is a `Fiber`, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{cont::Fiber, eval, Value};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let val: Value = eval("Fiber.new { :foo }").unwrap();
    /// assert!(Fiber::from_value(val).is_some());
    ///
    /// let val: Value = eval("1 + 2").unwrap();
    /// assert!(Fiber::from_value(val).is_none());
    /// ```
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        let val = val.as_rb_value();
        unsafe {
            Value::new(rb_obj_is_fiber(val))
                .to_bool()
                .then(|| Self::from_rb_value_unchecked(val))
        }
    }

    /// Check whether the fiber is alive and can be resumed.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{cont::Fiber, eval, Value};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let val: Value = eval("Fiber.new { :foo }").unwrap();
    /// let fiber = Fiber::from_value(val).unwrap();
    /// assert!(fiber.is_alive());
    ///
    /// let val: Value = eval("Fiber.new { :bar }.tap(&:resume)").unwrap();
    /// let fiber = Fiber::from_value(val).unwrap();
    /// assert!(!fiber.is_alive());
    /// ```
    pub fn is_alive(self) -> bool {
        unsafe { rb_fiber_alive_p(private::ReprValue::as_rb_value(self)) == Qtrue.into() }
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        Self(NonZeroValue::new_unchecked(Value::new(val)))
    }
}

impl fmt::Display for Fiber {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe {
            private::ReprValue::to_s_infallible(self)
        })
    }
}

impl fmt::Debug for Fiber {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl IntoValue for Fiber {
    fn into_value_with(self, _: &Ruby) -> Value {
        self.0.get()
    }
}

impl TryConvert for Fiber {
    fn try_convert(val: Value) -> Result<Self, Error> {
        match Self::from_value(val) {
            Some(v) => Ok(v),
            None => Err(Error::new(
                Ruby::get_with(val).exception_type_error(),
                format!("no implicit conversion of {} into Class", unsafe {
                    val.classname()
                },),
            )),
        }
    }
}

impl Object for Fiber {}

unsafe impl private::ReprValue for Fiber {}

impl ReprValue for Fiber {}
