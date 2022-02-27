//! Types and functions for working with Ruby modules.

use std::{ffi::CString, fmt, mem::transmute, ops::Deref};

use crate::{
    class::RClass,
    debug_assert_value,
    error::{protect, Error},
    method::Method,
    object::Object,
    ruby_sys::{
        rb_class_inherited_p, rb_const_get, rb_define_class_id_under, rb_define_method_id,
        rb_define_module_function, rb_define_module_id_under, rb_define_private_method,
        rb_define_protected_method, rb_mComparable, rb_mEnumerable, rb_mErrno, rb_mFileTest,
        rb_mGC, rb_mKernel, rb_mMath, rb_mProcess, rb_mWaitReadable, rb_mWaitWritable,
        ruby_value_type, VALUE,
    },
    try_convert::TryConvert,
    value::{Id, NonZeroValue, Value},
};

/// A Value pointer to a RModule struct, Ruby's internal representation of
/// modules.
///
/// See the [`Module`] trait for defining instance methods and nested
/// classes/modules.
/// See the [`Object`] trait for defining singlton methods (aka class methods).
///
/// All [`Value`] methods should be available on this type through [`Deref`],
/// but some may be missed by this documentation.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RModule(NonZeroValue);

impl RModule {
    /// Return `Some(RModule)` if `val` is a `RModule`, `None` otherwise.
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            (val.rb_type() == ruby_value_type::RUBY_T_MODULE)
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        Self(NonZeroValue::new_unchecked(Value::new(val)))
    }

    /// Define a method in `self`'s scope as a 'module function'. This method
    /// will be visible as a public 'class' method on the module and a private
    /// instance method on any object including the module.
    pub fn define_module_function<M>(self, name: &str, func: M)
    where
        M: Method,
    {
        debug_assert_value!(self);
        let name = CString::new(name).unwrap();
        unsafe {
            rb_define_module_function(
                self.as_rb_value(),
                name.as_ptr(),
                transmute(func.as_ptr()),
                M::arity().into(),
            );
        }
    }
}

impl Deref for RModule {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
    }
}

impl fmt::Display for RModule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for RModule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl From<RModule> for Value {
    fn from(val: RModule) -> Self {
        *val
    }
}

impl Object for RModule {}
impl Module for RModule {}

impl TryConvert for RModule {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        Self::from_value(*val).ok_or_else(|| {
            Error::type_error(format!(
                "no implicit conversion of {} into Module",
                unsafe { val.classname() },
            ))
        })
    }
}

/// Functions available on both classes and modules.
pub trait Module: Object + Deref<Target = Value> + Copy {
    /// Define a class in `self`'s scope.
    fn define_class<T: Into<Id>>(self, name: T, superclass: RClass) -> Result<RClass, Error> {
        debug_assert_value!(self);
        debug_assert_value!(superclass);
        let id = name.into();
        let superclass = superclass.as_rb_value();
        unsafe {
            let res = protect(|| {
                Value::new(rb_define_class_id_under(
                    self.as_rb_value(),
                    id.as_rb_id(),
                    superclass,
                ))
            });
            res.map(|v| RClass::from_value(v).unwrap())
        }
    }

    /// Define a module in `self`'s scope.
    fn define_module<T: Into<Id>>(self, name: T) -> Result<RModule, Error> {
        let id = name.into();
        unsafe {
            let res = protect(|| {
                Value::new(rb_define_module_id_under(self.as_rb_value(), id.as_rb_id()))
            });
            res.map(|v| RModule::from_value(v).unwrap())
        }
    }

    /// Get the value for the constant `name` within `self`'s scope.
    fn const_get<T, U>(self, name: T) -> Result<U, Error>
    where
        T: Into<Id>,
        U: TryConvert,
    {
        debug_assert_value!(self);
        let id = name.into();
        let res =
            unsafe { protect(|| Value::new(rb_const_get(self.as_rb_value(), id.as_rb_id()))) };
        res.and_then(|v| v.try_convert())
    }

    /// Returns whether or not `other` inherits from `self`.
    ///
    /// Classes including a module are considered to inherit from that module.
    fn is_inherited<T>(self, other: T) -> bool
    where
        T: Deref<Target = Value> + Module,
    {
        unsafe {
            Value::new(rb_class_inherited_p(
                self.as_rb_value(),
                other.as_rb_value(),
            ))
            .to_bool()
        }
    }

    /// Define a method in `self`'s scope.
    fn define_method<T, M>(self, name: T, func: M)
    where
        T: Into<Id>,
        M: Method,
    {
        debug_assert_value!(self);
        let id = name.into();
        unsafe {
            rb_define_method_id(
                self.as_rb_value(),
                id.as_rb_id(),
                transmute(func.as_ptr()),
                M::arity().into(),
            );
        }
    }

    /// Define a private method in `self`'s scope.
    fn define_private_method<M>(self, name: &str, func: M)
    where
        M: Method,
    {
        debug_assert_value!(self);
        let name = CString::new(name).unwrap();
        unsafe {
            rb_define_private_method(
                self.as_rb_value(),
                name.as_ptr(),
                transmute(func.as_ptr()),
                M::arity().into(),
            );
        }
    }

    /// Define a protected method in `self`'s scope.
    fn define_protected_method<M>(self, name: &str, func: M)
    where
        M: Method,
    {
        debug_assert_value!(self);
        let name = CString::new(name).unwrap();
        unsafe {
            rb_define_protected_method(
                self.as_rb_value(),
                name.as_ptr(),
                transmute(func.as_ptr()),
                M::arity().into(),
            );
        }
    }
}

/// Return Ruby's `Comparable` module.
#[inline]
pub fn comparable() -> RModule {
    unsafe { RModule::from_rb_value_unchecked(rb_mComparable) }
}

/// Return Ruby's `Enumerable` module.
#[inline]
pub fn enumerable() -> RModule {
    unsafe { RModule::from_rb_value_unchecked(rb_mEnumerable) }
}

/// Return Ruby's `Errno` module.
#[inline]
pub fn errno() -> RModule {
    unsafe { RModule::from_rb_value_unchecked(rb_mErrno) }
}

/// Return Ruby's `FileTest` module.
#[inline]
pub fn file_test() -> RModule {
    unsafe { RModule::from_rb_value_unchecked(rb_mFileTest) }
}

/// Return Ruby's `GC` module.
#[inline]
pub fn gc() -> RModule {
    unsafe { RModule::from_rb_value_unchecked(rb_mGC) }
}

/// Return Ruby's `Kernel` module.
#[inline]
pub fn kernel() -> RModule {
    unsafe { RModule::from_rb_value_unchecked(rb_mKernel) }
}

/// Return Ruby's `Math` module.
#[inline]
pub fn math() -> RModule {
    unsafe { RModule::from_rb_value_unchecked(rb_mMath) }
}

/// Return Ruby's `Process` module.
#[inline]
pub fn process() -> RModule {
    unsafe { RModule::from_rb_value_unchecked(rb_mProcess) }
}

/// Return Ruby's `WaitReadable` module.
#[inline]
pub fn wait_readable() -> RModule {
    unsafe { RModule::from_rb_value_unchecked(rb_mWaitReadable) }
}

/// Return Ruby's `WaitWritable` module.
#[inline]
pub fn wait_writable() -> RModule {
    unsafe { RModule::from_rb_value_unchecked(rb_mWaitWritable) }
}
