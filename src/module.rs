//! Types and functions for working with Ruby modules.
//!
//! See also [`Ruby`](Ruby#core-modules) for more module related methods.

use std::{ffi::CString, fmt, mem::transmute, os::raw::c_int};

use rb_sys::{
    rb_alias, rb_attr, rb_class_inherited_p, rb_const_get, rb_const_set, rb_define_class_id_under,
    rb_define_method_id, rb_define_module_function, rb_define_module_id_under,
    rb_define_private_method, rb_define_protected_method, rb_include_module, rb_mComparable,
    rb_mEnumerable, rb_mErrno, rb_mFileTest, rb_mGC, rb_mKernel, rb_mMath, rb_mProcess,
    rb_mWaitReadable, rb_mWaitWritable, rb_mod_ancestors, rb_module_new, rb_prepend_module,
    ruby_value_type, VALUE,
};

use crate::{
    class::{Class, RClass},
    error::{protect, Error},
    exception::ExceptionClass,
    into_value::IntoValue,
    method::Method,
    object::Object,
    r_array::RArray,
    try_convert::TryConvert,
    value::{
        private::{self, ReprValue as _},
        IntoId, NonZeroValue, ReprValue, Value,
    },
    Ruby,
};

/// # `RModule`
///
/// Functions that can be used to create Ruby modules.
///
/// See also the [`RModule`] type.
#[allow(missing_docs)]
impl Ruby {
    pub fn module_new(&self) -> RModule {
        unsafe { RModule::from_rb_value_unchecked(rb_module_new()) }
    }
}

/// A Value pointer to a RModule struct, Ruby's internal representation of
/// modules.
///
/// See the [`Module`] trait for defining instance methods and nested
/// classes/modules.
/// See the [`Object`] trait for defining singlton methods (aka class methods).
///
/// See the [`ReprValue`] trait for additional methods available on this type.
/// See [`Ruby`](Ruby#rmodule) for methods to create an `RModule`.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RModule(NonZeroValue);

impl RModule {
    /// Return `Some(RModule)` if `val` is a `RModule`, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RModule};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(RModule::from_value(eval("Enumerable").unwrap()).is_some());
    /// assert!(RModule::from_value(eval("String").unwrap()).is_none());
    /// assert!(RModule::from_value(eval("nil").unwrap()).is_none());
    /// ```
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

    /// Create a new anonymous module.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread. See [`Ruby::module_new`] for
    /// the non-panicking version.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{class, prelude::*, RModule};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let module = RModule::new();
    /// assert!(module.is_kind_of(class::module()));
    /// ```
    #[cfg(feature = "friendly-api")]
    #[inline]
    pub fn new() -> Self {
        get_ruby!().module_new()
    }

    /// Define a method in `self`'s scope as a 'module function'. This method
    /// will be visible as a public 'class' method on the module and a private
    /// instance method on any object including the module.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{define_module, eval, function, r_string, RString};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// fn greet() -> RString {
    ///     r_string!("Hello, world!")
    /// }
    ///
    /// let module = define_module("Greeting").unwrap();
    /// module
    ///     .define_module_function("greet", function!(greet, 0))
    ///     .unwrap();
    ///
    /// let res = eval::<bool>(r#"Greeting.greet == "Hello, world!""#).unwrap();
    /// assert!(res);
    ///
    /// let res = eval::<bool>(
    ///     r#"
    ///     include Greeting
    ///     greet == "Hello, world!"
    /// "#,
    /// )
    /// .unwrap();
    /// assert!(res);
    /// ```
    pub fn define_module_function<M>(self, name: &str, func: M) -> Result<(), Error>
    where
        M: Method,
    {
        debug_assert_value!(self);
        let name = CString::new(name).unwrap();
        protect(|| {
            unsafe {
                rb_define_module_function(
                    self.as_rb_value(),
                    name.as_ptr(),
                    transmute(func.as_ptr()),
                    M::arity().into(),
                )
            };
            Ruby::get_with(self).qnil()
        })?;
        Ok(())
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

impl IntoValue for RModule {
    fn into_value_with(self, _: &Ruby) -> Value {
        self.0.get()
    }
}

impl Object for RModule {}
impl Module for RModule {}

unsafe impl private::ReprValue for RModule {}

impl ReprValue for RModule {}

impl TryConvert for RModule {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Self::from_value(val).ok_or_else(|| {
            Error::new(
                Ruby::get_with(val).exception_type_error(),
                format!("no implicit conversion of {} into Module", unsafe {
                    val.classname()
                },),
            )
        })
    }
}

/// Functions available on both classes and modules.
pub trait Module: Object + ReprValue + Copy {
    /// Define a class in `self`'s scope.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{class, define_module, prelude::*};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let outer = define_module("Outer").unwrap();
    /// let inner = outer.define_class("Inner", class::object()).unwrap();
    /// assert!(inner.is_kind_of(class::class()));
    /// ```
    fn define_class<T>(self, name: T, superclass: RClass) -> Result<RClass, Error>
    where
        T: IntoId,
    {
        debug_assert_value!(self);
        debug_assert_value!(superclass);
        let id = name.into_id_with(&Ruby::get_with(self));
        let superclass = superclass.as_rb_value();
        protect(|| unsafe {
            RClass::from_rb_value_unchecked(rb_define_class_id_under(
                self.as_rb_value(),
                id.as_rb_id(),
                superclass,
            ))
        })
    }

    /// Define a module in `self`'s scope.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{class, define_module, prelude::*};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let outer = define_module("Outer").unwrap();
    /// let inner = outer.define_module("Inner").unwrap();
    /// assert!(inner.is_kind_of(class::module()));
    /// ```
    fn define_module<T>(self, name: T) -> Result<RModule, Error>
    where
        T: IntoId,
    {
        let id = name.into_id_with(&Ruby::get_with(self));
        protect(|| unsafe {
            RModule::from_rb_value_unchecked(rb_define_module_id_under(
                self.as_rb_value(),
                id.as_rb_id(),
            ))
        })
    }

    /// Define an exception class in `self`'s scope.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{define_module, exception, prelude::*};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let outer = define_module("Outer").unwrap();
    /// let inner = outer
    ///     .define_error("InnerError", exception::standard_error())
    ///     .unwrap();
    /// assert!(inner.is_inherited(exception::standard_error()));
    /// ```
    fn define_error<T>(self, name: T, superclass: ExceptionClass) -> Result<ExceptionClass, Error>
    where
        T: IntoId,
    {
        self.define_class(name, superclass.as_r_class())
            .map(|c| unsafe { ExceptionClass::from_value_unchecked(c.as_value()) })
    }

    /// Include `module` into `self`.
    ///
    /// Effectively makes `module` the superclass of `self`. See also
    /// [`prepend_module`](Module::prepend_module).
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{class, function, prelude::*, RClass, RModule};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// fn example() -> i64 {
    ///     42
    /// }
    ///
    /// let module = RModule::new();
    /// module
    ///     .define_method("example", function!(example, 0))
    ///     .unwrap();
    ///
    /// let class = RClass::new(class::object()).unwrap();
    /// class.include_module(module).unwrap();
    ///
    /// let obj = class.new_instance(()).unwrap();
    /// assert_eq!(obj.funcall::<_, _, i64>("example", ()).unwrap(), 42);
    /// ```
    fn include_module(self, module: RModule) -> Result<(), Error> {
        protect(|| {
            unsafe { rb_include_module(self.as_rb_value(), module.as_rb_value()) };
            Ruby::get_with(self).qnil()
        })?;
        Ok(())
    }

    /// Prepend `self` with `module`.
    ///
    /// Similar to [`include_module`](Module::include_module), but inserts
    /// `module` as if it were a subclass in the inheritance chain.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{call_super, eval, function, prelude::*, Error, RClass, RModule};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// fn example() -> Result<i64, Error> {
    ///     Ok(call_super::<_, i64>(())? + 2)
    /// }
    ///
    /// let module = RModule::new();
    /// module
    ///     .define_method("example", function!(example, 0))
    ///     .unwrap();
    ///
    /// let class: RClass = eval(
    ///     r#"
    ///     class Example
    ///       def example
    ///         40
    ///       end
    ///     end
    ///     Example
    /// "#,
    /// )
    /// .unwrap();
    /// class.prepend_module(module).unwrap();
    ///
    /// let obj = class.new_instance(()).unwrap();
    /// assert_eq!(obj.funcall::<_, _, i64>("example", ()).unwrap(), 42);
    /// ```
    fn prepend_module(self, module: RModule) -> Result<(), Error> {
        protect(|| {
            unsafe { rb_prepend_module(self.as_rb_value(), module.as_rb_value()) };
            Ruby::get_with(self).qnil()
        })?;
        Ok(())
    }

    /// Set the value for the constant `name` within `self`'s scope.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{class, eval, Module};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// class::array().const_set("EXAMPLE", 42).unwrap();
    ///
    /// assert_eq!(eval::<i64>("Array::EXAMPLE").unwrap(), 42);
    /// ```
    fn const_set<T, U>(self, name: T, value: U) -> Result<(), Error>
    where
        T: IntoId,
        U: IntoValue,
    {
        let handle = Ruby::get_with(self);
        let id = name.into_id_with(&handle);
        let val = value.into_value_with(&handle);
        protect(|| {
            unsafe { rb_const_set(self.as_rb_value(), id.as_rb_id(), val.as_rb_value()) };
            handle.qnil()
        })?;
        Ok(())
    }

    /// Get the value for the constant `name` within `self`'s scope.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{class, eval, Module, RClass, Value};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// eval::<Value>(
    ///     "
    ///     class Example
    ///       VALUE = 42
    ///     end
    /// ",
    /// )
    /// .unwrap();
    ///
    /// let class = class::object().const_get::<_, RClass>("Example").unwrap();
    /// assert_eq!(class.const_get::<_, i64>("VALUE").unwrap(), 42);
    /// ```
    fn const_get<T, U>(self, name: T) -> Result<U, Error>
    where
        T: IntoId,
        U: TryConvert,
    {
        debug_assert_value!(self);
        let id = name.into_id_with(&Ruby::get_with(self));
        let res =
            unsafe { protect(|| Value::new(rb_const_get(self.as_rb_value(), id.as_rb_id()))) };
        res.and_then(TryConvert::try_convert)
    }

    /// Returns whether or not `self` inherits from `other`.
    ///
    /// Classes including a module are considered to inherit from that module.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{class, prelude::*, Module, RClass};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let a = RClass::new(class::object()).unwrap();
    /// let b = RClass::new(a).unwrap();
    /// assert!(b.is_inherited(a));
    /// assert!(!a.is_inherited(b));
    /// ```
    fn is_inherited<T>(self, other: T) -> bool
    where
        T: ReprValue + Module,
    {
        unsafe {
            Value::new(rb_class_inherited_p(
                self.as_rb_value(),
                other.as_rb_value(),
            ))
            .to_bool()
        }
    }

    /// Return the classes and modules `self` inherits, includes, or prepends.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{class, eval, Module};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = class::string().ancestors();
    ///
    /// let res: bool = eval!(
    ///     "ary == [String, Comparable, Object, Kernel, BasicObject]",
    ///     ary
    /// )
    /// .unwrap();
    /// assert!(res);
    /// ```
    fn ancestors(self) -> RArray {
        unsafe { RArray::from_rb_value_unchecked(rb_mod_ancestors(self.as_rb_value())) }
    }

    /// Define a method in `self`'s scope.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{class, eval, method, Module};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// fn escape_unicode(s: String) -> String {
    ///     s.escape_unicode().to_string()
    /// }
    ///
    /// class::string()
    ///     .define_method("escape_unicode", method!(escape_unicode, 0))
    ///     .unwrap();
    ///
    /// let res = eval::<bool>(
    ///     r#""🤖\etest".escape_unicode == "\\u{1f916}\\u{1b}\\u{74}\\u{65}\\u{73}\\u{74}""#,
    /// )
    /// .unwrap();
    /// assert!(res);
    /// ```
    fn define_method<T, M>(self, name: T, func: M) -> Result<(), Error>
    where
        T: IntoId,
        M: Method,
    {
        debug_assert_value!(self);
        let handle = Ruby::get_with(self);
        let id = name.into_id_with(&handle);
        protect(|| {
            unsafe {
                rb_define_method_id(
                    self.as_rb_value(),
                    id.as_rb_id(),
                    transmute(func.as_ptr()),
                    M::arity().into(),
                )
            };
            handle.qnil()
        })?;
        Ok(())
    }

    /// Define a private method in `self`'s scope.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{class, eval, exception, function, Module, Value};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// fn percent_encode(c: char) -> String {
    ///     if c.is_ascii_alphanumeric() || c == '-' || c == '_' || c == '.' || c == '~' {
    ///         String::from(c)
    ///     } else {
    ///         format!("%{:X}", c as u32)
    ///     }
    /// }
    ///
    /// class::string()
    ///     .define_private_method("percent_encode_char", function!(percent_encode, 1))
    ///     .unwrap();
    ///
    /// eval::<Value>(
    ///     r#"
    ///     class String
    ///       def percent_encode
    ///         chars.map {|c| percent_encode_char(c)}.join("")
    ///       end
    ///     end
    /// "#,
    /// )
    /// .unwrap();
    ///
    /// let res = eval::<bool>(r#""foo bar".percent_encode == "foo%20bar""#).unwrap();
    /// assert!(res);
    ///
    /// assert!(eval::<bool>(r#"" ".percent_encode_char(" ")"#)
    ///     .unwrap_err()
    ///     .is_kind_of(exception::no_method_error()));
    /// ```
    fn define_private_method<M>(self, name: &str, func: M) -> Result<(), Error>
    where
        M: Method,
    {
        debug_assert_value!(self);
        let name = CString::new(name).unwrap();
        protect(|| {
            unsafe {
                rb_define_private_method(
                    self.as_rb_value(),
                    name.as_ptr(),
                    transmute(func.as_ptr()),
                    M::arity().into(),
                )
            };
            Ruby::get_with(self).qnil()
        })?;
        Ok(())
    }

    /// Define a protected method in `self`'s scope.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{class, eval, exception, method, Module, Value};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// fn escape_unicode(s: String) -> String {
    ///     s.escape_unicode().to_string()
    /// }
    ///
    /// fn is_invisible(c: char) -> bool {
    ///     c.is_control() || c.is_whitespace()
    /// }
    ///
    /// class::string()
    ///     .define_method("escape_unicode", method!(escape_unicode, 0))
    ///     .unwrap();
    /// class::string()
    ///     .define_protected_method("invisible?", method!(is_invisible, 0))
    ///     .unwrap();
    ///
    /// eval::<Value>(
    ///     r#"
    ///     class String
    ///       def escape_invisible
    ///         chars.map {|c| c.invisible? ? c.escape_unicode : c}.join("")
    ///       end
    ///     end
    /// "#,
    /// )
    /// .unwrap();
    ///
    /// let res: bool = eval!(
    ///     r#"
    ///     "🤖\tfoo bar".escape_invisible == "🤖\\u{9}foo\\u{20}bar"
    /// "#
    /// )
    /// .unwrap();
    /// assert!(res);
    ///
    /// assert!(eval::<bool>(r#"" ".invisible?"#)
    ///     .unwrap_err()
    ///     .is_kind_of(exception::no_method_error()));
    /// ```
    fn define_protected_method<M>(self, name: &str, func: M) -> Result<(), Error>
    where
        M: Method,
    {
        debug_assert_value!(self);
        let name = CString::new(name).unwrap();
        protect(|| {
            unsafe {
                rb_define_protected_method(
                    self.as_rb_value(),
                    name.as_ptr(),
                    transmute(func.as_ptr()),
                    M::arity().into(),
                )
            };
            Ruby::get_with(self).qnil()
        })?;
        Ok(())
    }

    /// Define public accessor methods for the attribute `name`.
    ///
    /// `name` should be **without** the preceding `@`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{class, prelude::*, Attr, Module, RClass, Value};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let class = RClass::new(class::object()).unwrap();
    /// class.define_attr("example", Attr::ReadWrite).unwrap();
    ///
    /// let obj = class.new_instance(()).unwrap();
    /// let _: Value = obj.funcall("example=", (42,)).unwrap();
    /// assert_eq!(obj.funcall::<_, _, i64>("example", ()).unwrap(), 42);
    /// ```
    fn define_attr<T>(self, name: T, rw: Attr) -> Result<(), Error>
    where
        T: IntoId,
    {
        let handle = Ruby::get_with(self);
        let id = name.into_id_with(&handle);
        protect(|| {
            unsafe {
                rb_attr(
                    self.as_rb_value(),
                    id.as_rb_id(),
                    rw.is_read() as c_int,
                    rw.is_write() as c_int,
                    0,
                )
            };
            handle.qnil()
        })?;
        Ok(())
    }

    /// Alias the method `src` of `self` as `dst`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{class, function, prelude::*, Module, RClass};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// fn example() -> i64 {
    ///     42
    /// }
    ///
    /// let class = RClass::new(class::object()).unwrap();
    /// class
    ///     .define_method("example", function!(example, 0))
    ///     .unwrap();
    /// class.define_alias("test", "example").unwrap();
    ///
    /// let obj = class.new_instance(()).unwrap();
    /// assert_eq!(obj.funcall::<_, _, i64>("test", ()).unwrap(), 42);
    /// ```
    fn define_alias<T, U>(self, dst: T, src: U) -> Result<(), Error>
    where
        T: IntoId,
        U: IntoId,
    {
        let handle = Ruby::get_with(self);
        let d_id = dst.into_id_with(&handle);
        let s_id = src.into_id_with(&handle);
        protect(|| {
            unsafe { rb_alias(self.as_rb_value(), d_id.as_rb_id(), s_id.as_rb_id()) };
            handle.qnil()
        })?;
        Ok(())
    }
}

/// Argument for [`define_attr`](Module::define_attr).
#[derive(Clone, Copy, Debug)]
pub enum Attr {
    /// Define a reader method like `name`.
    Read,
    /// Define a writer method like `name=`.
    Write,
    /// Define both reader and writer methods like `name` and `name=`.
    ReadWrite,
}

impl Attr {
    fn is_read(self) -> bool {
        match self {
            Attr::Read | Attr::ReadWrite => true,
            Attr::Write => false,
        }
    }

    fn is_write(self) -> bool {
        match self {
            Attr::Write | Attr::ReadWrite => true,
            Attr::Read => false,
        }
    }
}

/// # Core Modules
///
/// Functions to access Ruby's built-in modules.
///
/// See also [`Ruby::define_module`] and the [`module`](self) module.
#[allow(missing_docs)]
impl Ruby {
    #[inline]
    pub fn module_comparable(&self) -> RModule {
        unsafe { RModule::from_rb_value_unchecked(rb_mComparable) }
    }

    #[inline]
    pub fn module_enumerable(&self) -> RModule {
        unsafe { RModule::from_rb_value_unchecked(rb_mEnumerable) }
    }

    #[inline]
    pub fn module_errno(&self) -> RModule {
        unsafe { RModule::from_rb_value_unchecked(rb_mErrno) }
    }

    #[inline]
    pub fn module_file_test(&self) -> RModule {
        unsafe { RModule::from_rb_value_unchecked(rb_mFileTest) }
    }

    #[inline]
    pub fn module_gc(&self) -> RModule {
        unsafe { RModule::from_rb_value_unchecked(rb_mGC) }
    }

    #[inline]
    pub fn module_kernel(&self) -> RModule {
        unsafe { RModule::from_rb_value_unchecked(rb_mKernel) }
    }

    #[inline]
    pub fn module_math(&self) -> RModule {
        unsafe { RModule::from_rb_value_unchecked(rb_mMath) }
    }

    #[inline]
    pub fn module_process(&self) -> RModule {
        unsafe { RModule::from_rb_value_unchecked(rb_mProcess) }
    }

    #[inline]
    pub fn module_wait_readable(&self) -> RModule {
        unsafe { RModule::from_rb_value_unchecked(rb_mWaitReadable) }
    }

    #[inline]
    pub fn module_wait_writable(&self) -> RModule {
        unsafe { RModule::from_rb_value_unchecked(rb_mWaitWritable) }
    }
}

/// Return Ruby's `Comparable` module.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::module_comparable`]
/// for the non-panicking version.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn comparable() -> RModule {
    get_ruby!().module_comparable()
}

/// Return Ruby's `Enumerable` module.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::module_enumerable`]
/// for the non-panicking version.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn enumerable() -> RModule {
    get_ruby!().module_enumerable()
}

/// Return Ruby's `Errno` module.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::module_errno`] for the
/// non-panicking version.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn errno() -> RModule {
    get_ruby!().module_errno()
}

/// Return Ruby's `FileTest` module.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::module_file_test`] for
/// the non-panicking version.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn file_test() -> RModule {
    get_ruby!().module_file_test()
}

/// Return Ruby's `GC` module.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::module_gc`] for the
/// non-panicking version.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn gc() -> RModule {
    get_ruby!().module_gc()
}

/// Return Ruby's `Kernel` module.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::module_kernel`] for
/// the non-panicking version.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn kernel() -> RModule {
    get_ruby!().module_kernel()
}

/// Return Ruby's `Math` module.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::module_math`] for the
/// non-panicking version.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn math() -> RModule {
    get_ruby!().module_math()
}

/// Return Ruby's `Process` module.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::module_process`] for
/// the non-panicking version.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn process() -> RModule {
    get_ruby!().module_process()
}

/// Return Ruby's `IO::WaitReadable` module.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::module_wait_readable`]
/// for the non-panicking version.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn wait_readable() -> RModule {
    get_ruby!().module_wait_readable()
}

/// Return Ruby's `IO::WaitWritable` module.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::module_wait_writable`]
/// for the non-panicking version.
#[cfg(feature = "friendly-api")]
#[inline]
pub fn wait_writable() -> RModule {
    get_ruby!().module_wait_writable()
}
