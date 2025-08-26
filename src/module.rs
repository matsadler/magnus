//! Types and functions for working with Ruby modules.
//!
//! See also [`Ruby`](Ruby#core-modules) for more module related methods.

use std::{ffi::CString, fmt, mem::transmute, os::raw::c_int};

use rb_sys::{
    VALUE, rb_alias, rb_attr, rb_class_inherited_p, rb_const_get, rb_const_set,
    rb_define_class_id_under, rb_define_method_id, rb_define_module_function,
    rb_define_module_id_under, rb_define_private_method, rb_define_protected_method,
    rb_include_module, rb_mComparable, rb_mEnumerable, rb_mErrno, rb_mFileTest, rb_mGC, rb_mKernel,
    rb_mMath, rb_mProcess, rb_mWaitReadable, rb_mWaitWritable, rb_mod_ancestors, rb_module_new,
    rb_prepend_module, ruby_value_type,
};

use crate::{
    Ruby,
    class::{Class, RClass},
    error::{Error, protect},
    exception::ExceptionClass,
    into_value::IntoValue,
    method::Method,
    object::Object,
    r_array::RArray,
    try_convert::TryConvert,
    value::{
        IntoId, NonZeroValue, ReprValue, Value,
        private::{self, ReprValue as _},
    },
};

/// # `RModule`
///
/// Functions that can be used to create Ruby modules.
///
/// See also the [`RModule`] type.
impl Ruby {
    /// Create a new anonymous module.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby, prelude::*};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let module = ruby.module_new();
    ///     assert!(module.is_kind_of(ruby.class_module()));
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn module_new(&self) -> RModule {
        unsafe { RModule::from_rb_value_unchecked(rb_module_new()) }
    }
}

/// A Value pointer to a RModule struct, Ruby's internal representation of
/// modules.
///
/// See the [`Module`] trait for defining instance methods and nested
/// classes/modules.
/// See the [`Object`] trait for defining singleton methods (aka class methods).
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
    /// use magnus::{RModule, eval};
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
        unsafe { Self(NonZeroValue::new_unchecked(Value::new(val))) }
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
    /// # #![allow(deprecated)]
    /// use magnus::{RModule, class, prelude::*};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let module = RModule::new();
    /// assert!(module.is_kind_of(class::module()));
    /// ```
    #[cfg_attr(
        not(feature = "old-api"),
        deprecated(note = "please use `Ruby::module_new` instead")
    )]
    #[cfg_attr(docsrs, doc(cfg(feature = "old-api")))]
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
    /// use magnus::{Error, RString, Ruby, function, r_string, rb_assert};
    ///
    /// fn greet(ruby: &Ruby) -> RString {
    ///     r_string!(ruby, "Hello, world!")
    /// }
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let module = ruby.define_module("Greeting")?;
    ///     module.define_module_function("greet", function!(greet, 0))?;
    ///
    ///     rb_assert!(ruby, r#"Greeting.greet == "Hello, world!""#);
    ///
    ///     rb_assert!(
    ///         ruby,
    ///         r#"
    ///             include Greeting
    ///             greet == "Hello, world!"
    ///         "#,
    ///     );
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
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
    #[inline]
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
    /// use magnus::{Error, Ruby, prelude::*, rb_assert};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let outer = ruby.define_module("Outer")?;
    ///     outer.define_class("Inner", ruby.class_object())?;
    ///     rb_assert!(ruby, "Outer::Inner.is_a?(Class)");
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
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
    /// use magnus::{Error, Ruby, prelude::*, rb_assert};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let outer = ruby.define_module("Outer")?;
    ///     outer.define_module("Inner")?;
    ///     rb_assert!(ruby, "Outer::Inner.is_a?(Module)");
    ///     rb_assert!(ruby, "!Outer::Inner.is_a?(Class)");
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
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
    /// use magnus::{Error, Ruby, prelude::*, rb_assert};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let outer = ruby.define_module("Outer")?;
    ///     outer.define_error("InnerError", ruby.exception_standard_error())?;
    ///     rb_assert!(ruby, "Outer::InnerError.is_a?(Class)");
    ///     rb_assert!(ruby, "Outer::InnerError < Exception");
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
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
    /// use magnus::{Error, RClass, Ruby, function, prelude::*, rb_assert};
    ///
    /// fn test() -> i64 {
    ///     42
    /// }
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let module = ruby.module_new();
    ///     module.define_method("test", function!(test, 0))?;
    ///
    ///     let class = RClass::new(ruby.class_object())?;
    ///     class.include_module(module)?;
    ///
    ///     let obj = class.new_instance(())?;
    ///     rb_assert!(ruby, "obj.test == 42", obj);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
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
    /// use magnus::{Error, RClass, Ruby, function, prelude::*, rb_assert};
    ///
    /// fn test(ruby: &Ruby) -> Result<i64, Error> {
    ///     Ok(ruby.call_super::<_, i64>(())? + 2)
    /// }
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let module = ruby.module_new();
    ///     module.define_method("test", function!(test, 0))?;
    ///
    ///     let class: RClass = ruby.eval(
    ///         r#"
    ///             class Example
    ///               def test
    ///                 40
    ///               end
    ///             end
    ///             Example
    ///         "#,
    ///     )?;
    ///     class.prepend_module(module)?;
    ///
    ///     let obj = class.new_instance(())?;
    ///     rb_assert!("obj.test == 42", obj);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
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
    /// use magnus::{Error, Module, Ruby, rb_assert};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     ruby.class_array().const_set("EXAMPLE", 42)?;
    ///
    ///     rb_assert!(ruby, "Array::EXAMPLE == 42");
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
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
    /// use magnus::{Error, Module, RClass, Ruby, Value, rb_assert};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     ruby.eval::<Value>(
    ///         "
    ///           class Example
    ///             VALUE = 42
    ///           end
    ///         ",
    ///     )?;
    ///
    ///     let class = ruby.class_object().const_get::<_, RClass>("Example")?;
    ///     rb_assert!(ruby, "klass::VALUE == 42", klass = class);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
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
    /// use magnus::{Error, Module, RClass, Ruby, prelude::*};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let a = RClass::new(ruby.class_object())?;
    ///     let b = RClass::new(a)?;
    ///     assert!(b.is_inherited(a));
    ///     assert!(!a.is_inherited(b));
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
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
    /// use magnus::{Error, Module, Ruby, rb_assert};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let ary = ruby.class_string().ancestors();
    ///
    ///     rb_assert!(
    ///         ruby,
    ///         "ary == [String, Comparable, Object, Kernel, BasicObject]",
    ///         ary,
    ///     );
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    fn ancestors(self) -> RArray {
        unsafe { RArray::from_rb_value_unchecked(rb_mod_ancestors(self.as_rb_value())) }
    }

    /// Define a method in `self`'s scope.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Module, Ruby, method, rb_assert};
    ///
    /// fn escape_unicode(s: String) -> String {
    ///     s.escape_unicode().to_string()
    /// }
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     ruby.class_string()
    ///         .define_method("escape_unicode", method!(escape_unicode, 0))?;
    ///
    ///     rb_assert!(
    ///         ruby,
    ///         r#""🤖\etest".escape_unicode == "\\u{1f916}\\u{1b}\\u{74}\\u{65}\\u{73}\\u{74}""#,
    ///     );
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
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
    /// use magnus::{Error, Module, Ruby, Value, eval, function, rb_assert};
    ///
    /// fn percent_encode(c: char) -> String {
    ///     if c.is_ascii_alphanumeric() || c == '-' || c == '_' || c == '.' || c == '~' {
    ///         String::from(c)
    ///     } else {
    ///         format!("%{:X}", c as u32)
    ///     }
    /// }
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     ruby.class_string()
    ///         .define_private_method("percent_encode_char", function!(percent_encode, 1))?;
    ///
    ///     ruby.eval::<Value>(
    ///         r#"
    ///             class String
    ///               def percent_encode
    ///                 chars.map {|c| percent_encode_char(c)}.join("")
    ///               end
    ///             end
    ///         "#,
    ///     )?;
    ///
    ///     rb_assert!(ruby, r#""foo bar".percent_encode == "foo%20bar""#);
    ///
    ///     assert!(
    ///         eval::<bool>(r#"" ".percent_encode_char(" ")"#)
    ///             .unwrap_err()
    ///             .is_kind_of(ruby.exception_no_method_error())
    ///     );
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
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
    /// use magnus::{Error, Module, Ruby, Value, method, rb_assert};
    ///
    /// fn escape_unicode(s: String) -> String {
    ///     s.escape_unicode().to_string()
    /// }
    ///
    /// fn is_invisible(c: char) -> bool {
    ///     c.is_control() || c.is_whitespace()
    /// }
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     ruby.class_string()
    ///         .define_method("escape_unicode", method!(escape_unicode, 0))?;
    ///     ruby.class_string()
    ///         .define_protected_method("invisible?", method!(is_invisible, 0))?;
    ///
    ///     ruby.eval::<Value>(
    ///         r#"
    ///             class String
    ///               def escape_invisible
    ///                 chars.map {|c| c.invisible? ? c.escape_unicode : c}.join("")
    ///               end
    ///             end
    ///         "#,
    ///     )?;
    ///
    ///     rb_assert!(
    ///         ruby,
    ///         r#""🤖\tfoo bar".escape_invisible == "🤖\\u{9}foo\\u{20}bar""#,
    ///     );
    ///
    ///     assert!(
    ///         ruby.eval::<bool>(r#"" ".invisible?"#)
    ///             .unwrap_err()
    ///             .is_kind_of(ruby.exception_no_method_error())
    ///     );
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
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
    /// use magnus::{Attr, Error, Module, RClass, Ruby, Value, eval, prelude::*, rb_assert};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let class = RClass::new(ruby.class_object())?;
    ///     class.define_attr("example", Attr::ReadWrite)?;
    ///
    ///     let obj = class.new_instance(())?;
    ///     let _: Value = eval!(ruby, "obj.example = 42", obj)?;
    ///     rb_assert!(ruby, "obj.example == 42", obj);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
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
    /// use magnus::{Error, Module, RClass, Ruby, function, prelude::*, rb_assert};
    ///
    /// fn test() -> i64 {
    ///     42
    /// }
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let class = RClass::new(ruby.class_object())?;
    ///     class.define_method("test", function!(test, 0))?;
    ///     class.define_alias("example", "test")?;
    ///
    ///     let obj = class.new_instance(())?;
    ///     rb_assert!(ruby, "obj.example == 42", obj);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
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
impl Ruby {
    /// Return Ruby's `Comparable` module.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby, rb_assert};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "md == Comparable", md = ruby.module_comparable());
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn module_comparable(&self) -> RModule {
        unsafe { RModule::from_rb_value_unchecked(rb_mComparable) }
    }

    /// Return Ruby's `Enumerable` module.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby, rb_assert};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "md == Enumerable", md = ruby.module_enumerable());
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn module_enumerable(&self) -> RModule {
        unsafe { RModule::from_rb_value_unchecked(rb_mEnumerable) }
    }

    /// Return Ruby's `Errno` module.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby, rb_assert};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "md == Errno", md = ruby.module_errno());
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn module_errno(&self) -> RModule {
        unsafe { RModule::from_rb_value_unchecked(rb_mErrno) }
    }

    /// Return Ruby's `FileTest` module.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby, rb_assert};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "md == FileTest", md = ruby.module_file_test());
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn module_file_test(&self) -> RModule {
        unsafe { RModule::from_rb_value_unchecked(rb_mFileTest) }
    }

    /// Return Ruby's `GC` module.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby, rb_assert};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "md == GC", md = ruby.module_gc());
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn module_gc(&self) -> RModule {
        unsafe { RModule::from_rb_value_unchecked(rb_mGC) }
    }

    /// Return Ruby's `Kernel` module.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby, rb_assert};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "md == Kernel", md = ruby.module_kernel());
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn module_kernel(&self) -> RModule {
        unsafe { RModule::from_rb_value_unchecked(rb_mKernel) }
    }

    /// Return Ruby's `Math` module.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby, rb_assert};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "md == Math", md = ruby.module_math());
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn module_math(&self) -> RModule {
        unsafe { RModule::from_rb_value_unchecked(rb_mMath) }
    }

    /// Return Ruby's `Process` module.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby, rb_assert};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "md == Process", md = ruby.module_process());
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn module_process(&self) -> RModule {
        unsafe { RModule::from_rb_value_unchecked(rb_mProcess) }
    }

    /// Return Ruby's `IO::WaitReadable` module.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby, rb_assert};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "md == IO::WaitReadable",
    ///         md = ruby.module_wait_readable()
    ///     );
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn module_wait_readable(&self) -> RModule {
        unsafe { RModule::from_rb_value_unchecked(rb_mWaitReadable) }
    }

    /// Return Ruby's `IO::WaitWritable` module.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby, rb_assert};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "md == IO::WaitWritable",
    ///         md = ruby.module_wait_writable()
    ///     );
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
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
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::module_comparable` instead")
)]
#[cfg_attr(docsrs, doc(cfg(feature = "old-api")))]
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
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::module_enumerable` instead")
)]
#[cfg_attr(docsrs, doc(cfg(feature = "old-api")))]
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
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::module_errno` instead")
)]
#[cfg_attr(docsrs, doc(cfg(feature = "old-api")))]
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
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::module_file_test` instead")
)]
#[cfg_attr(docsrs, doc(cfg(feature = "old-api")))]
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
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::module_gc` instead")
)]
#[cfg_attr(docsrs, doc(cfg(feature = "old-api")))]
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
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::module_kernel` instead")
)]
#[cfg_attr(docsrs, doc(cfg(feature = "old-api")))]
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
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::module_math` instead")
)]
#[cfg_attr(docsrs, doc(cfg(feature = "old-api")))]
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
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::module_process` instead")
)]
#[cfg_attr(docsrs, doc(cfg(feature = "old-api")))]
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
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::module_wait_readable` instead")
)]
#[cfg_attr(docsrs, doc(cfg(feature = "old-api")))]
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
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::module_wait_writable` instead")
)]
#[cfg_attr(docsrs, doc(cfg(feature = "old-api")))]
#[inline]
pub fn wait_writable() -> RModule {
    get_ruby!().module_wait_writable()
}
