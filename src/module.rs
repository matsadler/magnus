//! Types and functions for working with Ruby modules.

use std::{ffi::CString, fmt, mem::transmute, ops::Deref};

use crate::ruby_sys::{
    rb_class_inherited_p, rb_const_get, rb_define_class_id_under, rb_define_method_id,
    rb_define_module_function, rb_define_module_id_under, rb_define_private_method,
    rb_define_protected_method, rb_mComparable, rb_mEnumerable, rb_mErrno, rb_mFileTest, rb_mGC,
    rb_mKernel, rb_mMath, rb_mProcess, rb_mWaitReadable, rb_mWaitWritable, rb_module_new,
    ruby_value_type, VALUE,
};

use crate::{
    class::RClass,
    debug_assert_value,
    error::{protect, Error},
    exception,
    method::Method,
    object::Object,
    try_convert::TryConvert,
    value::{private, Id, NonZeroValue, ReprValue, Value},
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
    /// # Examples
    ///
    /// ```
    /// use magnus::{class, RModule};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let module = RModule::new();
    /// assert!(module.is_kind_of(class::module()));
    /// ```
    pub fn new() -> Self {
        unsafe { Self::from_rb_value_unchecked(rb_module_new()) }
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
    ///    r_string!("Hello, world!")
    /// }
    ///
    /// let module = define_module("Greeting").unwrap();
    /// module.define_module_function("greet", function!(greet, 0));
    ///
    /// let res = eval::<bool>(r#"Greeting.greet == "Hello, world!""#).unwrap();
    /// assert!(res);
    ///
    /// let res = eval::<bool>(r#"
    ///     include Greeting
    ///     greet == "Hello, world!"
    /// "#).unwrap();
    /// assert!(res);
    /// ```
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

unsafe impl private::ReprValue for RModule {
    fn to_value(self) -> Value {
        *self
    }

    unsafe fn from_value_unchecked(val: Value) -> Self {
        Self(NonZeroValue::new_unchecked(val))
    }
}

impl ReprValue for RModule {}

impl TryConvert for RModule {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        Self::from_value(*val).ok_or_else(|| {
            Error::new(
                exception::type_error(),
                format!("no implicit conversion of {} into Module", unsafe {
                    val.classname()
                },),
            )
        })
    }
}

/// Functions available on both classes and modules.
pub trait Module: Object + Deref<Target = Value> + Copy {
    /// Define a class in `self`'s scope.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{class, define_module, Module};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let outer = define_module("Outer").unwrap();
    /// let inner = outer.define_class("Inner", Default::default()).unwrap();
    /// assert!(inner.is_kind_of(class::class()));
    /// ```
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
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{class, define_module, Module};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let outer = define_module("Outer").unwrap();
    /// let inner = outer.define_module("Inner").unwrap();
    /// assert!(inner.is_kind_of(class::module()));
    /// ```
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
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{class, eval, Module, RClass, Value};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// eval::<Value>("
    ///     class Example
    ///       VALUE = 42
    ///     end
    /// ").unwrap();
    ///
    /// let class = class::object().const_get::<_, RClass>("Example").unwrap();
    /// assert_eq!(class.const_get::<_, i64>("VALUE").unwrap(), 42);
    /// ```
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

    /// Returns whether or not `self` inherits from `other`.
    ///
    /// Classes including a module are considered to inherit from that module.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Module, RClass};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let a = RClass::new(Default::default()).unwrap();
    /// let b = RClass::new(a).unwrap();
    /// assert!(b.is_inherited(a));
    /// assert!(!a.is_inherited(b));
    /// ```
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
    /// class::string().define_method("escape_unicode", method!(escape_unicode, 0));
    ///
    /// let res = eval::<bool>(r#""🤖\etest".escape_unicode == "\\u{1f916}\\u{1b}\\u{74}\\u{65}\\u{73}\\u{74}""#).unwrap();
    /// assert!(res);
    /// ```
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
    /// class::string().define_private_method("percent_encode_char", function!(percent_encode, 1));
    ///
    /// eval::<Value>(r#"
    ///     class String
    ///       def percent_encode
    ///         chars.map {|c| percent_encode_char(c)}.join("")
    ///       end
    ///     end
    /// "#).unwrap();
    ///
    /// let res = eval::<bool>(r#""foo bar".percent_encode == "foo%20bar""#).unwrap();
    /// assert!(res);
    ///
    /// assert!(eval::<bool>(r#"" ".percent_encode_char(" ")"#).unwrap_err().is_kind_of(exception::no_method_error()));
    /// ```
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
    /// class::string().define_method("escape_unicode", method!(escape_unicode, 0));
    /// class::string().define_protected_method("invisible?", method!(is_invisible, 0));
    ///
    /// eval::<Value>(r#"
    ///     class String
    ///       def escape_invisible
    ///         chars.map {|c| c.invisible? ? c.escape_unicode : c}.join("")
    ///       end
    ///     end
    /// "#).unwrap();
    ///
    /// let res: bool = eval!(r#"
    ///     "🤖\tfoo bar".escape_invisible == "🤖\\u{9}foo\\u{20}bar"
    /// "#).unwrap();
    /// assert!(res);
    ///
    /// assert!(eval::<bool>(r#"" ".invisible?"#).unwrap_err().is_kind_of(exception::no_method_error()));
    /// ```
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

/// Return Ruby's `IO::WaitReadable` module.
#[inline]
pub fn wait_readable() -> RModule {
    unsafe { RModule::from_rb_value_unchecked(rb_mWaitReadable) }
}

/// Return Ruby's `IO::WaitWritable` module.
#[inline]
pub fn wait_writable() -> RModule {
    unsafe { RModule::from_rb_value_unchecked(rb_mWaitWritable) }
}
