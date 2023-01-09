//! Types and functions for working with Ruby classes.

use std::{borrow::Cow, ffi::CStr, fmt, ops::Deref, os::raw::c_int};

#[cfg(ruby_gte_3_1)]
use rb_sys::rb_cRefinement;
use rb_sys::{
    self, rb_cArray, rb_cBasicObject, rb_cBinding, rb_cClass, rb_cComplex, rb_cDir, rb_cEncoding,
    rb_cEnumerator, rb_cFalseClass, rb_cFile, rb_cFloat, rb_cHash, rb_cIO, rb_cInteger, rb_cMatch,
    rb_cMethod, rb_cModule, rb_cNameErrorMesg, rb_cNilClass, rb_cNumeric, rb_cObject, rb_cProc,
    rb_cRandom, rb_cRange, rb_cRational, rb_cRegexp, rb_cStat, rb_cString, rb_cStruct, rb_cSymbol,
    rb_cThread, rb_cTime, rb_cTrueClass, rb_cUnboundMethod, rb_class2name, rb_class_new,
    rb_class_new_instance, rb_class_superclass, rb_undef_alloc_func, ruby_value_type, VALUE,
};

use crate::{
    debug_assert_value,
    error::{protect, Error},
    exception,
    module::Module,
    object::Object,
    ruby_handle::RubyHandle,
    try_convert::{ArgList, TryConvert},
    value::{private, NonZeroValue, ReprValue, Value},
};

/// A Value pointer to a RClass struct, Ruby's internal representation of
/// classes.
///
/// See the [`Module`] trait for defining instance methods and nested
/// classes/modules.
/// See the [`Object`] trait for defining singlton methods (aka class methods).
///
/// All [`Value`] methods should be available on this type through [`Deref`],
/// but some may be missed by this documentation.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RClass(NonZeroValue);

impl RClass {
    /// Return `Some(RClass)` if `val` is a `RClass`, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RClass};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(RClass::from_value(eval("String").unwrap()).is_some());
    /// assert!(RClass::from_value(eval("Enumerable").unwrap()).is_none());
    /// assert!(RClass::from_value(eval("nil").unwrap()).is_none());
    /// ```
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            (val.rb_type() == ruby_value_type::RUBY_T_CLASS)
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        Self(NonZeroValue::new_unchecked(Value::new(val)))
    }

    /// Create a new anonymous class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{class, RClass};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let class = RClass::new(Default::default()).unwrap();
    /// assert!(class.is_kind_of(class::class()));
    /// ```
    pub fn new(superclass: RClass) -> Result<RClass, Error> {
        Class::new(superclass)
    }

    /// Create a new object, an instance of `self`, passing the arguments
    /// `args` to the initialiser.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::class;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let s = class::string().new_instance(()).unwrap();
    /// assert!(s.is_kind_of(class::string()));
    /// assert_eq!(s.to_string(), "");
    /// ```
    pub fn new_instance<T>(self, args: T) -> Result<Value, Error>
    where
        T: ArgList,
    {
        Class::new_instance(self, args)
    }

    /// Returns the parent class of `self`.
    ///
    /// Returns `Err` if `self` can not have a parent class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{class, eval};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let klass = class::hash().superclass().unwrap();
    /// assert!(klass.equal(class::object()).unwrap());
    /// ```
    pub fn superclass(self) -> Result<Self, Error> {
        Class::superclass(self)
    }

    /// Return the name of `self`.
    ///
    /// # Safety
    ///
    /// Ruby may modify or free the memory backing the returned str, the caller
    /// must ensure this does not happen.
    ///
    /// This can be used safely by immediately calling
    /// [`into_owned`](Cow::into_owned) on the return value.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{class, eval};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let value = class::hash();
    /// // safe as we neve give Ruby a chance to free the string.
    /// let s = unsafe { value.name() }.into_owned();
    /// assert_eq!(s, "Hash");
    /// ```
    pub unsafe fn name(&self) -> Cow<str> {
        Class::name(self)
    }
}

impl Default for RClass {
    fn default() -> Self {
        unsafe { RClass::from_rb_value_unchecked(rb_sys::rb_cObject) }
    }
}

impl Deref for RClass {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
    }
}

impl fmt::Display for RClass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for RClass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl From<RClass> for Value {
    fn from(val: RClass) -> Self {
        *val
    }
}

impl Object for RClass {}
impl Module for RClass {}

unsafe impl private::ReprValue for RClass {
    fn to_value(self) -> Value {
        *self
    }

    unsafe fn from_value_unchecked(val: Value) -> Self {
        Self(NonZeroValue::new_unchecked(val))
    }
}

impl ReprValue for RClass {}

impl TryConvert for RClass {
    fn try_convert(val: Value) -> Result<Self, Error> {
        match Self::from_value(val) {
            Some(v) => Ok(v),
            None => Err(Error::new(
                exception::type_error(),
                format!("no implicit conversion of {} into Class", unsafe {
                    val.classname()
                },),
            )),
        }
    }
}

/// Functions available on all types representing a Ruby class.
pub trait Class: Module {
    /// The type representing an instance of the class `Self`.
    type Instance;

    /// Create a new anonymous class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{exception, prelude::*, ExceptionClass};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(ExceptionClass::new(exception::standard_error()).is_ok());
    /// ```
    fn new(superclass: Self) -> Result<Self, Error>;

    /// Create a new object, an instance of `self`, passing the arguments
    /// `args` to the initialiser.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{exception, prelude::*};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let s = exception::standard_error().new_instance(("bang!",)).unwrap();
    /// assert!(s.is_kind_of(exception::standard_error()));
    /// ```
    fn new_instance<T>(self, args: T) -> Result<Self::Instance, Error>
    where
        T: ArgList;

    /// Returns the parent class of `self`.
    ///
    /// Returns `Err` if `self` can not have a parent class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{class, exception, prelude::*};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let klass = exception::exception().superclass().unwrap();
    /// assert!(klass.equal(class::object()).unwrap());
    /// ```
    fn superclass(self) -> Result<RClass, Error> {
        protect(|| unsafe {
            RClass::from_rb_value_unchecked(rb_class_superclass(self.as_rb_value()))
        })
    }

    /// Return the name of `self`.
    ///
    /// # Safety
    ///
    /// Ruby may modify or free the memory backing the returned str, the caller
    /// must ensure this does not happen.
    ///
    /// This can be used safely by immediately calling
    /// [`into_owned`](Cow::into_owned) on the return value.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{exception, prelude::*};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let value = exception::standard_error();
    /// // safe as we neve give Ruby a chance to free the string.
    /// let s = unsafe { value.name() }.into_owned();
    /// assert_eq!(s, "StandardError");
    /// ```
    unsafe fn name(&self) -> Cow<str> {
        let ptr = rb_class2name(self.as_rb_value());
        let cstr = CStr::from_ptr(ptr);
        cstr.to_string_lossy()
    }

    /// Return `self` as an [`RClass`].
    fn as_r_class(self) -> RClass {
        RClass::from_value(*self).unwrap()
    }

    /// Remove the allocator function of a class.
    ///
    /// Useful for RTypedData, where instances should not be allocated by
    /// the default allocate function. `#[derive(TypedData)]` and `#[wrap]`
    /// take care of undefining the allocator function, you do not need
    /// to use `undef_alloc_func` if you're using one of those.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{class, eval, Class};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    /// let class = magnus::define_class("Point", Default::default()).unwrap();
    ///
    /// class.undef_alloc_func();
    ///
    /// let instance = class.new_instance(());
    /// assert_eq!("allocator undefined for Point", instance.err().unwrap().to_string());
    /// ```
    fn undef_alloc_func(self) {
        unsafe { rb_undef_alloc_func(self.as_rb_value()) }
    }
}

impl Class for RClass {
    type Instance = Value;

    fn new(superclass: Self) -> Result<Self, Error> {
        debug_assert_value!(superclass);
        let superclass = superclass.as_rb_value();
        protect(|| unsafe { Self::from_rb_value_unchecked(rb_class_new(superclass)) })
    }

    fn new_instance<T>(self, args: T) -> Result<Self::Instance, Error>
    where
        T: ArgList,
    {
        let args = args.into_arg_list();
        let slice = args.as_ref();
        unsafe {
            protect(|| {
                Value::new(rb_class_new_instance(
                    slice.len() as c_int,
                    slice.as_ptr() as *const VALUE,
                    self.as_rb_value(),
                ))
            })
        }
    }

    fn as_r_class(self) -> RClass {
        self
    }
}

impl RubyHandle {
    #[inline]
    pub fn class_array(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cArray) }
    }

    #[inline]
    pub fn class_basic_object(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cBasicObject) }
    }

    #[inline]
    pub fn class_binding(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cBinding) }
    }

    #[inline]
    pub fn class_class(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cClass) }
    }

    #[inline]
    pub fn class_complex(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cComplex) }
    }

    #[inline]
    pub fn class_dir(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cDir) }
    }

    #[inline]
    pub fn class_encoding(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cEncoding) }
    }

    #[inline]
    pub fn class_enumerator(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cEnumerator) }
    }

    #[inline]
    pub fn class_false_class(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cFalseClass) }
    }

    #[inline]
    pub fn class_file(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cFile) }
    }

    #[inline]
    pub fn class_float(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cFloat) }
    }

    #[inline]
    pub fn class_hash(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cHash) }
    }

    #[inline]
    pub fn class_io(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cIO) }
    }

    #[inline]
    pub fn class_integer(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cInteger) }
    }

    #[inline]
    pub fn class_match_class(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cMatch) }
    }

    #[inline]
    pub fn class_method(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cMethod) }
    }

    #[inline]
    pub fn class_module(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cModule) }
    }

    #[inline]
    pub fn class_name_error_mesg(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cNameErrorMesg) }
    }

    #[inline]
    pub fn class_nil_class(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cNilClass) }
    }

    #[inline]
    pub fn class_numeric(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cNumeric) }
    }

    #[inline]
    pub fn class_object(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cObject) }
    }

    #[inline]
    pub fn class_proc(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cProc) }
    }

    #[inline]
    pub fn class_random(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cRandom) }
    }

    #[inline]
    pub fn class_range(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cRange) }
    }

    #[inline]
    pub fn class_rational(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cRational) }
    }

    #[cfg(any(ruby_gte_3_1, docsrs))]
    #[cfg_attr(docsrs, doc(cfg(ruby_gte_3_1)))]
    #[inline]
    pub fn class_refinement(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cRefinement) }
    }

    #[inline]
    pub fn class_regexp(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cRegexp) }
    }

    #[inline]
    pub fn class_stat(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cStat) }
    }

    #[inline]
    pub fn class_string(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cString) }
    }

    #[inline]
    pub fn class_struct_class(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cStruct) }
    }

    #[inline]
    pub fn class_symbol(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cSymbol) }
    }

    #[inline]
    pub fn class_thread(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cThread) }
    }

    #[inline]
    pub fn class_time(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cTime) }
    }

    #[inline]
    pub fn class_true_class(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cTrueClass) }
    }

    #[inline]
    pub fn class_unbound_method(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cUnboundMethod) }
    }
}

/// Return Ruby's `Array` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn array() -> RClass {
    get_ruby!().class_array()
}

/// Return Ruby's `BasicObject` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn basic_object() -> RClass {
    get_ruby!().class_basic_object()
}

/// Return Ruby's `Binding` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn binding() -> RClass {
    get_ruby!().class_binding()
}

/// Return Ruby's `Class` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn class() -> RClass {
    get_ruby!().class_class()
}

/// Return Ruby's `Complex` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn complex() -> RClass {
    get_ruby!().class_complex()
}

/// Return Ruby's `Dir` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn dir() -> RClass {
    get_ruby!().class_dir()
}

/// Return Ruby's `Encoding` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn encoding() -> RClass {
    get_ruby!().class_encoding()
}

/// Return Ruby's `Enumerator` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn enumerator() -> RClass {
    get_ruby!().class_enumerator()
}

/// Return Ruby's `FalseClass` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn false_class() -> RClass {
    get_ruby!().class_false_class()
}

/// Return Ruby's `File` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn file() -> RClass {
    get_ruby!().class_file()
}

/// Return Ruby's `Float` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn float() -> RClass {
    get_ruby!().class_float()
}

/// Return Ruby's `Hash` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn hash() -> RClass {
    get_ruby!().class_hash()
}

/// Return Ruby's `IO` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn io() -> RClass {
    get_ruby!().class_io()
}

/// Return Ruby's `Integer` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn integer() -> RClass {
    get_ruby!().class_integer()
}

/// Return Ruby's `MatchData` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn match_class() -> RClass {
    get_ruby!().class_match_class()
}

/// Return Ruby's `Method` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn method() -> RClass {
    get_ruby!().class_method()
}

/// Return Ruby's `Module` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn module() -> RClass {
    get_ruby!().class_module()
}

/// Return Ruby's `NameError::Message` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn name_error_mesg() -> RClass {
    get_ruby!().class_name_error_mesg()
}

/// Return Ruby's `NilClass` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn nil_class() -> RClass {
    get_ruby!().class_nil_class()
}

/// Return Ruby's `Numeric` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn numeric() -> RClass {
    get_ruby!().class_numeric()
}

/// Return Ruby's `Object` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn object() -> RClass {
    get_ruby!().class_object()
}

/// Return Ruby's `Proc` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn proc() -> RClass {
    get_ruby!().class_proc()
}

/// Return Ruby's `Random` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn random() -> RClass {
    get_ruby!().class_random()
}

/// Return Ruby's `Range` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn range() -> RClass {
    get_ruby!().class_range()
}

/// Return Ruby's `Rational` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn rational() -> RClass {
    get_ruby!().class_rational()
}

/// Return Ruby's `Refinement` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[cfg(any(ruby_gte_3_1, docsrs))]
#[cfg_attr(docsrs, doc(cfg(ruby_gte_3_1)))]
#[inline]
pub fn refinement() -> RClass {
    get_ruby!().class_refinement()
}

/// Return Ruby's `Regexp` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn regexp() -> RClass {
    get_ruby!().class_regexp()
}

/// Return Ruby's `File::Stat` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn stat() -> RClass {
    get_ruby!().class_stat()
}

/// Return Ruby's `String` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn string() -> RClass {
    get_ruby!().class_string()
}

/// Return Ruby's `Struct` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn struct_class() -> RClass {
    get_ruby!().class_struct_class()
}

/// Return Ruby's `Symbol` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn symbol() -> RClass {
    get_ruby!().class_symbol()
}

/// Return Ruby's `Thread` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn thread() -> RClass {
    get_ruby!().class_thread()
}

/// Return Ruby's `Time` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn time() -> RClass {
    get_ruby!().class_time()
}

/// Return Ruby's `TrueClass` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn true_class() -> RClass {
    get_ruby!().class_true_class()
}

/// Return Ruby's `UnboundMethod` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn unbound_method() -> RClass {
    get_ruby!().class_unbound_method()
}
