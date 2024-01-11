//! Types and functions for working with Ruby classes.
//!
//! See also [`Ruby`](Ruby#core-classes) for more class related methods.

use std::{borrow::Cow, ffi::CStr, fmt, mem::transmute, os::raw::c_int};

#[cfg(ruby_gte_3_1)]
use rb_sys::rb_cRefinement;
use rb_sys::{
    self, rb_alloc_func_t, rb_cArray, rb_cBasicObject, rb_cBinding, rb_cClass, rb_cComplex,
    rb_cDir, rb_cEncoding, rb_cEnumerator, rb_cFalseClass, rb_cFile, rb_cFloat, rb_cHash, rb_cIO,
    rb_cInteger, rb_cMatch, rb_cMethod, rb_cModule, rb_cNameErrorMesg, rb_cNilClass, rb_cNumeric,
    rb_cObject, rb_cProc, rb_cRandom, rb_cRange, rb_cRational, rb_cRegexp, rb_cStat, rb_cString,
    rb_cStruct, rb_cSymbol, rb_cThread, rb_cTime, rb_cTrueClass, rb_cUnboundMethod, rb_class2name,
    rb_class_new, rb_class_new_instance_kw, rb_class_superclass, rb_define_alloc_func,
    rb_get_alloc_func, rb_obj_alloc, rb_undef_alloc_func, ruby_value_type, VALUE,
};

use crate::{
    error::{protect, Error},
    into_value::{kw_splat, ArgList, IntoValue},
    module::Module,
    object::Object,
    try_convert::TryConvert,
    typed_data::TypedData,
    value::{
        private::{self, ReprValue as _},
        NonZeroValue, ReprValue, Value,
    },
    Ruby,
};

/// A Value pointer to a RClass struct, Ruby's internal representation of
/// classes.
///
/// See the [`Class`] trait for methods available on classes.
/// See the [`Module`] trait for defining instance methods and nested
/// classes/modules.
/// See the [`Object`] trait for defining singlton methods (aka class methods).
///
/// See the [`ReprValue`] trait for additional methods available on this type.
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

impl IntoValue for RClass {
    #[inline]
    fn into_value_with(self, _: &Ruby) -> Value {
        self.0.get()
    }
}

impl Object for RClass {}
impl Module for RClass {}

unsafe impl private::ReprValue for RClass {}

impl ReprValue for RClass {}

impl TryConvert for RClass {
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

/// Functions available on all types representing a Ruby class.
pub trait Class: Module {
    /// The type representing an instance of the class `Self`.
    type Instance;

    /// Create a new anonymous class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{prelude::*, Error, RClass, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let class = RClass::new(ruby.class_object())?;
    ///     assert!(class.is_kind_of(ruby.class_class()));
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    ///
    /// ```
    /// use magnus::{prelude::*, Error, ExceptionClass, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     assert!(ExceptionClass::new(ruby.exception_standard_error()).is_ok());
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    fn new(superclass: Self) -> Result<Self, Error>;

    /// Create a new object, an instance of `self`, passing the arguments
    /// `args` to the initialiser.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{prelude::*, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let s = ruby.class_string().new_instance(())?;
    ///     assert!(s.is_kind_of(ruby.class_string()));
    ///     assert_eq!(s.to_string(), "");
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    ///
    /// ```
    /// use magnus::{eval, kwargs, prelude::*, Error, RClass, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let cls: RClass = eval!(
    ///         ruby,
    ///         r#"
    ///             class Foo
    ///               def initialize(bar, baz:)
    ///                 @bar = bar
    ///                 @baz = baz
    ///               end
    ///
    ///               attr_reader(:bar, :baz)
    ///             end
    ///
    ///             Object.const_get(:Foo)
    ///         "#
    ///     )?;
    ///     let instance = cls.new_instance((1, kwargs!("baz" => 2)))?;
    ///     assert!(instance.is_kind_of(cls));
    ///     let bar: i32 = instance.funcall("bar", ())?;
    ///     assert_eq!(bar, 1);
    ///     let baz: i32 = instance.funcall("baz", ())?;
    ///     assert_eq!(baz, 2);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    ///
    /// ```
    /// use magnus::{prelude::*, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let s = ruby.exception_standard_error().new_instance(("bang!",))?;
    ///     assert!(s.is_kind_of(ruby.exception_standard_error()));
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    ///
    /// ```
    /// use magnus::{eval, ExceptionClass, kwargs, prelude::*, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let exc: ExceptionClass = eval!(
    ///         ruby,
    ///         r#"
    ///             class MyError < StandardError
    ///               def initialize(message:)
    ///                 super(message)
    ///               end
    ///             end
    ///
    ///             Object.const_get(:MyError)
    ///         "#
    ///     )?;
    ///     let s = exc.new_instance((kwargs!("message" => "bang!"),))?;
    ///     assert!(s.is_kind_of(exc));
    ///     let message: String = s.funcall("message", ())?;
    ///     assert_eq!(message, "bang!");
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    fn new_instance<T>(self, args: T) -> Result<Self::Instance, Error>
    where
        T: ArgList;

    /// Create a new object, an instance of `self`, without calling the class's
    /// `initialize` method.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{prelude::*, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let s = ruby.class_string().obj_alloc()?;
    ///     assert!(s.is_kind_of(ruby.class_string()));
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    ///
    /// ```
    /// use magnus::{prelude::*, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let s = ruby.exception_standard_error().obj_alloc()?;
    ///     assert!(s.is_kind_of(ruby.exception_standard_error()));
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    fn obj_alloc(self) -> Result<Self::Instance, Error>;

    /// Returns the parent class of `self`.
    ///
    /// Returns `Err` if `self` can not have a parent class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{prelude::*, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let klass = ruby.class_hash().superclass()?;
    ///     assert!(klass.equal(ruby.class_object())?);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    ///
    /// ```
    /// use magnus::{prelude::*, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let klass = ruby.exception_exception().superclass()?;
    ///     assert!(klass.equal(ruby.class_object())?);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
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
    /// use magnus::{prelude::*, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let value = ruby.class_hash();
    ///     // safe as we neve give Ruby a chance to free the string.
    ///     let s = unsafe { value.name() }.into_owned();
    ///     assert_eq!(s, "Hash");
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    ///
    /// ```
    /// use magnus::{prelude::*, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let value = ruby.exception_standard_error();
    ///     // safe as we neve give Ruby a chance to free the string.
    ///     let s = unsafe { value.name() }.into_owned();
    ///     assert_eq!(s, "StandardError");
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    unsafe fn name(&self) -> Cow<str> {
        let ptr = rb_class2name(self.as_rb_value());
        let cstr = CStr::from_ptr(ptr);
        cstr.to_string_lossy()
    }

    /// Return `self` as an [`RClass`].
    fn as_r_class(self) -> RClass {
        RClass::from_value(self.as_value()).unwrap()
    }

    /// Define an allocator function for `self` using `T`'s [`Default`]
    /// implementation.
    ///
    /// In Ruby creating a new object has two steps, first the object is
    /// allocated, and then it is initialised. Allocating the object is handled
    /// by the `new` class method, which then also calls `initialize` on the
    /// newly allocated object.
    ///
    /// This does not map well to Rust, where data is allocated and initialised
    /// in a single step. For this reason most examples in this documentation
    /// show defining the `new` class method directly, opting out of the two
    /// step allocate and then initialise process. However, this means the
    /// class can't be subclassed in Ruby.
    ///
    /// Defining an allocator function allows a class be subclassed with the
    /// normal Ruby behaviour of calling the `initialize` method.
    ///
    /// Be aware when creating an instance of once of a class with an allocator
    /// function from Rust it must be done with [`Class::new_instance`] to call
    /// the allocator and then the `initialize` method.
    ///
    /// # Panics
    ///
    /// Panics if `self` and `<T as TypedData>::class()` are not the same class.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::cell::RefCell;
    ///
    /// use magnus::{function, method, prelude::*, wrap, Error, RClass, Ruby, Value};
    ///
    /// #[derive(Default)]
    /// struct Point {
    ///     x: isize,
    ///     y: isize,
    /// }
    ///
    /// #[derive(Default)]
    /// #[wrap(class = "Point")]
    /// struct MutPoint(RefCell<Point>);
    ///
    /// impl MutPoint {
    ///     fn initialize(&self, x: isize, y: isize) {
    ///         let mut this = self.0.borrow_mut();
    ///         this.x = x;
    ///         this.y = y;
    ///     }
    ///
    ///     // bypasses initialize
    ///     fn create(x: isize, y: isize) -> MutPoint {
    ///         MutPoint(RefCell::new(Point { x, y }))
    ///     }
    ///
    ///     // calls initialize
    ///     fn call_new(class: RClass, x: isize, y: isize) -> Result<Value, Error> {
    ///         class.new_instance((x, y))
    ///     }
    ///
    ///     fn distance(&self, other: &MutPoint) -> f64 {
    ///         let a = self.0.borrow();
    ///         let b = other.0.borrow();
    ///         (((b.x - a.x).pow(2) + (b.y - a.y).pow(2)) as f64).sqrt()
    ///     }
    /// }
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let class = ruby.define_class("Point", ruby.class_object())?;
    ///     class.define_alloc_func::<MutPoint>();
    ///     class.define_singleton_method("create", function!(MutPoint::create, 2))?;
    ///     class.define_singleton_method("call_new", method!(MutPoint::call_new, 2))?;
    ///     class.define_method("initialize", method!(MutPoint::initialize, 2))?;
    ///     class.define_method("distance", method!(MutPoint::distance, 1))?;
    ///
    ///     let d: f64 = ruby.eval(
    ///         "
    ///           class OffsetPoint < Point
    ///             def initialize(offset, x, y)
    ///               super(x + offset, y + offset)
    ///             end
    ///           end
    ///           a = Point.new(1, 1)
    ///           b = OffsetPoint.new(2, 3, 3)
    ///           a.distance(b).round(2)
    ///         ",
    ///     )?;
    ///
    ///     assert_eq!(d, 5.66);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    fn define_alloc_func<T>(self)
    where
        T: Default + TypedData,
    {
        extern "C" fn allocate<T: Default + TypedData>(class: RClass) -> Value {
            Ruby::get_with(class)
                .obj_wrap_as(T::default(), class)
                .as_value()
        }

        let class = T::class(&Ruby::get_with(self));
        assert!(
            class.equal(self).unwrap_or(false),
            "{} does not match {}",
            self.as_value(),
            class
        );
        unsafe {
            rb_define_alloc_func(
                self.as_rb_value(),
                Some(transmute(allocate::<T> as extern "C" fn(RClass) -> Value)),
            )
        }
    }

    /// Remove the allocator function of a class if it is Ruby's default
    /// allocator function.
    ///
    /// Useful for RTypedData, where instances should not be allocated by
    /// the default allocate function. `#[derive(TypedData)]` and `#[wrap]`
    /// take care of undefining the allocator function, you do not need
    /// to use `undef_default_alloc_func` if you're using one of those.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Class, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let class = ruby.define_class("Point", ruby.class_object())?;
    ///
    ///     class.undef_default_alloc_func();
    ///
    ///     let instance = class.new_instance(());
    ///     assert_eq!(
    ///         "allocator undefined for Point",
    ///         instance.err().unwrap().to_string()
    ///     );
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    fn undef_default_alloc_func(self) {
        static INIT: std::sync::Once = std::sync::Once::new();
        static mut RB_CLASS_ALLOCATE_INSTANCE: rb_alloc_func_t = None;
        let rb_class_allocate_instance = unsafe {
            INIT.call_once(|| {
                RB_CLASS_ALLOCATE_INSTANCE =
                    rb_get_alloc_func(Ruby::get_unchecked().class_object().as_rb_value());
            });
            RB_CLASS_ALLOCATE_INSTANCE
        };

        unsafe {
            if rb_get_alloc_func(self.as_rb_value()) == rb_class_allocate_instance {
                rb_undef_alloc_func(self.as_rb_value())
            }
        }
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
        let kw_splat = kw_splat(&args);
        let args = args.into_arg_list_with(&Ruby::get_with(self));
        let slice = args.as_ref();
        unsafe {
            protect(|| {
                Value::new(rb_class_new_instance_kw(
                    slice.len() as c_int,
                    slice.as_ptr() as *const VALUE,
                    self.as_rb_value(),
                    kw_splat as c_int,
                ))
            })
        }
    }

    fn obj_alloc(self) -> Result<Self::Instance, Error> {
        unsafe { protect(|| Value::new(rb_obj_alloc(self.as_rb_value()))) }
    }

    fn as_r_class(self) -> RClass {
        self
    }
}

/// # Core Classes
///
/// Functions to access Ruby's built-in classes.
///
/// See also the [`class`](self) module.
impl Ruby {
    /// Return Ruby's `Array` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "klass == Array", klass = ruby.class_array());
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn class_array(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cArray) }
    }

    /// Return Ruby's `BasicObject` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "klass == BasicObject",
    ///         klass = ruby.class_basic_object()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn class_basic_object(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cBasicObject) }
    }

    /// Return Ruby's `Binding` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "klass == Binding", klass = ruby.class_binding());
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn class_binding(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cBinding) }
    }

    /// Return Ruby's `Class` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "klass == Class", klass = ruby.class_class());
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn class_class(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cClass) }
    }

    /// Return Ruby's `Complex` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "klass == Complex", klass = ruby.class_complex());
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn class_complex(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cComplex) }
    }

    /// Return Ruby's `Dir` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "klass == Dir", klass = ruby.class_dir());
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn class_dir(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cDir) }
    }

    /// Return Ruby's `Encoding` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "klass == Encoding", klass = ruby.class_encoding());
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn class_encoding(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cEncoding) }
    }

    /// Return Ruby's `Enumerator` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "klass == Enumerator", klass = ruby.class_enumerator());
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn class_enumerator(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cEnumerator) }
    }

    /// Return Ruby's `FalseClass` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "klass == FalseClass",
    ///         klass = ruby.class_false_class()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn class_false_class(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cFalseClass) }
    }

    /// Return Ruby's `File` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "klass == File", klass = ruby.class_file());
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn class_file(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cFile) }
    }

    /// Return Ruby's `Float` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "klass == Float", klass = ruby.class_float());
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn class_float(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cFloat) }
    }

    /// Return Ruby's `Hash` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "klass == Hash", klass = ruby.class_hash());
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn class_hash(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cHash) }
    }

    /// Return Ruby's `IO` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "klass == IO", klass = ruby.class_io());
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn class_io(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cIO) }
    }

    /// Return Ruby's `Integer` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "klass == Integer", klass = ruby.class_integer());
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn class_integer(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cInteger) }
    }

    /// Return Ruby's `MatchData` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "klass == MatchData", klass = ruby.class_match());
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn class_match(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cMatch) }
    }

    /// Return Ruby's `Method` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "klass == Method", klass = ruby.class_method());
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn class_method(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cMethod) }
    }

    /// Return Ruby's `Module` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "klass == Module", klass = ruby.class_module());
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn class_module(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cModule) }
    }

    /// Return Ruby's `NameError::message` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         r#"klass.name == "NameError::message""#,
    ///         klass = ruby.class_name_error_mesg()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn class_name_error_mesg(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cNameErrorMesg) }
    }

    /// Return Ruby's `NilClass` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "klass == NilClass", klass = ruby.class_nil_class());
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn class_nil_class(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cNilClass) }
    }

    /// Return Ruby's `Numeric` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "klass == Numeric", klass = ruby.class_numeric());
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn class_numeric(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cNumeric) }
    }

    /// Return Ruby's `Object` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "klass == Object", klass = ruby.class_object());
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn class_object(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cObject) }
    }

    /// Return Ruby's `Proc` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "klass == Proc", klass = ruby.class_proc());
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn class_proc(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cProc) }
    }

    /// Return Ruby's `Random` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "klass == Random", klass = ruby.class_random());
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn class_random(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cRandom) }
    }

    /// Return Ruby's `Range` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "klass == Range", klass = ruby.class_range());
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn class_range(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cRange) }
    }

    /// Return Ruby's `Rational` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "klass == Rational", klass = ruby.class_rational());
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn class_rational(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cRational) }
    }

    /// Return Ruby's `Refinement` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "klass == Refinement", klass = ruby.class_refinement());
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[cfg(any(ruby_gte_3_1, docsrs))]
    #[cfg_attr(docsrs, doc(cfg(ruby_gte_3_1)))]
    #[inline]
    pub fn class_refinement(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cRefinement) }
    }

    /// Return Ruby's `Regexp` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "klass == Regexp", klass = ruby.class_regexp());
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn class_regexp(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cRegexp) }
    }

    /// Return Ruby's `File::Stat` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "klass == File::Stat", klass = ruby.class_stat());
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn class_stat(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cStat) }
    }

    /// Return Ruby's `String` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "klass == String", klass = ruby.class_string());
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn class_string(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cString) }
    }

    /// Return Ruby's `Struct` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "klass == Struct", klass = ruby.class_struct());
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn class_struct(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cStruct) }
    }

    /// Return Ruby's `Symbol` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "klass == Symbol", klass = ruby.class_symbol());
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn class_symbol(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cSymbol) }
    }

    /// Return Ruby's `Thread` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "klass == Thread", klass = ruby.class_thread());
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn class_thread(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cThread) }
    }

    /// Return Ruby's `Time` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "klass == Time", klass = ruby.class_time());
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn class_time(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cTime) }
    }

    /// Return Ruby's `TrueClass` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(ruby, "klass == TrueClass", klass = ruby.class_true_class());
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn class_true_class(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cTrueClass) }
    }

    /// Return Ruby's `UnboundMethod` class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     rb_assert!(
    ///         ruby,
    ///         "klass == UnboundMethod",
    ///         klass = ruby.class_unbound_method()
    ///     );
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn class_unbound_method(&self) -> RClass {
        unsafe { RClass::from_rb_value_unchecked(rb_cUnboundMethod) }
    }
}

/// Return Ruby's `Array` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::class_array`] for the
/// non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::class_array` instead")
)]
#[inline]
pub fn array() -> RClass {
    get_ruby!().class_array()
}

/// Return Ruby's `BasicObject` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::class_basic_object`]
/// for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::class_basic_object` instead")
)]
#[inline]
pub fn basic_object() -> RClass {
    get_ruby!().class_basic_object()
}

/// Return Ruby's `Binding` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::class_binding`] for
/// the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::class_binding` instead")
)]
#[inline]
pub fn binding() -> RClass {
    get_ruby!().class_binding()
}

/// Return Ruby's `Class` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::class_class`] for the
/// non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::class_class` instead")
)]
#[inline]
pub fn class() -> RClass {
    get_ruby!().class_class()
}

/// Return Ruby's `Complex` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::class_complex`] for
/// the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::class_complex` instead")
)]
#[inline]
pub fn complex() -> RClass {
    get_ruby!().class_complex()
}

/// Return Ruby's `Dir` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::class_dir`] for the
/// non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::class_dir` instead")
)]
#[inline]
pub fn dir() -> RClass {
    get_ruby!().class_dir()
}

/// Return Ruby's `Encoding` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::class_encoding`] for
/// the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::class_encoding` instead")
)]
#[inline]
pub fn encoding() -> RClass {
    get_ruby!().class_encoding()
}

/// Return Ruby's `Enumerator` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::class_enumerator`]
/// for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::class_enumerator` instead")
)]
#[inline]
pub fn enumerator() -> RClass {
    get_ruby!().class_enumerator()
}

/// Return Ruby's `FalseClass` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::class_false_class`]
/// for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::class_false_class` instead")
)]
#[inline]
pub fn false_class() -> RClass {
    get_ruby!().class_false_class()
}

/// Return Ruby's `File` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::class_file`] for the
/// non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::class_file` instead")
)]
#[inline]
pub fn file() -> RClass {
    get_ruby!().class_file()
}

/// Return Ruby's `Float` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::class_float`] for the
/// non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::class_float` instead")
)]
#[inline]
pub fn float() -> RClass {
    get_ruby!().class_float()
}

/// Return Ruby's `Hash` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::class_hash`] for the
/// non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::class_hash` instead")
)]
#[inline]
pub fn hash() -> RClass {
    get_ruby!().class_hash()
}

/// Return Ruby's `IO` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::class_io`] for the
/// non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::class_io` instead")
)]
#[inline]
pub fn io() -> RClass {
    get_ruby!().class_io()
}

/// Return Ruby's `Integer` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::class_integer`] for
/// the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::class_integer` instead")
)]
#[inline]
pub fn integer() -> RClass {
    get_ruby!().class_integer()
}

/// Return Ruby's `MatchData` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::class_match`]
/// for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::class_match` instead")
)]
#[inline]
pub fn match_class() -> RClass {
    get_ruby!().class_match()
}

/// Return Ruby's `Method` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::class_method`] for the
/// non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::class_method` instead")
)]
#[inline]
pub fn method() -> RClass {
    get_ruby!().class_method()
}

/// Return Ruby's `Module` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::class_module`] for the
/// non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::class_module` instead")
)]
#[inline]
pub fn module() -> RClass {
    get_ruby!().class_module()
}

/// Return Ruby's `NameError::message` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::class_name_error_mesg`]
/// for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::class_name_error_mesg` instead")
)]
#[inline]
pub fn name_error_mesg() -> RClass {
    get_ruby!().class_name_error_mesg()
}

/// Return Ruby's `NilClass` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::class_nil_class`] for
/// the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::class_nil_class` instead")
)]
#[inline]
pub fn nil_class() -> RClass {
    get_ruby!().class_nil_class()
}

/// Return Ruby's `Numeric` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::class_numeric`] for
/// the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::class_numeric` instead")
)]
#[inline]
pub fn numeric() -> RClass {
    get_ruby!().class_numeric()
}

/// Return Ruby's `Object` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::class_object`] for the
/// non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::class_object` instead")
)]
#[inline]
pub fn object() -> RClass {
    get_ruby!().class_object()
}

/// Return Ruby's `Proc` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::class_proc`] for the
/// non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::class_proc` instead")
)]
#[inline]
pub fn proc() -> RClass {
    get_ruby!().class_proc()
}

/// Return Ruby's `Random` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::class_random`] for the
/// non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::class_random` instead")
)]
#[inline]
pub fn random() -> RClass {
    get_ruby!().class_random()
}

/// Return Ruby's `Range` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::class_range`] for the
/// non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::class_range` instead")
)]
#[inline]
pub fn range() -> RClass {
    get_ruby!().class_range()
}

/// Return Ruby's `Rational` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::class_rational`] for
/// the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::class_rational` instead")
)]
#[inline]
pub fn rational() -> RClass {
    get_ruby!().class_rational()
}

/// Return Ruby's `Refinement` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::class_refinement`] for
/// the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::class_refinement` instead")
)]
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
/// Panics if called from a non-Ruby thread. See [`Ruby::class_regexp`] for the
/// non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::class_regexp` instead")
)]
#[inline]
pub fn regexp() -> RClass {
    get_ruby!().class_regexp()
}

/// Return Ruby's `File::Stat` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::class_stat`] for the
/// non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::class_stat` instead")
)]
#[inline]
pub fn stat() -> RClass {
    get_ruby!().class_stat()
}

/// Return Ruby's `String` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::class_string`] for the
/// non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::class_string` instead")
)]
#[inline]
pub fn string() -> RClass {
    get_ruby!().class_string()
}

/// Return Ruby's `Struct` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::class_struct`]
/// for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::class_struct` instead")
)]
#[inline]
pub fn struct_class() -> RClass {
    get_ruby!().class_struct()
}

/// Return Ruby's `Symbol` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::class_symbol`] for the
/// non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::class_symbol` instead")
)]
#[inline]
pub fn symbol() -> RClass {
    get_ruby!().class_symbol()
}

/// Return Ruby's `Thread` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::class_thread`] for the
/// non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::class_thread` instead")
)]
#[inline]
pub fn thread() -> RClass {
    get_ruby!().class_thread()
}

/// Return Ruby's `Time` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::class_time`] for the
/// non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::class_time` instead")
)]
#[inline]
pub fn time() -> RClass {
    get_ruby!().class_time()
}

/// Return Ruby's `TrueClass` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::class_true_class`] for
/// the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::class_true_class` instead")
)]
#[inline]
pub fn true_class() -> RClass {
    get_ruby!().class_true_class()
}

/// Return Ruby's `UnboundMethod` class.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::class_unbound_method`]
/// for the non-panicking version.
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::class_unbound_method` instead")
)]
#[inline]
pub fn unbound_method() -> RClass {
    get_ruby!().class_unbound_method()
}
