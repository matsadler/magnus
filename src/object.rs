use std::{
    ffi::{CString, c_void},
    mem::transmute,
};

use rb_sys::{
    VALUE, rb_define_singleton_method, rb_extend_object, rb_ivar_get, rb_ivar_set,
    rb_singleton_class,
};

use crate::{
    Ruby,
    class::RClass,
    error::{Error, protect},
    into_value::IntoValue,
    method::Method,
    module::RModule,
    try_convert::TryConvert,
    value::{IntoId, ReprValue, Value, private::ReprValue as _},
};

/// Functions available all non-immediate values.
pub trait Object: ReprValue + Copy {
    /// Define a singleton method in `self`'s scope.
    ///
    /// Singleton methods defined on a class are Ruby's method for implementing
    /// 'class' methods.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby, function, prelude::*, rb_assert};
    ///
    /// fn test() -> i64 {
    ///     42
    /// }
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let module = ruby.define_module("Example")?;
    ///     module.define_singleton_method("test", function!(test, 0))?;
    ///     rb_assert!(ruby, "Example.test == 42");
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    ///
    /// ```
    /// use magnus::{Error, Ruby, function, prelude::*, rb_assert};
    ///
    /// #[magnus::wrap(class = "Point", free_immediately, size)]
    /// struct Point {
    ///     x: isize,
    ///     y: isize,
    /// }
    ///
    /// impl Point {
    ///     fn new(x: isize, y: isize) -> Self {
    ///         Self { x, y }
    ///     }
    /// }
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let class = ruby.define_class("Point", ruby.class_object())?;
    ///     class.define_singleton_method("new", function!(Point::new, 2))?;
    ///
    ///     rb_assert!(ruby, "Point.new(1, 2).is_a?(Point)");
    ///
    ///     Ok(())
    /// }
    /// # let _ = Point { x: 1, y: 2 }.x + Point { x: 3, y: 4 }.y;
    /// # Ruby::init(example).unwrap()
    /// ```
    fn define_singleton_method<M>(self, name: &str, func: M) -> Result<(), Error>
    where
        M: Method,
    {
        debug_assert_value!(self);
        let name = CString::new(name).unwrap();
        protect(|| {
            unsafe {
                rb_define_singleton_method(
                    self.as_rb_value(),
                    name.as_ptr(),
                    transmute::<*mut c_void, Option<unsafe extern "C" fn() -> VALUE>>(
                        func.as_ptr(),
                    ),
                    M::arity().into(),
                )
            };
            Ruby::get_with(self).qnil()
        })?;
        Ok(())
    }

    /// Get the value for the instance variable `name` within `self`'s scope.
    ///
    /// Note, the `@` is part of the name. An instance variable can be set and
    /// retrieved without a preceding `@` and it will work, but the instance
    /// variable will be invisible to Ruby code.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, RObject, Ruby, prelude::*};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let val: RObject = ruby.eval(
    ///         r#"
    ///             class Example
    ///               def initialize(value)
    ///                 @value = value
    ///               end
    ///             end
    ///             Example.new("foo")
    ///         "#,
    ///     )?;
    ///
    ///     assert_eq!(val.ivar_get::<_, String>("@value")?, "foo");
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    fn ivar_get<T, U>(self, name: T) -> Result<U, Error>
    where
        T: IntoId,
        U: TryConvert,
    {
        debug_assert_value!(self);
        let id = name.into_id_with(&Ruby::get_with(self));
        let res = unsafe { protect(|| Value::new(rb_ivar_get(self.as_rb_value(), id.as_rb_id()))) };
        res.and_then(TryConvert::try_convert)
    }

    /// Set the value for the instance variable `name` within `self`'s scope.
    ///
    /// Note, the `@` is part of the name. Setting an instance variable without
    /// a preceding `@` will work, but the instance variable will be invisible
    /// to Ruby code.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, RObject, Ruby, prelude::*, rb_assert};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let obj: RObject = ruby.eval(
    ///         r#"
    ///             class Example
    ///               def initialize(value)
    ///                 @value = value
    ///               end
    ///
    ///               def value
    ///                 @value
    ///               end
    ///             end
    ///             Example.new("foo")
    ///         "#,
    ///     )?;
    ///
    ///     obj.ivar_set("@value", "bar")?;
    ///     rb_assert!(ruby, r#"obj.value == "bar""#, obj);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    fn ivar_set<T, U>(self, name: T, value: U) -> Result<(), Error>
    where
        T: IntoId,
        U: IntoValue,
    {
        debug_assert_value!(self);
        let handle = Ruby::get_with(self);
        let id = name.into_id_with(&handle);
        let value = value.into_value_with(&handle);
        unsafe {
            protect(|| {
                Value::new(rb_ivar_set(
                    self.as_rb_value(),
                    id.as_rb_id(),
                    value.as_rb_value(),
                ))
            })
        }?;
        Ok(())
    }

    /// Finds or creates the singleton class of `self`.
    ///
    /// Returns `Err` if `self` can not have a singleton class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby, prelude::*};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     assert!(ruby.str_new("example").singleton_class().is_ok());
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    fn singleton_class(self) -> Result<RClass, Error> {
        protect(|| unsafe {
            RClass::from_rb_value_unchecked(rb_singleton_class(self.as_rb_value()))
        })
    }

    /// Extend `self` with `module`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, RObject, Ruby, function, prelude::*, rb_assert};
    ///
    /// fn test() -> i64 {
    ///     42
    /// }
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let module = ruby.module_new();
    ///     module.define_method("test", function!(test, 0))?;
    ///
    ///     let obj = RObject::try_convert(ruby.class_object().new_instance(())?)?;
    ///     obj.extend_object(module)?;
    ///     rb_assert!(ruby, "obj.test == 42", obj);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    fn extend_object(self, module: RModule) -> Result<(), Error> {
        protect(|| {
            unsafe { rb_extend_object(self.as_rb_value(), module.as_rb_value()) };
            Ruby::get_with(self).qnil()
        })?;
        Ok(())
    }
}
