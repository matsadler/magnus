use std::{ffi::CString, mem::transmute};

use rb_sys::{
    rb_define_singleton_method, rb_extend_object, rb_ivar_get, rb_ivar_set, rb_singleton_class,
};

use crate::{
    class::RClass,
    error::{protect, Error},
    into_value::IntoValue,
    method::Method,
    module::RModule,
    try_convert::TryConvert,
    value::{private::ReprValue as _, IntoId, ReprValue, Value},
    Ruby,
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
    /// use magnus::{define_module, function, prelude::*, rb_assert};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// fn example() -> i64 {
    ///     42
    /// }
    ///
    /// let module = define_module("Example").unwrap();
    /// module
    ///     .define_singleton_method("example", function!(example, 0))
    ///     .unwrap();
    /// rb_assert!("Example.example == 42");
    /// ```
    ///
    /// ```
    /// use magnus::{class, define_class, function, prelude::*, rb_assert};
    /// # let _cleanup = unsafe { magnus::embed::init() };
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
    /// let class = define_class("Point", class::object()).unwrap();
    /// class
    ///     .define_singleton_method("new", function!(Point::new, 2))
    ///     .unwrap();
    ///
    /// rb_assert!("Point.new(1, 2).is_a?(Point)");
    /// # let _ = Point { x: 1, y: 2 }.x + Point { x: 3, y: 4 }.y;
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
                    transmute(func.as_ptr()),
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
    /// use magnus::{eval, prelude::*, RObject};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let val: RObject = eval(
    ///     r#"
    ///       class Example
    ///         def initialize(value)
    ///           @value = value
    ///         end
    ///       end
    ///       Example.new("foo")
    ///     "#,
    /// )
    /// .unwrap();
    ///
    /// assert_eq!(val.ivar_get::<_, String>("@value").unwrap(), "foo");
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
    /// use magnus::{eval, prelude::*, rb_assert, RObject};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let obj: RObject = eval(
    ///     r#"
    ///       class Example
    ///         def initialize(value)
    ///           @value = value
    ///         end
    ///
    ///         def value
    ///           @value
    ///         end
    ///       end
    ///       Example.new("foo")
    ///     "#,
    /// )
    /// .unwrap();
    ///
    /// obj.ivar_set("@value", "bar").unwrap();
    /// rb_assert!(r#"obj.value == "bar""#, obj);
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
    /// use magnus::{prelude::*, RString};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(RString::new("example").singleton_class().is_ok());
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
    /// use magnus::{class, function, prelude::*, rb_assert, RModule, RObject};
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
    /// let obj = RObject::try_convert(class::object().new_instance(()).unwrap()).unwrap();
    /// obj.extend_object(module).unwrap();
    /// rb_assert!("obj.example == 42", obj);
    /// ```
    fn extend_object(self, module: RModule) -> Result<(), Error> {
        protect(|| {
            unsafe { rb_extend_object(self.as_rb_value(), module.as_rb_value()) };
            Ruby::get_with(self).qnil()
        })?;
        Ok(())
    }
}
