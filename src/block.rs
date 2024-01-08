//! Types and functions for working with Ruby blocks and Procs.
//!
//! See also [`Ruby`](Ruby#blocks) for more block related methods.

use std::{
    fmt,
    mem::{forget, size_of},
    os::raw::c_int,
    slice,
};

use rb_sys::{
    rb_block_given_p, rb_block_proc, rb_data_typed_object_wrap, rb_obj_is_proc, rb_proc_arity,
    rb_proc_call_kw, rb_proc_lambda_p, rb_proc_new, rb_yield, rb_yield_splat, rb_yield_values_kw,
    VALUE,
};

use crate::{
    data_type_builder,
    enumerator::Enumerator,
    error::{ensure, protect, Error},
    gc,
    into_value::{kw_splat, ArgList, IntoValue, RArrayArgList},
    method::{Block, BlockReturn},
    object::Object,
    r_array::RArray,
    try_convert::TryConvert,
    typed_data::{DataType, DataTypeFunctions},
    value::{
        private::{self, ReprValue as _},
        NonZeroValue, ReprValue, Value,
    },
    Ruby,
};

/// # `Proc`
///
/// Functions that can be used to create instances of [`Proc`], Ruby's
/// representation of a block as an object.
///
/// See also the [`Proc`] type.
impl Ruby {
    /// Create a new `Proc`.
    ///
    /// As `block` is a function pointer, only functions and closures that do
    /// not capture any variables are permitted. For more flexibility (at the
    /// cost of allocating) see [`proc_from_fn`](Ruby::proc_from_fn).
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{prelude::*, rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let proc = ruby.proc_new(|_ruby, args, _block| {
    ///         let acc = i64::try_convert(*args.get(0).unwrap())?;
    ///         let i = i64::try_convert(*args.get(1).unwrap())?;
    ///         Ok(acc + i)
    ///     });
    ///
    ///     rb_assert!(ruby, "proc.call(1, 2) == 3", proc);
    ///
    ///     rb_assert!(ruby, "[1, 2, 3, 4, 5].inject(&proc) == 15", proc);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn proc_new<R>(&self, block: fn(&Ruby, &[Value], Option<Proc>) -> R) -> Proc
    where
        R: BlockReturn,
    {
        unsafe extern "C" fn call<R>(
            _yielded_arg: VALUE,
            callback_arg: VALUE,
            argc: c_int,
            argv: *const VALUE,
            blockarg: VALUE,
        ) -> VALUE
        where
            R: BlockReturn,
        {
            let func =
                std::mem::transmute::<VALUE, fn(&Ruby, &[Value], Option<Proc>) -> R>(callback_arg);
            func.call_handle_error(argc, argv as *const Value, Value::new(blockarg))
                .as_rb_value()
        }

        let call_func =
            call::<R> as unsafe extern "C" fn(VALUE, VALUE, c_int, *const VALUE, VALUE) -> VALUE;

        unsafe {
            #[allow(clippy::fn_to_numeric_cast)]
            Proc::from_rb_value_unchecked(rb_proc_new(Some(call_func), block as VALUE))
        }
    }

    /// Create a new `Proc`.
    ///
    /// See also [`proc_new`](Ruby::proc_new), which is more efficient when
    /// `block` is a function or closure that does not capture any variables.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{prelude::*, rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let mut count = 0;
    ///
    ///     let proc = ruby.proc_from_fn(move |_ruby, args, _block| {
    ///         let step = i64::try_convert(*args.get(0).unwrap())?;
    ///         count += step;
    ///         Ok(count)
    ///     });
    ///
    ///     rb_assert!(ruby, "proc.call(1) == 1", proc);
    ///     rb_assert!(ruby, "proc.call(1) == 2", proc);
    ///     rb_assert!(ruby, "proc.call(2) == 4", proc);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn proc_from_fn<F, R>(&self, block: F) -> Proc
    where
        F: 'static + Send + FnMut(&Ruby, &[Value], Option<Proc>) -> R,
        R: BlockReturn,
    {
        unsafe extern "C" fn call<F, R>(
            _yielded_arg: VALUE,
            callback_arg: VALUE,
            argc: c_int,
            argv: *const VALUE,
            blockarg: VALUE,
        ) -> VALUE
        where
            F: FnMut(&Ruby, &[Value], Option<Proc>) -> R,
            R: BlockReturn,
        {
            let closure = &mut *(callback_arg as *mut F);
            closure
                .call_handle_error(argc, argv as *const Value, Value::new(blockarg))
                .as_rb_value()
        }

        let (closure, keepalive) = wrap_closure(block);
        let call_func =
            call::<F, R> as unsafe extern "C" fn(VALUE, VALUE, c_int, *const VALUE, VALUE) -> VALUE;

        let proc = unsafe {
            Proc::from_rb_value_unchecked(rb_proc_new(Some(call_func), closure as VALUE))
        };
        // ivar without @ prefix is invisible from Ruby
        proc.ivar_set("__rust_closure", keepalive).unwrap();
        proc
    }
}

/// Wrapper type for a Value known to be an instance of Ruby’s Proc class.
///
/// See the [`ReprValue`] and [`Object`] traits for additional methods
/// available on this type. See [`Ruby`](Ruby#proc) for methods to create a
/// `Proc`.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Proc(NonZeroValue);

impl Proc {
    /// Return `Some(Proc)` if `val` is a `Proc`, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{block::Proc, eval, Value};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let val: Value = eval("Proc.new {|a, b| a + b}").unwrap();
    /// assert!(Proc::from_value(val).is_some());
    ///
    /// let val: Value = eval("1 + 2").unwrap();
    /// assert!(Proc::from_value(val).is_none());
    /// ```
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            Value::new(rb_obj_is_proc(val.as_rb_value()))
                .to_bool()
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        Self(NonZeroValue::new_unchecked(Value::new(val)))
    }

    /// Create a new `Proc`.
    ///
    /// As `block` is a function pointer, only functions and closures that do
    /// not capture any variables are permitted. For more flexibility (at the
    /// cost of allocating) see [`from_fn`](Proc::from_fn).
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread. See [`Ruby::proc_new`] for the
    /// non-panicking version.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(deprecated)]
    /// use magnus::{block::Proc, prelude::*, rb_assert};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let proc = Proc::new(|_ruby, args, _block| {
    ///     let acc = i64::try_convert(*args.get(0).unwrap())?;
    ///     let i = i64::try_convert(*args.get(1).unwrap())?;
    ///     Ok(acc + i)
    /// });
    ///
    /// rb_assert!("proc.call(1, 2) == 3", proc);
    ///
    /// rb_assert!("[1, 2, 3, 4, 5].inject(&proc) == 15", proc);
    /// ```
    #[cfg_attr(
        not(feature = "old-api"),
        deprecated(note = "please use `Ruby::proc_new` instead")
    )]
    #[inline]
    pub fn new<R>(block: fn(&Ruby, &[Value], Option<Proc>) -> R) -> Self
    where
        R: BlockReturn,
    {
        get_ruby!().proc_new(block)
    }

    /// Create a new `Proc`.
    ///
    /// See also [`Proc::new`], which is more efficient when `block` is a
    /// function or closure that does not capture any variables.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread. See [`Ruby::proc_from_fn`] for
    /// the non-panicking version.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(deprecated)]
    /// use magnus::{block::Proc, prelude::*, rb_assert};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let mut count = 0;
    ///
    /// let proc = Proc::from_fn(move |_ruby, args, _block| {
    ///     let step = i64::try_convert(*args.get(0).unwrap())?;
    ///     count += step;
    ///     Ok(count)
    /// });
    ///
    /// rb_assert!("proc.call(1) == 1", proc);
    /// rb_assert!("proc.call(1) == 2", proc);
    /// rb_assert!("proc.call(2) == 4", proc);
    /// ```
    #[cfg_attr(
        not(feature = "old-api"),
        deprecated(note = "please use `Ruby::proc_from_fn` instead")
    )]
    #[inline]
    pub fn from_fn<F, R>(block: F) -> Self
    where
        F: 'static + Send + FnMut(&Ruby, &[Value], Option<Proc>) -> R,
        R: BlockReturn,
    {
        get_ruby!().proc_from_fn(block)
    }

    /// Call the proc with `args`.
    ///
    /// Returns `Ok(T)` if the proc runs without error and the return value
    /// converts into a `T`, or returns `Err` if the proc raises or the
    /// conversion fails.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{block::Proc, eval, Integer, RArray};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let proc: Proc = eval("Proc.new {|a, b| a + b}").unwrap();
    ///
    /// // call with a tuple
    /// let result: i64 = proc.call((1, 2)).unwrap();
    /// assert_eq!(3, result);
    ///
    /// // call with a slice
    /// let result: i64 = proc
    ///     .call(&[Integer::from_i64(3), Integer::from_i64(4)][..])
    ///     .unwrap();
    /// assert_eq!(7, result);
    ///
    /// // call with an array
    /// let result: i64 = proc
    ///     .call([Integer::from_i64(5), Integer::from_i64(6)])
    ///     .unwrap();
    /// assert_eq!(11, result);
    ///
    /// // call with a Ruby array
    /// let array = RArray::from_vec(vec![7, 8]);
    /// let result: i64 = proc.call(array).unwrap();
    /// assert_eq!(15, result);
    /// ```
    ///
    /// With keyword arguments:
    ///
    /// ```
    /// use magnus::{block::Proc, eval, kwargs};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let proc: Proc = eval("Proc.new {|a, b:, c:| a + b + c}").unwrap();
    ///
    /// let result: i64 = proc.call((1, kwargs!("b" => 2, "c" => 3))).unwrap();
    /// assert_eq!(6, result);
    /// ```
    ///
    /// Ignoring return value:
    ///
    /// ```
    /// use magnus::{block::Proc, eval, rb_assert, Value};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let proc: Proc = eval("Proc.new { $called = true }").unwrap();
    ///
    /// let _: Value = proc.call(()).unwrap();
    ///
    /// rb_assert!("$called == true");
    /// ```
    pub fn call<A, T>(self, args: A) -> Result<T, Error>
    where
        A: RArrayArgList,
        T: TryConvert,
    {
        let kw_splat = kw_splat(&args);
        let args = args.into_array_arg_list_with(&Ruby::get_with(self));
        unsafe {
            protect(|| {
                Value::new(rb_proc_call_kw(
                    self.as_rb_value(),
                    args.as_rb_value(),
                    kw_splat as c_int,
                ))
            })
            .and_then(TryConvert::try_convert)
        }
    }

    /// Returns the number of arguments `self` takes.
    ///
    /// If `self` takes no arguments, returns `0`.
    /// If `self` takes only required arguments, returns the number of required
    /// arguments.
    /// If `self` is a lambda and has optional arguments, or is not a lambda
    /// and takes a splat argument, returns `-n-1`, where `n` is the number of
    /// required arguments.
    /// If `self` is not a lambda, and takes a finite number of optional
    /// arguments, returns the number of required arguments.
    /// Keyword arguments are considered as a single additional argument, that
    /// argument being required if any keyword argument is required.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{block::Proc, eval};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let proc: Proc = eval("proc {nil}").unwrap();
    /// assert_eq!(proc.arity(), 0);
    ///
    /// let proc: Proc = eval("proc {|a| a + 1}").unwrap();
    /// assert_eq!(proc.arity(), 1);
    ///
    /// let proc: Proc = eval("proc {|a, b| a + b}").unwrap();
    /// assert_eq!(proc.arity(), 2);
    ///
    /// let proc: Proc = eval("proc {|*args| args.sum}").unwrap();
    /// assert_eq!(proc.arity(), -1);
    /// ```
    pub fn arity(self) -> i64 {
        unsafe { rb_proc_arity(self.as_rb_value()) as i64 }
    }

    /// Returns whether or not `self` is a lambda.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{block::Proc, eval};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let proc: Proc = eval("proc {|a, b| a + b}").unwrap();
    /// assert!(!proc.is_lambda());
    ///
    /// let proc: Proc = eval("lambda {|a, b| a + b}").unwrap();
    /// assert!(proc.is_lambda());
    /// ```
    pub fn is_lambda(self) -> bool {
        unsafe { Value::new(rb_proc_lambda_p(self.as_rb_value())).to_bool() }
    }
}

impl fmt::Display for Proc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for Proc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl IntoValue for Proc {
    #[inline]
    fn into_value_with(self, _: &Ruby) -> Value {
        self.0.get()
    }
}

impl Object for Proc {}

unsafe impl private::ReprValue for Proc {}

impl ReprValue for Proc {}

impl TryConvert for Proc {
    fn try_convert(val: Value) -> Result<Self, Error> {
        let handle = Ruby::get_with(val);
        if let Some(p) = Proc::from_value(val) {
            return Ok(p);
        }
        let p_val: Value = match val.funcall("to_proc", ()) {
            Ok(v) => v,
            Err(_) => {
                return Err(Error::new(
                    handle.exception_type_error(),
                    format!("no implicit conversion of {} into Proc", unsafe {
                        val.classname()
                    },),
                ))
            }
        };
        Proc::from_value(val).ok_or_else(|| {
            Error::new(
                handle.exception_type_error(),
                format!(
                    "can't convert {0} to Proc ({0}#to_proc gives {1})",
                    unsafe { val.classname() },
                    unsafe { p_val.classname() },
                ),
            )
        })
    }
}

/// Wrap a closure in a Ruby object with no class.
///
/// This effectivly makes the closure's lifetime managed by Ruby. It will be
/// dropped when the returned `Value` is garbage collected.
fn wrap_closure<F, R>(func: F) -> (*mut F, Value)
where
    F: FnMut(&Ruby, &[Value], Option<Proc>) -> R,
    R: BlockReturn,
{
    struct Closure<F>(F, DataType);
    unsafe impl<F> Send for Closure<F> {}
    impl<F> DataTypeFunctions for Closure<F> {
        fn mark(&self, marker: &gc::Marker) {
            // Attempt to mark any Ruby values captured in a closure.
            // Rust's closures are structs that contain all the values they
            // have captured. This reads that struct as a slice of VALUEs and
            // calls rb_gc_mark_locations which calls gc_mark_maybe which
            // marks VALUEs and ignores non-VALUEs
            marker.mark_slice(unsafe {
                slice::from_raw_parts(
                    &self.0 as *const _ as *const Value,
                    size_of::<F>() / size_of::<Value>(),
                )
            });
        }
    }

    let data_type = data_type_builder!(Closure<F>, "rust closure")
        .free_immediately()
        .mark()
        .build();

    let boxed = Box::new(Closure(func, data_type));
    let ptr = Box::into_raw(boxed);
    let value = unsafe {
        Value::new(rb_data_typed_object_wrap(
            0, // using 0 for the class will hide the object from ObjectSpace
            ptr as *mut _,
            (*ptr).1.as_rb_data_type() as *const _,
        ))
    };
    unsafe { (&mut (*ptr).0 as *mut F, value) }
}

/// # Blocks
///
/// Functions to enable working with Ruby blocks.
///
/// See also the [`block`](self) module.
impl Ruby {
    /// Returns whether a Ruby block has been supplied to the current method.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{function, rb_assert, Error, Ruby};
    ///
    /// fn got_block(ruby: &Ruby) -> bool {
    ///     ruby.block_given()
    /// }
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     ruby.define_global_function("got_block?", function!(got_block, 0));
    ///
    ///     rb_assert!(ruby, "got_block? {} == true");
    ///     rb_assert!(ruby, "got_block? == false");
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn block_given(&self) -> bool {
        unsafe { rb_block_given_p() != 0 }
    }

    /// Returns the block given to the current method as a [`Proc`] instance.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{block::Proc, function, rb_assert, Error, Ruby};
    ///
    /// fn make_proc(ruby: &Ruby) -> Result<Proc, Error> {
    ///     ruby.block_proc()
    /// }
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     ruby.define_global_function("make_proc", function!(make_proc, 0));
    ///
    ///     rb_assert!(ruby, "make_proc {}.is_a?(Proc)");
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn block_proc(&self) -> Result<Proc, Error> {
        let val = unsafe { protect(|| Value::new(rb_block_proc()))? };
        Ok(Proc::from_value(val).unwrap())
    }

    /// Yields a value to the block given to the current method.
    ///
    /// **Note:** A method using `yield_value` converted to an Enumerator with
    /// `to_enum`/[`Value::enumeratorize`] will result in a non-functional
    /// Enumerator on versions of Ruby before 3.1. See [`Yield`] for an
    /// alternative.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{function, rb_assert, Error, Ruby, Value};
    ///
    /// fn metasyntactic_variables(ruby: &Ruby) -> Result<(), Error> {
    ///     let _: Value = ruby.yield_value("foo")?;
    ///     let _: Value = ruby.yield_value("bar")?;
    ///     let _: Value = ruby.yield_value("baz")?;
    ///     Ok(())
    /// }
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     ruby.define_global_function(
    ///         "metasyntactic_variables",
    ///         function!(metasyntactic_variables, 0),
    ///     );
    ///
    ///     let vars = ruby.ary_new();
    ///     rb_assert!(
    ///         ruby,
    ///         "metasyntactic_variables {|var| vars << var} == nil",
    ///         vars
    ///     );
    ///     rb_assert!(ruby, r#"vars == ["foo", "bar", "baz"]"#, vars);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn yield_value<T, U>(&self, val: T) -> Result<U, Error>
    where
        T: IntoValue,
        U: TryConvert,
    {
        let val = self.into_value(val);
        unsafe {
            protect(|| Value::new(rb_yield(val.as_rb_value()))).and_then(TryConvert::try_convert)
        }
    }

    /// Yields multiple values to the block given to the current method.
    ///
    /// **Note:** A method using `yield_values` converted to an Enumerator with
    /// `to_enum`/[`Value::enumeratorize`] will result in a non-functional
    /// Enumerator on versions of Ruby before 3.1. See [`YieldValues`] for an
    /// alternative.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{function, kwargs, rb_assert, Error, Ruby, Value};
    ///
    /// fn metasyntactic_variables(ruby: &Ruby) -> Result<(), Error> {
    ///     let _: Value = ruby.yield_values((0, kwargs!("var" => "foo")))?;
    ///     let _: Value = ruby.yield_values((1, kwargs!("var" => "bar")))?;
    ///     let _: Value = ruby.yield_values((2, kwargs!("var" => "baz")))?;
    ///     Ok(())
    /// }
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     ruby.define_global_function(
    ///         "metasyntactic_variables",
    ///         function!(metasyntactic_variables, 0),
    ///     );
    ///
    ///     let vars = ruby.ary_new();
    ///     rb_assert!(
    ///         ruby,
    ///         "metasyntactic_variables {|pos, var:| vars << [pos, var]} == nil",
    ///         vars
    ///     );
    ///     rb_assert!(
    ///         ruby,
    ///         r#"vars == [[0, "foo"], [1, "bar"], [2, "baz"]]"#,
    ///         vars
    ///     );
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn yield_values<T, U>(&self, vals: T) -> Result<U, Error>
    where
        T: ArgList,
        U: TryConvert,
    {
        let kw_splat = kw_splat(&vals);
        let vals = vals.into_arg_list_with(self);
        let slice = vals.as_ref();
        unsafe {
            protect(|| {
                Value::new(rb_yield_values_kw(
                    slice.len() as c_int,
                    slice.as_ptr() as *const VALUE,
                    kw_splat as c_int,
                ))
            })
            .and_then(TryConvert::try_convert)
        }
    }

    /// Yields a Ruby Array to the block given to the current method.
    ///
    /// **Note:** A method using `yield_splat` converted to an Enumerator with
    /// `to_enum`/[`Value::enumeratorize`] will result in a non-functional
    /// Enumerator on versions of Ruby before 3.1. See [`YieldSplat`] for an
    /// alternative.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{function, rb_assert, Error, Ruby, Value};
    ///
    /// fn metasyntactic_variables(ruby: &Ruby) -> Result<(), Error> {
    ///     let ary = ruby.ary_new();
    ///     ary.push(0)?;
    ///     ary.push("foo")?;
    ///     let _: Value = ruby.yield_splat(ary)?;
    ///     let ary = ruby.ary_new();
    ///     ary.push(1)?;
    ///     ary.push("bar")?;
    ///     let _: Value = ruby.yield_splat(ary)?;
    ///     let ary = ruby.ary_new();
    ///     ary.push(2)?;
    ///     ary.push("baz")?;
    ///     let _: Value = ruby.yield_splat(ary)?;
    ///     Ok(())
    /// }
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     ruby.define_global_function(
    ///         "metasyntactic_variables",
    ///         function!(metasyntactic_variables, 0),
    ///     );
    ///
    ///     let vars = ruby.ary_new();
    ///     rb_assert!(
    ///         ruby,
    ///         "metasyntactic_variables {|pos, var| vars << [pos, var]} == nil",
    ///         vars
    ///     );
    ///     rb_assert!(
    ///         ruby,
    ///         r#"vars == [[0, "foo"], [1, "bar"], [2, "baz"]]"#,
    ///         vars
    ///     );
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn yield_splat<T>(&self, vals: RArray) -> Result<T, Error>
    where
        T: TryConvert,
    {
        unsafe {
            protect(|| Value::new(rb_yield_splat(vals.as_rb_value())))
                .and_then(TryConvert::try_convert)
        }
    }
}

/// Returns whether a Ruby block has been supplied to the current method.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::block_given`] for the
/// non-panicking version.
///
/// # Examples
///
/// ```
/// # #![allow(deprecated)]
/// use magnus::{block::block_given, define_global_function, function, rb_assert};
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// fn got_block() -> bool {
///     block_given()
/// }
///
/// define_global_function("got_block?", function!(got_block, 0));
///
/// rb_assert!("got_block? {} == true");
/// rb_assert!("got_block? == false");
/// ```
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::block_given` instead")
)]
#[inline]
pub fn block_given() -> bool {
    get_ruby!().block_given()
}

/// Returns the block given to the current method as a [`Proc`] instance.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::block_proc`] for the
/// non-panicking version.
///
/// # Examples
///
/// ```
/// # #![allow(deprecated)]
/// use magnus::{
///     block::{block_proc, Proc},
///     define_global_function, function, rb_assert, Error,
/// };
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// fn make_proc() -> Result<Proc, Error> {
///     block_proc()
/// }
///
/// define_global_function("make_proc", function!(make_proc, 0));
///
/// rb_assert!("make_proc {}.is_a?(Proc)");
/// ```
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::block_proc` instead")
)]
#[inline]
pub fn block_proc() -> Result<Proc, Error> {
    get_ruby!().block_proc()
}

/// Yields a value to the block given to the current method.
///
/// **Note:** A method using `yield_value` converted to an Enumerator with
/// `to_enum`/[`Value::enumeratorize`] will result in a non-functional
/// Enumerator on versions of Ruby before 3.1. See [`Yield`] for an
/// alternative.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::yield_value`] for the
/// non-panicking version.
///
/// # Examples
///
/// ```
/// # #![allow(deprecated)]
/// use magnus::{
///     block::yield_value, define_global_function, function, rb_assert, Error, RArray, Value,
/// };
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// fn metasyntactic_variables() -> Result<(), Error> {
///     let _: Value = yield_value("foo")?;
///     let _: Value = yield_value("bar")?;
///     let _: Value = yield_value("baz")?;
///     Ok(())
/// }
///
/// define_global_function(
///     "metasyntactic_variables",
///     function!(metasyntactic_variables, 0),
/// );
///
/// let vars = RArray::new();
/// rb_assert!("metasyntactic_variables {|var| vars << var} == nil", vars);
/// rb_assert!(r#"vars == ["foo", "bar", "baz"]"#, vars);
/// ```
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::yield_value` instead")
)]
#[inline]
pub fn yield_value<T, U>(val: T) -> Result<U, Error>
where
    T: IntoValue,
    U: TryConvert,
{
    get_ruby!().yield_value(val)
}

/// Yields multiple values to the block given to the current method.
///
/// **Note:** A method using `yield_values` converted to an Enumerator with
/// `to_enum`/[`Value::enumeratorize`] will result in a non-functional
/// Enumerator on versions of Ruby before 3.1. See [`YieldValues`] for an
/// alternative.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::yield_values`] for the
/// non-panicking version.
///
/// # Examples
///
/// ```
/// # #![allow(deprecated)]
/// use magnus::{
///     block::yield_values, define_global_function, function, rb_assert, Error, RArray, Value,
/// };
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// fn metasyntactic_variables() -> Result<(), Error> {
///     let _: Value = yield_values((0, "foo"))?;
///     let _: Value = yield_values((1, "bar"))?;
///     let _: Value = yield_values((2, "baz"))?;
///     Ok(())
/// }
///
/// define_global_function(
///     "metasyntactic_variables",
///     function!(metasyntactic_variables, 0),
/// );
///
/// let vars = RArray::new();
/// rb_assert!(
///     "metasyntactic_variables {|pos, var| vars << [pos, var]} == nil",
///     vars
/// );
/// rb_assert!(r#"vars == [[0, "foo"], [1, "bar"], [2, "baz"]]"#, vars);
/// ```
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::yield_values` instead")
)]
#[inline]
pub fn yield_values<T, U>(vals: T) -> Result<U, Error>
where
    T: ArgList,
    U: TryConvert,
{
    get_ruby!().yield_values(vals)
}

/// Yields a Ruby Array to the block given to the current method.
///
/// **Note:** A method using `yield_splat` converted to an Enumerator with
/// `to_enum`/[`Value::enumeratorize`] will result in a non-functional
/// Enumerator on versions of Ruby before 3.1. See [`YieldSplat`] for an
/// alternative.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::yield_splat`] for the
/// non-panicking version.
///
/// # Examples
///
/// ```
/// # #![allow(deprecated)]
/// use magnus::{
///     block::yield_splat, define_global_function, function, rb_assert, Error, RArray, Value,
/// };
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// fn metasyntactic_variables() -> Result<(), Error> {
///     let ary = RArray::new();
///     ary.push(0)?;
///     ary.push("foo")?;
///     let _: Value = yield_splat(ary)?;
///     let ary = RArray::new();
///     ary.push(1)?;
///     ary.push("bar")?;
///     let _: Value = yield_splat(ary)?;
///     let ary = RArray::new();
///     ary.push(2)?;
///     ary.push("baz")?;
///     let _: Value = yield_splat(ary)?;
///     Ok(())
/// }
///
/// define_global_function(
///     "metasyntactic_variables",
///     function!(metasyntactic_variables, 0),
/// );
///
/// let vars = RArray::new();
/// rb_assert!(
///     "metasyntactic_variables {|pos, var| vars << [pos, var]} == nil",
///     vars
/// );
/// rb_assert!(r#"vars == [[0, "foo"], [1, "bar"], [2, "baz"]]"#, vars);
/// ```
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::yield_splat` instead")
)]
#[inline]
pub fn yield_splat<T>(vals: RArray) -> Result<T, Error>
where
    T: TryConvert,
{
    get_ruby!().yield_splat(vals)
}

// Our regular implementation of `yield` breaks yielding methods being
// converted to Enumerators because of the protect call not being compatible
// with the fibers used in Ruby itself to implement `Enumerator#next`.
// We have to use protect in `yield` because otherwise Ruby code can
// `break`/`return` through Rust code and break Rust invariants.
// This gives up using `protect` by instead using `ensure`, not exposing the
// `yield` call to user code, and maintaining the invariants ourselves. As it
// can still be `brake`/`return`ed though it can't be public as it's only safe
// to call as the last thing in one of our method wrappers (where the raise
// would normally go). Returning an iterator from a method will trigger this.
pub(crate) unsafe fn do_yield_iter<I, T>(mut iter: I)
where
    I: Iterator<Item = T>,
    T: IntoValue,
{
    let handle = Ruby::get_unchecked();
    let ptr = &mut iter as *mut I;
    forget(iter); // we're going to drop this ourself;
                  // ensure runs the first closure, but yield may raise, so the first
                  // closure might never reach the end, so wouldn't drop. The second
                  // closure is always run, and always after the first, so we do the
                  // drop there
    ensure(
        || {
            for val in &mut *ptr {
                rb_yield(handle.into_value(val).as_rb_value());
            }
            handle.qnil()
        },
        || {
            ptr.drop_in_place();
        },
    );
}

// see do_yield_iter
pub(crate) unsafe fn do_yield_values_iter<I, T>(mut iter: I)
where
    I: Iterator<Item = T>,
    T: ArgList,
{
    let handle = Ruby::get_unchecked();
    let ptr = &mut iter as *mut I;
    forget(iter);
    ensure(
        || {
            for val in &mut *ptr {
                let kw_splat = kw_splat(&val);
                let vals = val.into_arg_list_with(&handle);
                let slice = vals.as_ref();
                rb_yield_values_kw(
                    slice.len() as c_int,
                    slice.as_ptr() as *const VALUE,
                    kw_splat as c_int,
                );
            }
            handle.qnil()
        },
        || {
            ptr.drop_in_place();
        },
    );
}

// see do_yield_iter
pub(crate) unsafe fn do_yield_splat_iter<I>(mut iter: I)
where
    I: Iterator<Item = RArray>,
{
    let ptr = &mut iter as *mut I;
    forget(iter);
    ensure(
        || {
            for val in &mut *ptr {
                rb_yield_splat(val.as_rb_value());
            }
            Ruby::get_unchecked().qnil()
        },
        || {
            ptr.drop_in_place();
        },
    );
}

/// Helper type for functions that either yield a single value to a block or
/// return an Enumerator.
///
/// `I` must implement `Iterator<Item = T>`, where `T` implements [`IntoValue`].
///
/// # Examples
///
/// ```
/// use magnus::{
///     block::{block_given, Yield},
///     define_global_function, eval, method,
///     prelude::*,
///     rb_assert, RArray, Value,
/// };
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// fn count_to_3(rb_self: Value) -> Yield<impl Iterator<Item = u8>> {
///     if block_given() {
///         Yield::Iter(1..=3)
///     } else {
///         Yield::Enumerator(rb_self.enumeratorize("count_to_3", ()))
///     }
/// }
///
/// define_global_function("count_to_3", method!(count_to_3, 0));
///
/// // call Ruby method with a block.
/// let a = RArray::new();
/// rb_assert!("count_to_3 {|i| a << i} == nil", a);
/// rb_assert!("a == [1, 2, 3]", a);
///
/// // call Ruby method without a block.
/// let enumerator: Value = eval("count_to_3").unwrap();
///
/// rb_assert!("enumerator.next == 1", enumerator);
/// rb_assert!("enumerator.next == 2", enumerator);
/// ```
pub enum Yield<I> {
    /// Yields `I::Item` to given block.
    Iter(I),
    /// Returns `Enumerator` from the method.
    Enumerator(Enumerator),
}

/// Helper type for functions that either yield multiple values to a block or
/// return an Enumerator.
///
/// `I` must implement `Iterator<Item = T>`, where `T` implements [`ArgList`].
///
/// # Examples
///
/// ```
/// use magnus::{
///     block::{block_given, YieldValues},
///     define_global_function, eval, method,
///     prelude::*,
///     rb_assert, RArray, Value,
/// };
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// fn count_to_3_abc(rb_self: Value) -> YieldValues<impl Iterator<Item = (u8, char)>> {
///     if block_given() {
///         YieldValues::Iter((1..=3).zip('a'..='c'))
///     } else {
///         YieldValues::Enumerator(rb_self.enumeratorize("count_to_3_abc", ()))
///     }
/// }
///
/// define_global_function("count_to_3_abc", method!(count_to_3_abc, 0));
///
/// // call Ruby method with a block.
/// let a = RArray::new();
/// rb_assert!("count_to_3_abc {|i, c| a << [i, c]} == nil", a);
/// rb_assert!(r#"a == [[1, "a"], [2, "b"], [3, "c"]]"#, a);
///
/// // call Ruby method without a block.
/// let enumerator: Value = eval("count_to_3_abc").unwrap();
///
/// rb_assert!(r#"enumerator.next == [1, "a"]"#, enumerator);
/// rb_assert!(r#"enumerator.next == [2, "b"]"#, enumerator);
/// ```
pub enum YieldValues<I> {
    /// Yields `I::Item` to given block.
    Iter(I),
    /// Returns `Enumerator` from the method.
    Enumerator(Enumerator),
}

/// Helper type for functions that either yield an array to a block or
/// return an Enumerator.
///
/// `I` must implement `Iterator<Item = RArray>`.
///
/// # Examples
///
/// ```
/// use magnus::{
///     block::{block_given, YieldSplat},
///     define_global_function, eval, method,
///     prelude::*,
///     rb_assert, RArray, Value,
/// };
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// fn count_to_3_abc(rb_self: Value) -> YieldSplat<impl Iterator<Item = RArray>> {
///     if block_given() {
///         YieldSplat::Iter((1..=3).zip('a'..='c').map(|(i, c)| {
///             let ary = RArray::new();
///             ary.push(i).unwrap();
///             ary.push(c).unwrap();
///             ary
///         }))
///     } else {
///         YieldSplat::Enumerator(rb_self.enumeratorize("count_to_3_abc", ()))
///     }
/// }
///
/// define_global_function("count_to_3_abc", method!(count_to_3_abc, 0));
///
/// // call Ruby method with a block.
/// let a = RArray::new();
/// rb_assert!("count_to_3_abc {|i, c| a << [i, c]} == nil", a);
/// rb_assert!(r#"a == [[1, "a"], [2, "b"], [3, "c"]]"#, a);
///
/// // call Ruby method without a block.
/// let enumerator: Value = eval("count_to_3_abc").unwrap();
///
/// rb_assert!(r#"enumerator.next == [1, "a"]"#, enumerator);
/// rb_assert!(r#"enumerator.next == [2, "b"]"#, enumerator);
/// ```
pub enum YieldSplat<I> {
    /// Yields `I::Item` to given block.
    Iter(I),
    /// Returns `Enumerator` from the method.
    Enumerator(Enumerator),
}
