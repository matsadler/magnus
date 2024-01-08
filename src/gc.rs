//! Functions for working with Ruby's Garbage Collector.
//!
//! See also [`Ruby`](Ruby#gc) for more GC related methods.

use std::{marker::PhantomData, ops::Range};

use rb_sys::{
    rb_gc_adjust_memory_usage, rb_gc_count, rb_gc_disable, rb_gc_enable, rb_gc_location,
    rb_gc_mark, rb_gc_mark_locations, rb_gc_mark_movable, rb_gc_register_address,
    rb_gc_register_mark_object, rb_gc_start, rb_gc_stat, rb_gc_unregister_address, VALUE,
};

use crate::{
    error::{protect, Error},
    r_hash::RHash,
    symbol::IntoSymbol,
    value::{private::ReprValue as _, ReprValue, Value},
    Ruby,
};

pub(crate) mod private {
    use super::*;

    pub trait Mark {
        fn raw(self) -> VALUE;
    }

    pub trait Locate {
        fn raw(self) -> VALUE;

        fn from_raw(val: VALUE) -> Self;
    }
}

/// Trait indicating types that can be passed to GC marking functions.
///
/// See [`Marker`].
pub trait Mark: private::Mark {}

impl<T> private::Mark for T
where
    T: ReprValue,
{
    fn raw(self) -> VALUE {
        self.as_rb_value()
    }
}
impl<T> Mark for T where T: ReprValue {}

impl<T> private::Mark for crate::value::Opaque<T>
where
    T: ReprValue,
{
    fn raw(self) -> VALUE {
        unsafe { Ruby::get_unchecked() }
            .get_inner(self)
            .as_rb_value()
    }
}
impl<T> Mark for crate::value::Opaque<T> where T: ReprValue {}

/// A handle to GC marking functions.
///
/// See also
/// [`DataTypeFunctions::mark`](`crate::typed_data::DataTypeFunctions::mark`).
pub struct Marker(PhantomData<*mut ()>);

impl Marker {
    pub(crate) fn new() -> Self {
        Self(PhantomData)
    }

    /// Mark an Object.
    ///
    /// Used to mark any stored Ruby objects when implementing
    /// [`DataTypeFunctions::mark`](`crate::typed_data::DataTypeFunctions::mark`).
    pub fn mark<T>(&self, value: T)
    where
        T: Mark,
    {
        unsafe { rb_gc_mark(value.raw()) };
    }

    /// Mark multiple Objects.
    ///
    /// Used to mark any stored Ruby objects when implementing
    /// [`DataTypeFunctions::mark`](`crate::typed_data::DataTypeFunctions::mark`).
    pub fn mark_slice<T>(&self, values: &[T])
    where
        T: Mark,
    {
        let Range { start, end } = values.as_ptr_range();
        unsafe { rb_gc_mark_locations(start as *const VALUE, end as *const VALUE) }
    }

    /// Mark an Object and let Ruby know it is moveable.
    ///
    /// The [`Value`] type is effectly a pointer to a Ruby object. Ruby's
    /// garbage collector will avoid moving objects exposed to extensions,
    /// unless you use this function to mark them during the GC marking phase.
    ///
    /// Used to mark any stored Ruby objects when implementing
    /// [`DataTypeFunctions::mark`](`crate::typed_data::DataTypeFunctions::mark`)
    /// and you have also implemented
    /// [`DataTypeFunctions::compact`](`crate::typed_data::DataTypeFunctions::compact`).
    ///
    /// Beware that any Ruby object passed to this function may later become
    /// invalid to use from Rust when GC is run, you must update any stored
    /// objects with [`Compactor::location`] inside your implementation of
    /// [`DataTypeFunctions::compact`](`crate::typed_data::DataTypeFunctions::compact`).
    pub fn mark_movable<T>(&self, value: T)
    where
        T: Mark,
    {
        unsafe { rb_gc_mark_movable(value.raw()) };
    }
}

/// Trait indicating types that can given to [`Compactor::location`].
pub trait Locate: private::Locate {}

impl<T> private::Locate for T
where
    T: ReprValue,
{
    fn raw(self) -> VALUE {
        self.as_rb_value()
    }

    fn from_raw(val: VALUE) -> Self {
        unsafe { Self::from_value_unchecked(Value::new(val)) }
    }
}
impl<T> Locate for T where T: ReprValue {}

impl<T> private::Locate for crate::value::Opaque<T>
where
    T: ReprValue,
{
    fn raw(self) -> VALUE {
        unsafe { Ruby::get_unchecked() }
            .get_inner(self)
            .as_rb_value()
    }

    fn from_raw(val: VALUE) -> Self {
        unsafe { T::from_value_unchecked(Value::new(val)) }.into()
    }
}
impl<T> Locate for crate::value::Opaque<T> where T: ReprValue {}

/// A handle to functions relating to GC compaction.
///
/// See also
/// [`DataTypeFunctions::compact`](`crate::typed_data::DataTypeFunctions::compact`).
pub struct Compactor(PhantomData<*mut ()>);

impl Compactor {
    pub(crate) fn new() -> Self {
        Self(PhantomData)
    }

    /// Get the new location of an object.
    ///
    /// The [`Value`] type is effectly a pointer to a Ruby object. Ruby's
    /// garbage collector will avoid moving objects exposed to extensions,
    /// unless the object has been marked with
    /// [`mark_movable`](Marker::mark_movable). When implementing
    /// [`DataTypeFunctions::compact`](`crate::typed_data::DataTypeFunctions::compact`)
    /// you will need to update any Ruby objects you are storing.
    ///
    /// Returns a new `T` that is pointing to the object that `value` used to
    /// point to. If `value` hasn't moved, simply returns `value`.
    pub fn location<T>(&self, value: T) -> T
    where
        T: Locate,
    {
        unsafe { T::from_raw(rb_gc_location(value.raw())) }
    }
}

/// Registers `value` to never be garbage collected.
///
/// This is essentially a deliberate memory leak.
///
/// # Examples
///
/// ```
/// use magnus::{gc, RArray, RString};
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// // will never be collected
/// let root = RArray::new();
/// gc::register_mark_object(root);
///
/// // won't be collected while it is in our `root` array
/// let s = RString::new("example");
/// root.push(s).unwrap();
/// ```
pub fn register_mark_object<T>(value: T)
where
    T: Mark,
{
    unsafe { rb_gc_register_mark_object(value.raw()) }
}

/// Inform Ruby's garbage collector that `valref` points to a live Ruby object.
///
/// Prevents Ruby moving or collecting `valref`. This should be used on
/// `static` items to prevent them being collected instead of relying on Ruby
/// constants/globals to allways refrence the value.
///
/// See also [`BoxValue`](crate::value::BoxValue).
///
/// # Examples
///
/// ```
/// use magnus::{gc, RString};
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// let s = RString::new("example");
///
/// // s won't be collected even though it's on the heap
/// let boxed = Box::new(s);
/// gc::register_address(&*boxed);
///
/// // ...
///
/// // allow s to be collected
/// gc::unregister_address(&*boxed);
/// drop(boxed);
/// ```
pub fn register_address<T>(valref: &T)
where
    T: Mark,
{
    unsafe { rb_gc_register_address(valref as *const _ as *mut VALUE) }
}

/// Inform Ruby's garbage collector that `valref` that was previously
/// registered with [`register_address`] no longer points to a live Ruby
/// object.
///
/// # Examples
///
/// ```
/// use magnus::{gc, RString};
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// let s = RString::new("example");
///
/// // s won't be collected even though it's on the heap
/// let boxed = Box::new(s);
/// gc::register_address(&*boxed);
///
/// // ...
///
/// // allow s to be collected
/// gc::unregister_address(&*boxed);
/// drop(boxed);
/// ```
pub fn unregister_address<T>(valref: &T)
where
    T: Mark,
{
    unsafe { rb_gc_unregister_address(valref as *const _ as *mut VALUE) }
}

/// # GC
///
/// Functions for working with Ruby's Garbage Collector.
///
/// See also the [`gc`](self) module.
impl Ruby {
    /// Disable automatic GC runs.
    ///
    /// This could result in other Ruby api functions unexpectedly raising
    /// `NoMemError`.
    ///
    /// Returns `true` if GC was already disabled, `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let was_disabled = ruby.gc_disable();
    ///
    ///     // GC is off
    ///
    ///     // return GC to previous state
    ///     if !was_disabled {
    ///         ruby.gc_enable();
    ///     }
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn gc_disable(&self) -> bool {
        unsafe { Value::new(rb_gc_disable()).to_bool() }
    }

    /// Enable automatic GC run.
    ///
    /// Garbage Collection is enabled by default, calling this function only
    /// makes sense if [`disable`] was previously called.
    ///
    /// Returns `true` if GC was previously disabled, `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let was_disabled = ruby.gc_enable();
    ///
    ///     // GC is on
    ///
    ///     // return GC to previous state
    ///     if was_disabled {
    ///         ruby.gc_disable();
    ///     }
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn gc_enable(&self) -> bool {
        unsafe { Value::new(rb_gc_enable()).to_bool() }
    }

    /// Trigger a "full" GC run.
    ///
    /// This will perform a full mark phase and a complete sweep phase, but may
    /// not run every single proceess associated with garbage collection.
    ///
    /// Finalisers will be deferred to run later.
    ///
    /// Currently (with versions of Ruby that support compaction) it will not
    /// trigger compaction.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     ruby.gc_start();
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn gc_start(&self) {
        unsafe { rb_gc_start() };
    }

    /// Inform Ruby of external memory usage.
    ///
    /// The Ruby GC is run when Ruby thinks it's running out of memory, but
    /// won't take into account any memory allocated outside of Ruby api
    /// functions. This function can be used to give Ruby a more accurate idea
    /// of how much memory the process is using.
    ///
    /// Pass negative numbers to indicate memory has been freed.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let buf = Vec::<u8>::with_capacity(1024 * 1024);
    ///     let mem_size = buf.capacity() * std::mem::size_of::<u8>();
    ///     ruby.gc_adjust_memory_usage(mem_size as isize);
    ///
    ///     // ...
    ///
    ///     drop(buf);
    ///     ruby.gc_adjust_memory_usage(-(mem_size as isize));
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn gc_adjust_memory_usage(&self, diff: isize) {
        unsafe { rb_gc_adjust_memory_usage(diff as _) };
    }

    /// Returns the number of garbage collections that have been run since the
    /// start of the process.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let before = ruby.gc_count();
    ///     ruby.gc_start();
    ///     assert!(ruby.gc_count() > before);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn gc_count(&self) -> usize {
        unsafe { rb_gc_count() as usize }
    }

    /// Returns the GC profiling value for `key`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     assert!(ruby.gc_stat("heap_live_slots")? > 1);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn gc_stat<T>(&self, key: T) -> Result<usize, Error>
    where
        T: IntoSymbol,
    {
        let sym = key.into_symbol_with(self);
        let mut res = 0;
        protect(|| {
            res = unsafe { rb_gc_stat(sym.as_rb_value()) as usize };
            self.qnil()
        })?;
        Ok(res)
    }

    /// Returns all possible key/value pairs for [`stat`] as a Ruby Hash.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let stats = ruby.gc_all_stats();
    ///     let live_slots: usize = stats.fetch(ruby.to_symbol("heap_live_slots"))?;
    ///     assert!(live_slots > 1);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn gc_all_stats(&self) -> RHash {
        let res = self.hash_new();
        unsafe { rb_gc_stat(res.as_rb_value()) };
        res
    }
}

/// Disable automatic GC runs.
///
/// This could result in other Ruby api functions unexpectedly raising
/// `NoMemError`.
///
/// Returns `true` if GC was already disabled, `false` otherwise.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::gc_disable`] for the
/// non-panicking version.
///
/// # Examples
///
/// ```
/// # #![allow(deprecated)]
/// use magnus::gc;
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// let was_disabled = gc::disable();
///
/// // GC is off
///
/// // return GC to previous state
/// if !was_disabled {
///     gc::enable();
/// }
/// ```
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::gc_disable` instead")
)]
#[inline]
pub fn disable() -> bool {
    get_ruby!().gc_disable()
}

/// Enable automatic GC run.
///
/// Garbage Collection is enabled by default, calling this function only makes
/// sense if [`disable`] was previously called.
///
/// Returns `true` if GC was previously disabled, `false` otherwise.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::gc_enable`] for the
/// non-panicking version.
///
/// # Examples
///
/// ```
/// # #![allow(deprecated)]
/// use magnus::gc;
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// let was_disabled = gc::enable();
///
/// // GC is on
///
/// // return GC to previous state
/// if was_disabled {
///     gc::disable();
/// }
/// ```
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::gc_enable` instead")
)]
#[inline]
pub fn enable() -> bool {
    get_ruby!().gc_enable()
}

/// Trigger a "full" GC run.
///
/// This will perform a full mark phase and a complete sweep phase, but may not
/// run every single proceess associated with garbage collection.
///
/// Finalisers will be deferred to run later.
///
/// Currently (with versions of Ruby that support compaction) it will not
/// trigger compaction.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::gc_start`] for the
/// non-panicking version.
///
/// # Examples
///
/// ```
/// # #![allow(deprecated)]
/// use magnus::gc;
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// gc::start();
/// ```
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::gc_start` instead")
)]
#[inline]
pub fn start() {
    get_ruby!().gc_start()
}

/// Inform Ruby of external memory usage.
///
/// The Ruby GC is run when Ruby thinks it's running out of memory, but won't
/// take into account any memory allocated outside of Ruby api functions. This
/// function can be used to give Ruby a more accurate idea of how much memory
/// the process is using.
///
/// Pass negative numbers to indicate memory has been freed.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See
/// [`Ruby::gc_adjust_memory_usage`] for the non-panicking version.
///
/// # Examples
///
/// ```
/// # #![allow(deprecated)]
/// use magnus::gc;
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// let buf = Vec::<u8>::with_capacity(1024 * 1024);
/// let mem_size = buf.capacity() * std::mem::size_of::<u8>();
/// gc::adjust_memory_usage(mem_size as isize);
///
/// // ...
///
/// drop(buf);
/// gc::adjust_memory_usage(-(mem_size as isize));
/// ```
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::gc_adjust_memory_usage` instead")
)]
#[inline]
pub fn adjust_memory_usage(diff: isize) {
    get_ruby!().gc_adjust_memory_usage(diff)
}

/// Returns the number of garbage collections that have been run since the
/// start of the process.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::gc_count`] for the
/// non-panicking version.
///
/// # Examples
///
/// ```
/// # #![allow(deprecated)]
/// use magnus::gc;
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// let before = gc::count();
/// gc::start();
/// assert!(gc::count() > before);
/// ```
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::gc_count` instead")
)]
#[inline]
pub fn count() -> usize {
    get_ruby!().gc_count()
}

/// Returns the GC profiling value for `key`.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::gc_stat`] for the
/// non-panicking version.
///
/// # Examples
///
/// ```
/// # #![allow(deprecated)]
/// use magnus::gc;
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// assert!(gc::stat("heap_live_slots").unwrap() > 1);
/// ```
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::gc_stat` instead")
)]
#[inline]
pub fn stat<T>(key: T) -> Result<usize, Error>
where
    T: IntoSymbol,
{
    let handle = get_ruby!();
    handle.gc_stat(key.into_symbol_with(&handle))
}

/// Returns all possible key/value pairs for [`stat`] as a Ruby Hash.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::gc_all_stats`] for the
/// non-panicking version.
///
/// # Examples
///
/// ```
/// # #![allow(deprecated)]
/// use magnus::{gc, Symbol};
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// let stats = gc::all_stats();
/// let live_slots: usize = stats.fetch(Symbol::new("heap_live_slots")).unwrap();
/// assert!(live_slots > 1);
/// ```
#[cfg_attr(
    not(feature = "old-api"),
    deprecated(note = "please use `Ruby::gc_all_stats` instead")
)]
#[inline]
pub fn all_stats() -> RHash {
    get_ruby!().gc_all_stats()
}
