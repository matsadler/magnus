//! Functions for working with Ruby's Garbage Collector.

use std::ops::{Deref, Range};

use rb_sys::{
    rb_gc_adjust_memory_usage, rb_gc_count, rb_gc_disable, rb_gc_enable, rb_gc_mark,
    rb_gc_mark_locations, rb_gc_register_address, rb_gc_register_mark_object, rb_gc_start,
    rb_gc_stat, rb_gc_unregister_address, VALUE,
};
#[cfg(ruby_gte_2_7)]
use rb_sys::{rb_gc_location, rb_gc_mark_movable};

use crate::{
    error::{protect, Error},
    r_hash::RHash,
    symbol::Symbol,
    value::{ReprValue, Value, QNIL},
};

#[cfg(target_pointer_width = "64")]
type DiffSize = i64;

#[cfg(target_pointer_width = "32")]
type DiffSize = i32;

/// Mark an Object.
///
/// Used to mark any stored Ruby objects when implementing
/// [`DataTypeFunctions::mark`](`crate::typed_data::DataTypeFunctions::mark`).
pub fn mark<T>(value: T)
where
    T: Deref<Target = Value>,
{
    unsafe { rb_gc_mark(value.as_rb_value()) };
}

/// Mark multiple Objects.
///
/// Used to mark any stored Ruby objects when implementing
/// [`DataTypeFunctions::mark`](`crate::typed_data::DataTypeFunctions::mark`).
pub fn mark_slice<T>(values: &[T])
where
    T: ReprValue,
{
    let Range { start, end } = values.as_ptr_range();
    unsafe { rb_gc_mark_locations(start as *const VALUE, end as *const VALUE) }
}

/// Mark an Object and let Ruby know it is moveable.
///
/// The [`Value`] type is effectly a pointer to a Ruby object. Ruby's garbage
/// collector will avoid moving objects exposed to extensions, unless you use
/// this function to mark them during the GC marking phase.
///
/// Used to mark any stored Ruby objects when implementing
/// [`DataTypeFunctions::mark`](`crate::typed_data::DataTypeFunctions::mark`)
/// and you have also implemented
/// [`DataTypeFunctions::compact`](`crate::typed_data::DataTypeFunctions::compact`).
///
/// Beware that any Ruby object passed to this function may later become
/// invalid to use from Rust when GC is run, you must update any stored objects
/// with [`location`] inside your implementation of
/// [`DataTypeFunctions::compact`](`crate::typed_data::DataTypeFunctions::compact`).
#[cfg(any(ruby_gte_2_7, docsrs))]
#[cfg_attr(docsrs, doc(cfg(ruby_gte_2_7)))]
pub fn mark_movable<T>(value: T)
where
    T: Deref<Target = Value>,
{
    unsafe { rb_gc_mark_movable(value.as_rb_value()) };
}

/// Get the new location of an object.
///
/// The [`Value`] type is effectly a pointer to a Ruby object. Ruby's garbage
/// collector will avoid moving objects exposed to extensions, unless the
/// object has been marked with [`mark_movable`]. When implementing
/// [`DataTypeFunctions::compact`](`crate::typed_data::DataTypeFunctions::compact`)
/// you will need to update any Ruby objects you are storing.
///
/// Returns a new `Value` that is pointing to the object that `value` used to
/// point to. If `value` hasn't moved, simply returns `value`.
#[cfg(any(ruby_gte_2_7, docsrs))]
#[cfg_attr(docsrs, doc(cfg(ruby_gte_2_7)))]
pub fn location<T>(value: T) -> T
where
    T: ReprValue,
{
    unsafe { T::from_value_unchecked(Value::new(rb_gc_location(value.to_value().as_rb_value()))) }
}

/// Registers `value` to never be garbage collected.
///
/// This is essentially a deliberate memory leak.
pub fn register_mark_object<T>(value: T)
where
    T: ReprValue,
{
    unsafe { rb_gc_register_mark_object(value.to_value().as_rb_value()) }
}

/// Inform Ruby's garbage collector that `valref` points to a live Ruby object.
///
/// Prevents Ruby moving or collecting `valref`. This should be used on
/// `static` items to prevent them being collected instead of relying on Ruby
/// constants/globals to allways refrence the value.
///
/// See also [`BoxValue`](crate::value::BoxValue).
pub fn register_address<T>(valref: &T)
where
    T: ReprValue,
{
    unsafe { rb_gc_register_address(valref as *const _ as *mut VALUE) }
}

/// Inform Ruby's garbage collector that `valref` that was previously
/// registered with [`register_address`] no longer points to a live Ruby
/// object.
pub fn unregister_address<T>(valref: &T)
where
    T: ReprValue,
{
    unsafe { rb_gc_unregister_address(valref as *const _ as *mut VALUE) }
}

/// Disable automatic GC runs.
///
/// This could result in other Ruby api functions unexpectedly raising
/// `NoMemError`.
///
/// Returns `true` if GC was already disabled, `false` otherwise.
pub fn disable() -> bool {
    unsafe { Value::new(rb_gc_disable()).to_bool() }
}

/// Enable automatic GC run.
///
/// Garbage Collection is enabled by default, calling this function only makes
/// sense if [`disable`] was previously called.
///
/// Returns `true` if GC was previously disabled, `false` otherwise.
pub fn enable() -> bool {
    unsafe { Value::new(rb_gc_enable()).to_bool() }
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
pub fn start() {
    unsafe { rb_gc_start() };
}

/// Inform Ruby of external memory usage.
///
/// The Ruby GC is run when Ruby thinks it's running out of memory, but won't
/// take into account any memory allocated outside of Ruby api functions. This
/// function can be used to give Ruby a more accurate idea of how much memory
/// the process is using.
///
/// Pass negative numbers to indicate memory has been freed.
pub fn adjust_memory_usage(diff: DiffSize) {
    unsafe { rb_gc_adjust_memory_usage(diff) };
}

/// Returns the number of garbage collections that have been run since the
/// start of the process.
pub fn count() -> usize {
    unsafe { rb_gc_count() as usize }
}

/// Returns the GC profiling value for `key`.
pub fn stat<T>(key: T) -> Result<usize, Error>
where
    T: Into<Symbol>,
{
    let sym = key.into();
    let mut res = 0;
    protect(|| {
        res = unsafe { rb_gc_stat(sym.as_rb_value()) as usize };
        QNIL
    })?;
    Ok(res)
}

/// Returns all possible key/value pairs for [`stat`] as a Ruby Hash.
pub fn all_stats() -> RHash {
    let res = RHash::new();
    unsafe { rb_gc_stat(res.as_rb_value()) };
    res
}
