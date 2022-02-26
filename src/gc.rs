//! Functions for working with Ruby's Garbage Collector.

use std::ops::Deref;

use crate::{
    ruby_sys::{
        rb_gc_adjust_memory_usage, rb_gc_disable, rb_gc_enable, rb_gc_location, rb_gc_mark,
        rb_gc_mark_locations, rb_gc_mark_movable, rb_gc_start, ssize_t, VALUE,
    },
    value::Value,
};

/// Mark an Object.
///
/// Used to mark any stored Ruby objects when implementing
/// [`DataTypeFunctions::mark`](`crate::r_typed_data::DataTypeFunctions::mark`).
pub fn mark<T>(value: T)
where
    T: Deref<Target = Value>,
{
    unsafe { rb_gc_mark(value.as_rb_value()) };
}

/// Mark multiple Objects.
///
/// Used to mark any stored Ruby objects when implementing
/// [`DataTypeFunctions::mark`](`crate::r_typed_data::DataTypeFunctions::mark`).
pub fn mark_slice(values: &[Value]) {
    if let (Some(start), Some(end)) = (values.first(), values.last()) {
        unsafe {
            rb_gc_mark_locations(
                start as *const _ as *const VALUE,
                end as *const _ as *const VALUE,
            )
        }
    };
}

/// Mark an Object and let Ruby know it is moveable.
///
/// The [`Value`] type is effectly a pointer to a Ruby object. Ruby's garbage
/// collector will avoid moving objects exposed to extensions, unless you use
/// this function to mark them during the GC marking phase.
///
/// Used to mark any stored Ruby objects when implementing
/// [`DataTypeFunctions::mark`](`crate::r_typed_data::DataTypeFunctions::mark`)
/// and you have also implemented
/// [`DataTypeFunctions::compact`](`crate::r_typed_data::DataTypeFunctions::compact`).
///
/// Beware that any Ruby object passed to this function may later become
/// invalid to use from Rust when GC is run, you must update any stored objects
/// with [`location`] inside your implementation of
/// [`DataTypeFunctions::compact`](`crate::r_typed_data::DataTypeFunctions::compact`).
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
/// [`DataTypeFunctions::compact`](`crate::r_typed_data::DataTypeFunctions::compact`)
/// you will need to update any Ruby objects you are storing.
///
/// Returns a new `Value` that is pointing to the object that `value` used to
/// point to. If `value` hasn't moved, simply returns `value`.
pub fn location(value: Value) -> Value {
    unsafe { Value::new(rb_gc_location(value.as_rb_value())) }
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
/// sense if [`disabled`] was previously called.
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
pub fn adjust_memory_usage(diff: i32) {
    unsafe { rb_gc_adjust_memory_usage(diff as ssize_t) };
}
