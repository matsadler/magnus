//! This module/file's name is a hack to get the `impl Ruby` defined here to
//! show first in docs. This module shouldn't be exposed publicly.

use std::{cell::RefCell, marker::PhantomData};

use rb_sys::ruby_native_thread_p;

// Ruby does not expose this publicly, but it is used in the fiddle gem via
// this kind of hack, and although the function is marked experimental in
// Ruby's source, that comment and the code have been unchanged singe 1.9.2,
// 14 years ago as of writing.
extern "C" {
    fn ruby_thread_has_gvl_p() -> ::std::os::raw::c_int;
}

use crate::{error::RubyUnavailableError, value::ReprValue};

#[derive(Clone, Copy)]
enum RubyGvlState {
    Locked,
    Unlocked,
    NonRubyThread,
}

thread_local! {
    static RUBY_GVL_STATE: RefCell<Option<RubyGvlState>> = RefCell::new(None);
}

impl RubyGvlState {
    fn current() -> Self {
        let current = if unsafe { ruby_thread_has_gvl_p() } != 0 {
            Self::Locked
        } else if unsafe { ruby_native_thread_p() != 0 } {
            Self::Unlocked
        } else {
            Self::NonRubyThread
        };
        RUBY_GVL_STATE.with(|ruby_gvl_state| {
            *ruby_gvl_state.borrow_mut() = Some(current);
        });
        current
    }

    fn cached() -> Self {
        RUBY_GVL_STATE.with(|ruby_gvl_state| {
            let x = *ruby_gvl_state.borrow();
            match x {
                // assumed not to change because there's currently no api to
                // unlock.
                Some(Self::Locked) => Self::Locked,
                None => Self::current(),
                // Don't expect without an api to unlock, so skip cache
                Some(Self::Unlocked) => Self::current(),
                // assumed not to change
                Some(Self::NonRubyThread) => Self::NonRubyThread,
            }
        })
    }

    fn ok<T>(self, value: T) -> Result<T, RubyUnavailableError> {
        match self {
            Self::Locked => Ok(value),
            Self::Unlocked => Err(RubyUnavailableError::GvlUnlocked),
            Self::NonRubyThread => Err(RubyUnavailableError::NonRubyThread),
        }
    }
}

/// A handle to access Ruby's API.
///
/// Using Ruby's API requires the Ruby VM to be initalised and all access to be
/// from a Ruby-created thread.
///
/// This structure allows safe access to Ruby's API as it should only be
/// possible to aquire an instance in situations where Ruby's API is known to
/// be available.
///
/// Many functions that take Ruby values as arguments are available directly
/// without having to use a `Ruby` handle, as being able to provide a Ruby
/// value is 'proof' the function is being called from a Ruby thread. Because
/// of this most methods defined on `Ruby` deal with creating Ruby objects
/// from Rust data.
///
/// ---
///
/// The methods available on `Ruby` are broken up into sections for easier
/// navigation.
///
/// To get a `Ruby` handle see [Accessing `Ruby`](#accessing-ruby).
///
/// To get a value from [`Opaque`][crate::value::Opaque] or
/// [`Lazy`][crate::value::Lazy] see the section on
/// [Extracting values from `Opaque`/`Lazy`](#extracting-values-from-opaquelazy).
///
/// For wrapping Rust data in a Ruby object see the sections on
/// [`typed_data::Obj`](#typed_dataobj) and [`RTypedData`](#rtypeddata).
///
/// To create a Ruby `Module` see the [`RModule`](#rmodule) section.
///
/// To get Ruby's `true` / `false` / `nil` see [true](#true) / [false](#false)
/// / [nil](#nil).
///
/// To get references to Ruby's core classes and modules such as `Object`,
/// `StandardError`, and `Math` see [Core Classes](#core-classes),
/// [Core Exceptions](#core-exceptions), and [Core Modules](#core-modules).
///
/// For creating `Array`s see the [`RArray`](#rarray) section.
///
/// To create `Hash`es see [`RHash`](#rhash).
///
/// For working with strings see the [`RString`](#rstring),
/// [`Encoding`](#encoding), [`RbEncoding`](#rbencoding), and
/// [Encoding Index](#encoding-index) sections.
///
/// Functions to create Regular Expressions are in the [`RRegexp`](#rregexp)
/// section.
///
/// The sections for [`Symbol`](#symbol), [`StaticSymbol`](#staticsymbol), and
/// [`Id`](#id) cover workering with Ruby's `Symbol`s.
///
/// Numbers of various types can be created with functions from the following
/// sections: [`Integer`](#integer), [`Fixnum`](#fixnum), [`RBignum`](#rbignum),
/// [`Float`](#float), [`Flonum`](#flonum), [`RFloat`](#rfloat), and
/// [`RRational`](#rrational).
///
/// For Ruby `Struct`s see [`Struct`](#struct).
///
/// To create a Ruby `Range` see the [`Range`](#range) section.
///
/// The sections on [`Proc`](#proc), [blocks](#blocks) and [`break`](#break)
/// cover working with Ruby's `Proc`s and blocks.
///
/// The [Globals](#globals) section contains functions for defining global
/// variables, constants, etc, as well as accessing current state such as
/// calling the current `super` method.
///
/// The [Argument Parsing](#argument-parsing) section contains functions for
/// handling argument parsing.
///
/// For functions related to Garbage Collection see the [GC](#gc) section.
///
/// The [Embedding](#embedding) section contains functions relevant when
/// embedding Ruby in a Rust program.
pub struct Ruby(PhantomData<*mut ()>);

/// # Accessing `Ruby`
///
/// These functions allow you to obtain a `Ruby` handle only when the current
/// thread is a Ruby thread.
impl Ruby {
    /// Get a handle to Ruby's API.
    ///
    /// Returns a new handle to Ruby's API if it can be verified the current
    /// thread is a Ruby thread.
    ///
    /// If the Ruby API is not useable, returns `Err(RubyUnavailableError)`.
    pub fn get() -> Result<Self, RubyUnavailableError> {
        RubyGvlState::cached().ok(Self(PhantomData))
    }

    /// Get a handle to Ruby's API.
    ///
    /// Returns a new handle to Ruby's API using a Ruby value as proof that the
    /// current thread is a Ruby thread.
    ///
    /// Note that all Ruby values are [`Copy`], so this will not take ownership
    /// of the passed value.
    #[allow(unused_variables)]
    pub fn get_with<T>(value: T) -> Self
    where
        T: ReprValue,
    {
        Self(PhantomData)
    }

    /// Get a handle to Ruby's API.
    ///
    /// # Safety
    ///
    /// This must only be called from a Ruby thread - that is one created by
    /// Ruby, or the main thread after [`embed::init`](crate::embed::init) has
    /// been called - and without having released the GVL.
    #[inline]
    pub unsafe fn get_unchecked() -> Self {
        Self(PhantomData)
    }
}
