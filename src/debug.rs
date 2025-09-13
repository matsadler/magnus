//! Types and functions for working with Ruby's debugging tools.
//!
//! See also [`Ruby`](Ruby#debug) for more debugging related methods.

use std::{ffi::c_int, ptr::null_mut};

use rb_sys::{
    VALUE, rb_profile_frame_absolute_path, rb_profile_frame_base_label, rb_profile_frame_classpath,
    rb_profile_frame_first_lineno, rb_profile_frame_full_label, rb_profile_frame_label,
    rb_profile_frame_method_name, rb_profile_frame_path, rb_profile_frame_qualified_method_name,
    rb_profile_frame_singleton_method_p, rb_profile_frames, ruby_special_consts,
};

use crate::{
    Ruby, gc,
    integer::Integer,
    r_string::RString,
    value::{ReprValue, Value},
};

/// # Debug
///
/// Ruby's debugging tools.
impl Ruby {
    /// Fill `buf` with backtrace [`Frame`]s.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::cell::RefCell;
    ///
    /// use magnus::{Error, Ruby, Value, debug::FrameBuf, eval, function, prelude::*};
    ///
    /// thread_local! {
    ///     static FRAMES: RefCell<FrameBuf<1024>> = const { RefCell::new(FrameBuf::new()) };
    /// }
    ///
    /// fn profile(ruby: &Ruby) {
    ///     FRAMES.with_borrow_mut(|buf| {
    ///         ruby.profile_frames(buf);
    ///     });
    /// }
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     ruby.define_global_function("profile", function!(profile, 0));
    ///
    ///     let _: Value = eval!(
    ///         "def foo = bar
    ///          def bar = baz
    ///          def baz = profile"
    ///     )?;
    ///     let _: Value = ruby.class_object().funcall("foo", ())?;
    ///
    ///     let unknown = ruby.str_new("<unknown>");
    ///     let frames = FRAMES.with_borrow(|val| {
    ///         val.iter()
    ///             .map(|(frame, _line)| frame.full_label().unwrap_or(unknown).to_string())
    ///             .collect::<Result<Vec<String>, Error>>()
    ///     })?;
    ///     assert_eq!(
    ///         frames,
    ///         &["Kernel#profile", "Object#baz", "Object#bar", "Object#foo"]
    ///     );
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn profile_frames<const N: usize>(&self, buf: &mut FrameBuf<N>) {
        unsafe {
            buf.filled = profile_frames_impl(0, &mut buf.frames, Some(&mut buf.lines));
        }
    }

    /// Fill `buf` with backtrace [`Frame`]s, skipping the topmost `start`
    /// frames.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::cell::RefCell;
    ///
    /// use magnus::{Error, Ruby, Value, debug::FrameBuf, eval, function, prelude::*};
    ///
    /// thread_local! {
    ///     static FRAMES: RefCell<FrameBuf<1024>> = const { RefCell::new(FrameBuf::new()) };
    /// }
    ///
    /// fn profile(ruby: &Ruby) {
    ///     FRAMES.with_borrow_mut(|buf| {
    ///         ruby.profile_frames_starting(1, buf);
    ///     });
    /// }
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     ruby.define_global_function("profile", function!(profile, 0));
    ///
    ///     let _: Value = eval!(
    ///         "def foo = bar
    ///          def bar = baz
    ///          def baz = profile"
    ///     )?;
    ///     let _: Value = ruby.class_object().funcall("foo", ())?;
    ///
    ///     let unknown = ruby.str_new("<unknown>");
    ///     let frames = FRAMES.with_borrow(|val| {
    ///         val.iter()
    ///             .map(|(frame, _line)| frame.full_label().unwrap_or(unknown).to_string())
    ///             .collect::<Result<Vec<String>, Error>>()
    ///     })?;
    ///     assert_eq!(frames, &["Object#baz", "Object#bar", "Object#foo"]);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[cfg(any(ruby_gte_3_4, docsrs))]
    #[cfg_attr(docsrs, doc(cfg(ruby_gte_3_4)))]
    pub fn profile_frames_starting<const N: usize>(&self, start: usize, buf: &mut FrameBuf<N>) {
        unsafe {
            buf.filled = profile_frames_impl(start, &mut buf.frames, Some(&mut buf.lines));
        }
    }
}

/// A backtrace frame pointer.
///
/// `Frame`s should be [treated as Ruby objects](crate#safety) as they are
/// managed by Ruby GC, but are not object that can be returned to Ruby or
/// work with Ruby's standard APIs.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Frame(Value);

impl Frame {
    const EMPTY: Frame = Frame(Value::new(ruby_special_consts::RUBY_Qnil as VALUE));

    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, RArray, Ruby, Value, debug::FrameBuf, eval, function, prelude::*};
    ///
    /// fn baz(ruby: &Ruby) -> RArray {
    ///     let mut buf = FrameBuf::<64>::new();
    ///     ruby.profile_frames(&mut buf);
    ///     ruby.ary_from_iter(buf.iter().map(|(frame, _line)| frame.path()))
    /// }
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     ruby.define_global_function("baz", function!(baz, 0));
    ///     let _: Value = eval!(
    ///         "def foo = bar
    ///          def bar = baz"
    ///     )?;
    ///     let res: Vec<Option<String>> = ruby.class_object().funcall("foo", ())?;
    ///     assert_eq!(
    ///         res,
    ///         &[
    ///             None,
    ///             Some(String::from("(eval at -e:0)")),
    ///             Some(String::from("(eval at -e:0)"))
    ///         ]
    ///     );
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn path(self) -> Option<RString> {
        unsafe {
            let val = rb_profile_frame_path(self.0.as_rb_value());
            (!Value::new(val).is_nil()).then_some(RString::from_rb_value_unchecked(val))
        }
    }

    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, RArray, Ruby, Value, debug::FrameBuf, eval, function, prelude::*};
    ///
    /// fn baz(ruby: &Ruby) -> RArray {
    ///     let mut buf = FrameBuf::<64>::new();
    ///     ruby.profile_frames(&mut buf);
    ///     ruby.ary_from_iter(buf.iter().map(|(frame, _line)| frame.absolute_path()))
    /// }
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     ruby.define_global_function("baz", function!(baz, 0));
    ///     let _: Value = eval!(
    ///         "def foo = bar
    ///          def bar = baz"
    ///     )?;
    ///     let res: Vec<Option<String>> = ruby.class_object().funcall("foo", ())?;
    ///     assert_eq!(res, &[Some(String::from("<cfunc>")), None, None]);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn absolute_path(self) -> Option<RString> {
        unsafe {
            let val = rb_profile_frame_absolute_path(self.0.as_rb_value());
            (!Value::new(val).is_nil()).then_some(RString::from_rb_value_unchecked(val))
        }
    }

    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, RArray, Ruby, Value, debug::FrameBuf, eval, function, prelude::*};
    ///
    /// fn baz(ruby: &Ruby) -> RArray {
    ///     let mut buf = FrameBuf::<64>::new();
    ///     ruby.profile_frames(&mut buf);
    ///     ruby.ary_from_iter(buf.iter().map(|(frame, _line)| frame.label()))
    /// }
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     ruby.define_global_function("baz", function!(baz, 0));
    ///     let _: Value = eval!(
    ///         "def foo = bar
    ///          def bar = baz"
    ///     )?;
    ///     let res: Vec<Option<String>> = ruby.class_object().funcall("foo", ())?;
    ///     assert_eq!(res, &[None, Some(String::from("bar")), Some(String::from("foo"))]);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn label(self) -> Option<RString> {
        unsafe {
            let val = rb_profile_frame_label(self.0.as_rb_value());
            (!Value::new(val).is_nil()).then_some(RString::from_rb_value_unchecked(val))
        }
    }

    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, RArray, Ruby, Value, debug::FrameBuf, eval, function, prelude::*};
    ///
    /// fn baz(ruby: &Ruby) -> RArray {
    ///     let mut buf = FrameBuf::<64>::new();
    ///     ruby.profile_frames(&mut buf);
    ///     ruby.ary_from_iter(buf.iter().map(|(frame, _line)| frame.base_label()))
    /// }
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     ruby.define_global_function("baz", function!(baz, 0));
    ///     let _: Value = eval!(
    ///         "def foo = bar
    ///          def bar = baz"
    ///     )?;
    ///     let res: Vec<Option<String>> = ruby.class_object().funcall("foo", ())?;
    ///     assert_eq!(res, &[None, Some(String::from("bar")), Some(String::from("foo"))]);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn base_label(self) -> Option<RString> {
        unsafe {
            let val = rb_profile_frame_base_label(self.0.as_rb_value());
            (!Value::new(val).is_nil()).then_some(RString::from_rb_value_unchecked(val))
        }
    }

    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, RArray, Ruby, Value, debug::FrameBuf, eval, function, prelude::*};
    ///
    /// fn baz(ruby: &Ruby) -> RArray {
    ///     let mut buf = FrameBuf::<64>::new();
    ///     ruby.profile_frames(&mut buf);
    ///     ruby.ary_from_iter(buf.iter().map(|(frame, _line)| frame.full_label()))
    /// }
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     ruby.define_global_function("baz", function!(baz, 0));
    ///     let _: Value = eval!(
    ///         "def foo = bar
    ///          def bar = baz"
    ///     )?;
    ///     let res: Vec<String> = ruby.class_object().funcall("foo", ())?;
    ///     assert_eq!(res, &["Kernel#baz", "Object#bar", "Object#foo"]);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn full_label(self) -> Option<RString> {
        unsafe {
            let val = rb_profile_frame_full_label(self.0.as_rb_value());
            (!Value::new(val).is_nil()).then_some(RString::from_rb_value_unchecked(val))
        }
    }

    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, RArray, Ruby, Value, debug::FrameBuf, eval, function, prelude::*};
    ///
    /// fn baz(ruby: &Ruby) -> RArray {
    ///     let mut buf = FrameBuf::<64>::new();
    ///     ruby.profile_frames(&mut buf);
    ///     ruby.ary_from_iter(buf.iter().map(|(frame, _line)| frame.first_lineno()))
    /// }
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     ruby.define_global_function("baz", function!(baz, 0));
    ///     let _: Value = eval!(
    ///         "def foo = bar
    ///          def bar = baz"
    ///     )?;
    ///     let res: Vec<Option<usize>> = ruby.class_object().funcall("foo", ())?;
    ///     assert_eq!(res, &[None, Some(2), Some(1)]);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn first_lineno(self) -> Option<usize> {
        unsafe {
            let val = rb_profile_frame_first_lineno(self.0.as_rb_value());
            (!Value::new(val).is_nil())
                .then(|| Integer::from_rb_value_unchecked(val).to_usize().unwrap())
        }
    }

    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, RArray, Ruby, Value, debug::FrameBuf, eval, function, prelude::*};
    ///
    /// fn baz(ruby: &Ruby) -> RArray {
    ///     let mut buf = FrameBuf::<64>::new();
    ///     ruby.profile_frames(&mut buf);
    ///     ruby.ary_from_iter(buf.iter().map(|(frame, _line)| frame.classpath()))
    /// }
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     ruby.define_global_function("baz", function!(baz, 0));
    ///     let _: Value = eval!(
    ///         "def foo = bar
    ///          def bar = baz"
    ///     )?;
    ///     let res: Vec<String> = ruby.class_object().funcall("foo", ())?;
    ///     assert_eq!(res, &["Kernel", "Object", "Object"]);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn classpath(self) -> Option<RString> {
        unsafe {
            let val = rb_profile_frame_classpath(self.0.as_rb_value());
            (!Value::new(val).is_nil()).then_some(RString::from_rb_value_unchecked(val))
        }
    }

    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, RArray, Ruby, Value, debug::FrameBuf, eval, function, prelude::*};
    ///
    /// fn baz(ruby: &Ruby) -> RArray {
    ///     let mut buf = FrameBuf::<64>::new();
    ///     ruby.profile_frames(&mut buf);
    ///     ruby.ary_from_iter(buf.iter().map(|(frame, _line)| frame.is_singleton_method()))
    /// }
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     ruby.define_global_function("baz", function!(baz, 0));
    ///     let _: Value = eval!(
    ///         "def foo = bar
    ///          def bar = baz"
    ///     )?;
    ///     let res: Vec<bool> = ruby.class_object().funcall("foo", ())?;
    ///     assert_eq!(res, &[false, false, false]);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn is_singleton_method(self) -> bool {
        unsafe { Value::new(rb_profile_frame_singleton_method_p(self.0.as_rb_value())).to_bool() }
    }

    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, RArray, Ruby, Value, debug::FrameBuf, eval, function, prelude::*};
    ///
    /// fn baz(ruby: &Ruby) -> RArray {
    ///     let mut buf = FrameBuf::<64>::new();
    ///     ruby.profile_frames(&mut buf);
    ///     ruby.ary_from_iter(buf.iter().map(|(frame, _line)| frame.method_name()))
    /// }
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     ruby.define_global_function("baz", function!(baz, 0));
    ///     let _: Value = eval!(
    ///         "def foo = bar
    ///          def bar = baz"
    ///     )?;
    ///     let res: Vec<String> = ruby.class_object().funcall("foo", ())?;
    ///     assert_eq!(res, &["baz", "bar", "foo"]);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn method_name(self) -> Option<RString> {
        unsafe {
            let val = rb_profile_frame_method_name(self.0.as_rb_value());
            (!Value::new(val).is_nil()).then_some(RString::from_rb_value_unchecked(val))
        }
    }

    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, RArray, Ruby, Value, debug::FrameBuf, eval, function, prelude::*};
    ///
    /// fn baz(ruby: &Ruby) -> RArray {
    ///     let mut buf = FrameBuf::<64>::new();
    ///     ruby.profile_frames(&mut buf);
    ///     ruby.ary_from_iter(buf.iter().map(|(frame, _line)| frame.qualified_method_name()))
    /// }
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     ruby.define_global_function("baz", function!(baz, 0));
    ///     let _: Value = eval!(
    ///         "def foo = bar
    ///          def bar = baz"
    ///     )?;
    ///     let res: Vec<String> = ruby.class_object().funcall("foo", ())?;
    ///     assert_eq!(res, &["Kernel#baz", "Object#bar", "Object#foo"]);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn qualified_method_name(self) -> Option<RString> {
        unsafe {
            let val = rb_profile_frame_qualified_method_name(self.0.as_rb_value());
            (!Value::new(val).is_nil()).then_some(RString::from_rb_value_unchecked(val))
        }
    }
}

impl PartialEq for Frame {
    fn eq(&self, other: &Self) -> bool {
        self.0.as_rb_value() == other.0.as_rb_value()
    }
}

impl Eq for Frame {}

impl gc::private::Mark for Frame {
    fn raw(self) -> VALUE {
        self.0.as_rb_value()
    }
}
impl gc::Mark for Frame {}

unsafe fn profile_frames_impl<const N: usize>(
    start: usize,
    frames: &mut [Frame; N],
    lines: Option<&mut [i32; N]>,
) -> usize {
    unsafe {
        rb_profile_frames(
            start as c_int,
            N as c_int,
            frames as *mut _ as *mut VALUE,
            lines.map(|v| v as *mut c_int).unwrap_or(null_mut()),
        ) as usize
    }
}

/// A buffer for storing [`Frame`]s.
///
/// See [`Ruby::profile_frames`].
pub struct FrameBuf<const N: usize> {
    frames: [Frame; N],
    lines: [i32; N],
    filled: usize,
}

impl<const N: usize> FrameBuf<N> {
    pub const fn new() -> Self {
        Self {
            frames: [Frame::EMPTY; N],
            lines: [0; N],
            filled: 0,
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = (Frame, usize)> {
        self.frames
            .iter()
            .take(self.filled)
            .copied()
            .zip(self.lines.iter().map(|v| *v as usize))
    }

    pub fn len(&self) -> usize {
        self.filled
    }

    pub fn clear(&mut self) {
        self.filled = 0;
    }

    pub fn is_empty(&self) -> bool {
        self.filled == 0
    }
}

impl<const N: usize> Default for FrameBuf<N> {
    fn default() -> Self {
        Self::new()
    }
}
