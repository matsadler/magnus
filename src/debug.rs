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
    pub fn profile_frames<const N: usize>(&self, buf: &mut FrameBuf<N>) {
        unsafe {
            buf.filled = profile_frames_impl(0, &mut buf.frames, Some(&mut buf.lines));
        }
    }

    #[cfg(any(ruby_gte_3_4, docsrs))]
    #[cfg_attr(docsrs, doc(cfg(ruby_gte_3_4)))]
    pub fn profile_frames_starting<const N: usize>(&self, buf: &mut FrameBuf<N>, start: usize) {
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

    pub fn path(self) -> Option<RString> {
        unsafe {
            let val = rb_profile_frame_path(self.0.as_rb_value());
            (!Value::new(val).is_nil()).then_some(RString::from_rb_value_unchecked(val))
        }
    }

    pub fn absolute_path(self) -> Option<RString> {
        unsafe {
            let val = rb_profile_frame_absolute_path(self.0.as_rb_value());
            (!Value::new(val).is_nil()).then_some(RString::from_rb_value_unchecked(val))
        }
    }

    pub fn label(self) -> Option<RString> {
        unsafe {
            let val = rb_profile_frame_label(self.0.as_rb_value());
            (!Value::new(val).is_nil()).then_some(RString::from_rb_value_unchecked(val))
        }
    }

    pub fn base_label(self) -> Option<RString> {
        unsafe {
            let val = rb_profile_frame_base_label(self.0.as_rb_value());
            (!Value::new(val).is_nil()).then_some(RString::from_rb_value_unchecked(val))
        }
    }

    pub fn full_label(self) -> Option<RString> {
        unsafe {
            let val = rb_profile_frame_full_label(self.0.as_rb_value());
            (!Value::new(val).is_nil()).then_some(RString::from_rb_value_unchecked(val))
        }
    }

    pub fn first_lineno(self) -> Option<usize> {
        unsafe {
            let val = rb_profile_frame_first_lineno(self.0.as_rb_value());
            (!Value::new(val).is_nil())
                .then(|| Integer::from_rb_value_unchecked(val).to_usize().unwrap())
        }
    }

    pub fn classpath(self) -> Option<RString> {
        unsafe {
            let val = rb_profile_frame_classpath(self.0.as_rb_value());
            (!Value::new(val).is_nil()).then_some(RString::from_rb_value_unchecked(val))
        }
    }

    pub fn is_singleton_method(self) -> bool {
        unsafe { Value::new(rb_profile_frame_singleton_method_p(self.0.as_rb_value())).to_bool() }
    }

    pub fn method_name(self) -> Option<RString> {
        unsafe {
            let val = rb_profile_frame_method_name(self.0.as_rb_value());
            (!Value::new(val).is_nil()).then_some(RString::from_rb_value_unchecked(val))
        }
    }

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
    pub fn new() -> Self {
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
