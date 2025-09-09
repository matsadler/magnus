use std::{ffi::c_int, ptr::null_mut};

use rb_sys::{
    VALUE, rb_profile_frame_absolute_path, rb_profile_frame_base_label, rb_profile_frame_classpath,
    rb_profile_frame_first_lineno, rb_profile_frame_full_label, rb_profile_frame_label,
    rb_profile_frame_method_name, rb_profile_frame_path, rb_profile_frame_qualified_method_name,
    rb_profile_frame_singleton_method_p, rb_profile_frames, ruby_special_consts,
};

use crate::{
    Ruby,
    integer::Integer,
    r_string::RString,
    value::{ReprValue, Value},
};

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Frame(Value);

impl Ruby {
    pub fn profile_frames<const N: usize>(
        &self,
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
}

impl Frame {
    pub const EMPTY: Frame = Frame(Value::new(ruby_special_consts::RUBY_Qnil as VALUE));

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

    pub fn is_singleton_method(self) -> Option<bool> {
        unsafe {
            let val = rb_profile_frame_singleton_method_p(self.0.as_rb_value());
            (!Value::new(val).is_nil()).then_some(Value::new(val).to_bool())
        }
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
