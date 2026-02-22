//! Types and functions for working with Ruby's debugging tools.
//!
//! See also [`Ruby`](Ruby#debug) for more debugging related methods.

use std::{
    ffi::{c_int, c_long, c_void},
    fmt,
    marker::PhantomData,
    ptr::null_mut,
    slice,
};

use rb_sys::{
    RUBY_EVENT_ALL, RUBY_EVENT_B_CALL, RUBY_EVENT_B_RETURN, RUBY_EVENT_C_CALL, RUBY_EVENT_C_RETURN,
    RUBY_EVENT_CALL, RUBY_EVENT_CLASS, RUBY_EVENT_END, RUBY_EVENT_FIBER_SWITCH, RUBY_EVENT_LINE,
    RUBY_EVENT_NONE, RUBY_EVENT_RAISE, RUBY_EVENT_RETURN, RUBY_EVENT_SCRIPT_COMPILED,
    RUBY_EVENT_THREAD_BEGIN, RUBY_EVENT_THREAD_END, RUBY_EVENT_TRACEPOINT_ALL, VALUE,
    rb_data_typed_object_wrap, rb_debug_inspector_backtrace_locations,
    rb_debug_inspector_current_depth, rb_debug_inspector_frame_binding_get,
    rb_debug_inspector_frame_class_get, rb_debug_inspector_frame_depth,
    rb_debug_inspector_frame_iseq_get, rb_debug_inspector_frame_self_get, rb_debug_inspector_open,
    rb_debug_inspector_t, rb_event_flag_t, rb_profile_frame_absolute_path,
    rb_profile_frame_base_label, rb_profile_frame_classpath, rb_profile_frame_first_lineno,
    rb_profile_frame_full_label, rb_profile_frame_label, rb_profile_frame_method_name,
    rb_profile_frame_path, rb_profile_frame_qualified_method_name,
    rb_profile_frame_singleton_method_p, rb_profile_frames, rb_trace_arg_t, rb_tracearg_event,
    rb_tracearg_event_flag, rb_tracearg_from_tracepoint, rb_tracearg_method_id,
    rb_tracepoint_disable, rb_tracepoint_enable, rb_tracepoint_enabled_p, rb_tracepoint_new,
    ruby_special_consts,
};
#[cfg(ruby_gte_3_3)]
use rb_sys::{RUBY_EVENT_RESCUE, rb_profile_thread_frames};

use crate::{
    api::Ruby,
    class::RClass,
    error::{Error, protect},
    gc,
    integer::Integer,
    into_value::IntoValue,
    method::{BlockReturn, DebugInspectorOpen, InitReturn, TracePointNew},
    module::Module,
    object::Object,
    r_array::RArray,
    r_string::RString,
    thread::Thread,
    try_convert::TryConvert,
    typed_data::{DataType, DataTypeBuilder, DataTypeFunctions},
    value::{
        Fixnum, NonZeroValue, ReprValue, StaticSymbol, Value,
        private::{self, ReprValue as _},
    },
};

/// # Debug
///
/// Ruby's debugging tools.
impl Ruby {
    /// Fill `buf` with backtrace [`Frame`]s.
    ///
    /// See also [`Thread::profile_frames`].
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
    /// See also [`Thread::profile_frames_starting`].
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

    /// Open, execute, and clean up a debug session.
    ///
    /// Returns the value returned by `func` converted to a [`Value`].
    pub fn debug_inspector_open<F, R>(&self, func: F) -> Result<Value, Error>
    where
        F: FnOnce(DebugInspector) -> R,
        R: BlockReturn,
    {
        unsafe extern "C" fn call<F, R>(dc: *const rb_debug_inspector_t, data: *mut c_void) -> VALUE
        where
            F: FnOnce(DebugInspector) -> R,
            R: BlockReturn,
        {
            unsafe {
                let closure = (*(data as *mut Option<F>)).take().unwrap();
                let ruby = Ruby::get_unchecked();
                closure
                    .call_handle_error(&ruby, DebugInspector::from_ptr_with_lifetime(dc, &ruby))
                    .as_rb_value()
            }
        }

        let call_func = call::<F, R>
            as unsafe extern "C" fn(dc: *const rb_debug_inspector_t, data: *mut c_void) -> VALUE;

        unsafe {
            protect(|| {
                Value::new(rb_debug_inspector_open(
                    Some(call_func),
                    &mut Some(func) as *mut _ as *mut c_void,
                ))
            })
        }
    }

    /// Return the current frame depth.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby, Value, eval, function, prelude::*};
    ///
    /// fn depth(ruby: &Ruby) -> usize {
    ///     ruby.debug_inspector_current_depth()
    /// }
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     ruby.define_global_function("depth", function!(depth, 0));
    ///
    ///     let _: Value = eval!(
    ///         "def foo = bar
    ///          def bar = baz
    ///          def baz = depth"
    ///     )?;
    ///     let depth: usize = ruby.class_object().funcall("foo", ())?;
    ///
    ///     assert_eq!(depth, 5);
    ///
    ///     let depth: usize = ruby.class_object().funcall("depth", ())?;
    ///     assert_eq!(depth, 2);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn debug_inspector_current_depth(&self) -> usize {
        unsafe { Fixnum::from_rb_value_unchecked(rb_debug_inspector_current_depth()) }
            .to_usize()
            .unwrap()
    }

    pub fn tracepoint_new<F, R>(
        &self,
        thread: Option<Thread>,
        events: Events,
        func: F,
    ) -> TracePoint
    where
        F: 'static + Send + FnMut(TracePoint) -> R,
        R: InitReturn,
    {
        unsafe extern "C" fn call<F, R>(tpval: VALUE, data: *mut c_void)
        where
            F: FnMut(TracePoint) -> R,
            R: InitReturn,
        {
            unsafe {
                let closure = &mut *(data as *mut F);
                closure.call_handle_error(TracePoint::from_rb_value_unchecked(tpval))
            }
        }

        let (closure, keepalive) = wrap_closure(func);
        let call_func = call::<F, R> as unsafe extern "C" fn(VALUE, *mut c_void);

        let tp = unsafe {
            TracePoint::from_rb_value_unchecked(rb_tracepoint_new(
                thread
                    .map(|t| t.as_value())
                    .unwrap_or(self.qnil().as_value())
                    .as_rb_value(),
                events.0,
                Some(call_func),
                closure as *mut c_void,
            ))
        };
        // ivar without @ prefix is invisible from Ruby
        tp.ivar_set("__rust_closure", keepalive).unwrap();
        tp
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

    /// Return the file path of the frame.
    ///
    /// The path may be a relative path. Returns `None` if there isn't a path
    /// available, e.g. the method is implemented in C/Rust.
    ///
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
    /// #   #[cfg(ruby_gte_3_3)]
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

    /// Return the expanded file path of the frame.
    ///
    /// Returns `"<cfunc>"` for C/Rust methods.
    /// Returns `None` if there isn't a path available, e.g. the method was
    /// defined via `eval`.
    ///
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

    /// Return the label for the frame.
    ///
    /// This is usually the method name, but can be a string like `"<main>"`
    /// for code running at the global toplevel. Blocks will get
    /// `"block in method_name"`.
    ///
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
    ///     assert_eq!(
    ///         res,
    ///         &[None, Some(String::from("bar")), Some(String::from("foo"))]
    ///     );
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

    /// Return the unqualified label for the frame.
    ///
    /// This is usually the method name, but can be a string like `"<main>"`
    /// for code running at the global toplevel. Blocks will not be qualified,
    /// and so return just the method name.
    ///
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
    ///     assert_eq!(
    ///         res,
    ///         &[None, Some(String::from("bar")), Some(String::from("foo"))]
    ///     );
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

    /// Return the full label for the frame.
    ///
    /// This is usually the method name, but can be a string like `"<main>"`
    /// for code running at the global toplevel. Methods will be fully
    /// qualified with the class name.
    ///
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

    /// Return the line number of the first line of the method for the frame.
    ///
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

    /// Return the class path of the method for the frame.
    ///
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

    /// Return if the method for the frame is a singleton method.
    ///
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

    /// Return the name of the method for the frame.
    ///
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

    /// Return the fully qualified name of the method for the frame.
    ///
    /// The method name will be qualified with the class.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, RArray, Ruby, Value, debug::FrameBuf, eval, function, prelude::*};
    ///
    /// fn baz(ruby: &Ruby) -> RArray {
    ///     let mut buf = FrameBuf::<64>::new();
    ///     ruby.profile_frames(&mut buf);
    ///     ruby.ary_from_iter(
    ///         buf.iter()
    ///             .map(|(frame, _line)| frame.qualified_method_name()),
    ///     )
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
    fn raw_with(self, _ruby: &Ruby) -> VALUE {
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

#[cfg(ruby_gte_3_3)]
pub(crate) unsafe fn profile_thread_frames_impl<const N: usize>(
    thread: Thread,
    start: usize,
    frames: &mut [Frame; N],
    lines: Option<&mut [i32; N]>,
) -> usize {
    unsafe {
        rb_profile_thread_frames(
            thread.as_rb_value(),
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
    pub(crate) frames: [Frame; N],
    pub(crate) lines: [i32; N],
    pub(crate) filled: usize,
}

impl<const N: usize> FrameBuf<N> {
    /// Create a new `FrameBuf<N>`
    ///
    /// # Examples
    ///
    /// ```
    /// use std::cell::RefCell;
    ///
    /// use magnus::debug::FrameBuf;
    ///
    /// thread_local! {
    ///     static FRAMES: RefCell<FrameBuf<1024>> = const { RefCell::new(FrameBuf::new()) };
    /// }
    /// ```
    pub const fn new() -> Self {
        Self {
            frames: [Frame::EMPTY; N],
            lines: [0; N],
            filled: 0,
        }
    }

    /// Return an [`Iterator`] over `self`.
    pub fn iter(&self) -> impl Iterator<Item = (Frame, usize)> {
        self.frames
            .iter()
            .take(self.filled)
            .copied()
            .zip(self.lines.iter().map(|v| *v as usize))
    }

    /// Return the number of frames in the buffer.
    pub fn len(&self) -> usize {
        self.filled
    }

    /// Clear the buffer.
    ///
    /// Note this method does no change the allocated capacity of the buffer.
    pub fn clear(&mut self) {
        self.filled = 0;
    }

    /// Return `true` if the buffer contains no frames.
    pub fn is_empty(&self) -> bool {
        self.filled == 0
    }
}

impl<const N: usize> Default for FrameBuf<N> {
    fn default() -> Self {
        Self::new()
    }
}

/// A pointer to a Ruby Debug Inspector returned from
/// [`Ruby::debug_inspector_open`].
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct DebugInspector<'a> {
    ptr: *const rb_debug_inspector_t,
    lifetime: PhantomData<&'a ()>,
}

impl<'a> DebugInspector<'a> {
    fn from_ptr_with_lifetime<T>(ptr: *const rb_debug_inspector_t, _: &'a T) -> Self {
        Self {
            ptr,
            lifetime: PhantomData,
        }
    }

    /// Return a backtrace from the point the `DebugInspector` was opened.
    ///
    /// Returns a Ruby array of `Thread::Backtrace::Location` objects.
    pub fn backtrace_locations(self) -> RArray {
        unsafe { RArray::from_rb_value_unchecked(rb_debug_inspector_backtrace_locations(self.ptr)) }
    }

    /// Get Ruby's `self` for the frame at `index`.
    pub fn frame_self_get(self, index: usize) -> Result<Value, Error> {
        protect(|| unsafe {
            Value::new(rb_debug_inspector_frame_self_get(self.ptr, index as c_long))
        })
    }

    /// Get the Ruby class for the frame at `index`.
    pub fn frame_class_get(self, index: usize) -> Result<RClass, Error> {
        protect(|| unsafe {
            RClass::from_rb_value_unchecked(rb_debug_inspector_frame_class_get(
                self.ptr,
                index as c_long,
            ))
        })
    }

    /// Get the Ruby `Binding` object for the frame at `index`.
    pub fn frame_binding_get(self, index: usize) -> Result<Value, Error> {
        protect(|| unsafe {
            Value::new(rb_debug_inspector_frame_binding_get(
                self.ptr,
                index as c_long,
            ))
        })
    }

    /// Get the `RubyVM::InstructionSequence` for the frame at `index`.
    pub fn frame_iseq_get(self, index: usize) -> Result<Option<Value>, Error> {
        protect(|| unsafe {
            Value::new(rb_debug_inspector_frame_iseq_get(self.ptr, index as c_long))
        })
        .map(|v| (!v.is_nil()).then_some(v))
    }

    /// Return the depth of the frame at `index`.
    ///
    /// The depth is not same as the frame index as Ruby's debug inspector
    /// skips some special frames but the depth counts all frames.
    pub fn frame_depth(self, index: usize) -> Result<usize, Error> {
        protect(|| unsafe {
            Integer::from_rb_value_unchecked(rb_debug_inspector_frame_depth(
                self.ptr,
                index as c_long,
            ))
        })
        .and_then(|i| i.to_usize())
    }
}

/// Event types for use with [`Ruby::tracepoint_new`].
#[derive(Clone, Copy, Default)]
#[repr(transparent)]
pub struct Events(rb_event_flag_t);

impl Events {
    /// Create a new `Events` with no flags set.
    pub const fn new() -> Self {
        Self(RUBY_EVENT_NONE)
    }

    /// Set the `RUBY_EVENT_LINE` flag
    pub const fn line(self) -> Self {
        Self(self.0 | RUBY_EVENT_LINE)
    }

    /// Return if `self` contains the `RUBY_EVENT_LINE` flag
    pub const fn is_line(self) -> bool {
        self.0 & RUBY_EVENT_LINE != 0
    }

    /// Set the `RUBY_EVENT_CLASS` flag
    pub const fn class(self) -> Self {
        Self(self.0 | RUBY_EVENT_CLASS)
    }

    /// Return if `self` contains the `RUBY_EVENT_CLASS` flag
    pub const fn is_class(self) -> bool {
        self.0 & RUBY_EVENT_CLASS != 0
    }

    /// Set the `RUBY_EVENT_END` flag
    pub const fn end(self) -> Self {
        Self(self.0 | RUBY_EVENT_END)
    }

    /// Return if `self` contains the `RUBY_EVENT_END` flag
    pub const fn is_end(self) -> bool {
        self.0 & RUBY_EVENT_END != 0
    }

    /// Set the `RUBY_EVENT_CALL` flag
    pub const fn call(self) -> Self {
        Self(self.0 | RUBY_EVENT_CALL)
    }

    /// Return if `self` contains the `RUBY_EVENT_CALL` flag
    pub const fn is_call(self) -> bool {
        self.0 & RUBY_EVENT_CALL != 0
    }

    /// Set the `RUBY_EVENT_RETURN` flag
    pub const fn event_return(self) -> Self {
        Self(self.0 | RUBY_EVENT_RETURN)
    }

    /// Return if `self` contains the `RUBY_EVENT_RETURN` flag
    pub const fn is_return(self) -> bool {
        self.0 & RUBY_EVENT_RETURN != 0
    }

    /// Set the `RUBY_EVENT_C_CALL` flag
    pub const fn c_call(self) -> Self {
        Self(self.0 | RUBY_EVENT_C_CALL)
    }

    /// Return if `self` contains the `RUBY_EVENT_C_CALL` flag
    pub const fn is_c_call(self) -> bool {
        self.0 & RUBY_EVENT_C_CALL != 0
    }

    /// Set the `RUBY_EVENT_C_RETURN` flag
    pub const fn c_return(self) -> Self {
        Self(self.0 | RUBY_EVENT_C_RETURN)
    }

    /// Return if `self` contains the `RUBY_EVENT_C_RETURN` flag
    pub const fn is_c_return(self) -> bool {
        self.0 & RUBY_EVENT_C_RETURN != 0
    }

    /// Set the `RUBY_EVENT_RAISE` flag
    pub const fn raise(self) -> Self {
        Self(self.0 | RUBY_EVENT_RAISE)
    }

    /// Return if `self` contains the `RUBY_EVENT_RAISE` flag
    pub const fn is_raise(self) -> bool {
        self.0 & RUBY_EVENT_RAISE != 0
    }

    /// Set the `RUBY_EVENT_ALL` flag
    ///
    /// This is not all events, but the subset originally usable with the
    /// `set_trace_func` api. See [`tracepoint_all`](Events::tracepoint_all).
    pub const fn all(self) -> Self {
        Self(self.0 | RUBY_EVENT_ALL)
    }

    /// Return if `self` contains the `RUBY_EVENT_ALL` flag
    ///
    /// This is not all events, but the subset originally usable with the
    /// `set_trace_func` api. See [`is_tracepoint_all`](Events::is_tracepoint_all).
    pub const fn is_all(self) -> bool {
        self.0 & RUBY_EVENT_ALL != 0
    }

    /// Set the `RUBY_EVENT_B_CALL` flag
    pub const fn b_call(self) -> Self {
        Self(self.0 | RUBY_EVENT_B_CALL)
    }

    /// Return if `self` contains the `RUBY_EVENT_B_CALL` flag
    pub const fn is_b_call(self) -> bool {
        self.0 & RUBY_EVENT_B_CALL != 0
    }

    /// Set the `RUBY_EVENT_B_RETURN` flag
    pub const fn b_return(self) -> Self {
        Self(self.0 | RUBY_EVENT_B_RETURN)
    }

    /// Return if `self` contains the `RUBY_EVENT_B_RETURN` flag
    pub const fn is_b_return(self) -> bool {
        self.0 & RUBY_EVENT_B_RETURN != 0
    }

    /// Set the `RUBY_EVENT_THREAD_BEGIN` flag
    pub const fn thread_begin(self) -> Self {
        Self(self.0 | RUBY_EVENT_THREAD_BEGIN)
    }

    /// Return if `self` contains the `RUBY_EVENT_THREAD_BEGIN` flag
    pub const fn is_thread_begin(self) -> bool {
        self.0 & RUBY_EVENT_THREAD_BEGIN != 0
    }

    /// Set the `RUBY_EVENT_THREAD_END` flag
    pub const fn thread_end(self) -> Self {
        Self(self.0 | RUBY_EVENT_THREAD_END)
    }

    /// Return if `self` contains the `RUBY_EVENT_THREAD_END` flag
    pub const fn is_thread_end(self) -> bool {
        self.0 & RUBY_EVENT_THREAD_END != 0
    }

    /// Set the `RUBY_EVENT_FIBER_SWITCH` flag
    pub const fn fiber_switch(self) -> Self {
        Self(self.0 | RUBY_EVENT_FIBER_SWITCH)
    }

    /// Return if `self` contains the `RUBY_EVENT_FIBER_SWITCH` flag
    pub const fn is_fiber_switch(self) -> bool {
        self.0 & RUBY_EVENT_FIBER_SWITCH != 0
    }

    /// Set the `RUBY_EVENT_SCRIPT_COMPILED` flag
    pub const fn script_compiled(self) -> Self {
        Self(self.0 | RUBY_EVENT_SCRIPT_COMPILED)
    }

    /// Return if `self` contains the `RUBY_EVENT_SCRIPT_COMPILED` flag
    pub const fn is_script_compiled(self) -> bool {
        self.0 & RUBY_EVENT_SCRIPT_COMPILED != 0
    }

    /// Set the `RUBY_EVENT_RESCUE` flag
    #[cfg(ruby_gte_3_3)]
    pub const fn rescue(self) -> Self {
        Self(self.0 | RUBY_EVENT_RESCUE)
    }

    /// Return if `self` contains the `RUBY_EVENT_RESCUE` flag
    #[cfg(ruby_gte_3_3)]
    pub const fn is_rescue(self) -> bool {
        self.0 & RUBY_EVENT_RESCUE != 0
    }

    /// Set the `RUBY_EVENT_TRACEPOINT_ALL` flag
    pub const fn tracepoint_all(self) -> Self {
        Self(self.0 | RUBY_EVENT_TRACEPOINT_ALL)
    }

    /// Return if `self` contains the `RUBY_EVENT_TRACEPOINT_ALL` flag
    pub const fn is_tracepoint_all(self) -> bool {
        self.0 & RUBY_EVENT_TRACEPOINT_ALL != 0
    }
}

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct TracePoint(NonZeroValue);

impl TracePoint {
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            val.is_kind_of(
                Ruby::get_with(val)
                    .class_object()
                    .const_get::<_, RClass>("TracePoint")
                    .unwrap(),
            )
            .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        unsafe { Self(NonZeroValue::new_unchecked(Value::new(val))) }
    }

    pub fn enable(self) -> Result<(), Error> {
        unsafe {
            protect(|| Value::new(rb_tracepoint_enable(self.as_rb_value())))?;
        }
        Ok(())
    }

    pub fn disable(self) {
        unsafe {
            rb_tracepoint_disable(self.as_rb_value());
        }
    }

    pub fn is_enabled(self) -> bool {
        unsafe { Value::new(rb_tracepoint_enabled_p(self.as_rb_value())).to_bool() }
    }

    pub fn tracearg(&self) -> Result<TraceArg, Error> {
        let mut tracearg = TraceArg::from_ptr_with_lifetime(std::ptr::null_mut(), self);
        unsafe {
            protect(|| {
                tracearg = TraceArg::from_ptr_with_lifetime(
                    rb_tracearg_from_tracepoint(self.as_rb_value()),
                    self,
                );
                Ruby::get_with(*self).qnil().as_value()
            })?;
        }
        Ok(tracearg)
    }
}

impl fmt::Display for TracePoint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for TracePoint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl IntoValue for TracePoint {
    #[inline]
    fn into_value_with(self, _: &Ruby) -> Value {
        self.0.get()
    }
}

impl Object for TracePoint {}

unsafe impl private::ReprValue for TracePoint {}

impl ReprValue for TracePoint {}

impl TryConvert for TracePoint {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Self::from_value(val).ok_or_else(|| {
            Error::new(
                Ruby::get_with(val).exception_type_error(),
                format!("no implicit conversion of {} into TracePoint", unsafe {
                    val.classname()
                },),
            )
        })
    }
}

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct TraceArg<'a> {
    ptr: *mut rb_trace_arg_t,
    lifetime: PhantomData<&'a ()>,
}

impl<'a> TraceArg<'a> {
    fn from_ptr_with_lifetime<T>(ptr: *mut rb_trace_arg_t, _: &'a T) -> Self {
        Self {
            ptr,
            lifetime: PhantomData,
        }
    }

    pub fn event_flag(self) -> Events {
        unsafe { Events(rb_tracearg_event_flag(self.ptr)) }
    }

    pub fn event(self) -> StaticSymbol {
        unsafe { StaticSymbol::from_rb_value_unchecked(rb_tracearg_event(self.ptr)) }
    }

    // rb_tracearg_lineno

    // rb_tracearg_path

    // rb_tracearg_parameters

    pub fn method_id(self) -> Option<StaticSymbol> {
        unsafe {
            let val = rb_tracearg_method_id(self.ptr);
            (!Value::new(val).is_nil()).then_some(StaticSymbol::from_rb_value_unchecked(val))
        }
    }

    // rb_tracearg_callee_id

    // rb_tracearg_defined_class

    // rb_tracearg_binding

    // rb_tracearg_self

    // rb_tracearg_return_value

    // rb_tracearg_raised_exception

    // rb_tracearg_eval_script

    // rb_tracearg_instruction_sequence

    // rb_tracearg_object
}

/// Wrap a closure in a Ruby object with no class.
///
/// This effectively makes the closure's lifetime managed by Ruby. It will be
/// dropped when the returned `Value` is garbage collected.
fn wrap_closure<F, R>(func: F) -> (*mut F, Value)
where
    F: FnMut(TracePoint) -> R,
    R: InitReturn,
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

    let data_type = DataTypeBuilder::<Closure<F>>::new(c"rust closure")
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
