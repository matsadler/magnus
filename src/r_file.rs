use std::{fmt, ptr::NonNull};

use rb_sys::ruby_value_type;

use crate::{
    error::Error,
    into_value::IntoValue,
    object::Object,
    try_convert::TryConvert,
    value::{
        private::{self, ReprValue as _},
        NonZeroValue, ReprValue, Value,
    },
    Ruby,
};

/// A Value pointer to a RFile struct, Ruby's internal representation of IO.
///
/// See the [`ReprValue`] and [`Object`] traits for additional methods
/// available on this type.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RFile(NonZeroValue);

impl RFile {
    /// Return `Some(RFile)` if `val` is a `RFile`, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RFile};
    /// # let ruby = unsafe { magnus::embed::init() };
    ///
    /// assert!(RFile::from_value(eval("STDOUT").unwrap()).is_some());
    /// # #[cfg(not(windows))]
    /// # {
    /// assert!(RFile::from_value(eval(r#"File.open("/tmp/example.txt", "w+")"#).unwrap()).is_some());
    /// # ruby.require("socket").unwrap();
    /// assert!(RFile::from_value(eval("UNIXSocket.pair.first").unwrap()).is_some());
    /// # }
    /// assert!(RFile::from_value(eval("nil").unwrap()).is_none());
    /// ```
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            (val.rb_type() == ruby_value_type::RUBY_T_FILE)
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    fn as_internal(self) -> NonNull<rb_sys::RFile> {
        // safe as inner value is NonZero
        unsafe { NonNull::new_unchecked(self.0.get().as_rb_value() as *mut _) }
    }
}

impl fmt::Display for RFile {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for RFile {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl IntoValue for RFile {
    #[inline]
    fn into_value_with(self, _: &Ruby) -> Value {
        self.0.get()
    }
}

impl Object for RFile {}

unsafe impl private::ReprValue for RFile {}

impl ReprValue for RFile {}

impl TryConvert for RFile {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Self::from_value(val).ok_or_else(|| {
            Error::new(
                Ruby::get_with(val).exception_type_error(),
                format!("no implicit conversion of {} into File", unsafe {
                    val.classname()
                },),
            )
        })
    }
}

#[cfg(not(unix))]
pub mod fd {
    use std::os::raw::c_int;

    pub type RawFd = c_int;

    pub trait AsRawFd {
        fn as_raw_fd(&self) -> RawFd;
    }
}

#[cfg(unix)]
pub use std::os::unix::io as fd;

impl fd::AsRawFd for RFile {
    fn as_raw_fd(&self) -> fd::RawFd {
        unsafe { (*self.as_internal().as_ref().fptr).fd }
    }
}
