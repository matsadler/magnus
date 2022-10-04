//!

use {
    crate::{
        class::io,
        error::{protect, Error},
        exception::{io_error, type_error},
        object::Object,
        r_time::AsRawTime,
        ruby_sys::{
            rb_fd_init, rb_fd_set, rb_fd_term, rb_fdset_t, rb_io_ascii8bit_binmode, rb_io_bufwrite,
            rb_io_close, rb_io_eof, rb_io_fdopen, rb_io_flush, rb_io_getbyte, rb_io_gets, rb_pipe,
            rb_reserved_fd_p, rb_string_value_cstr, rb_sys_fail, rb_thread_fd_close,
            rb_thread_fd_writable, rb_thread_wait_fd,
        },
        try_convert::TryConvert,
        value::{private, NonZeroValue, ReprValue, Value},
        RString,
    },
    std::{
        convert::TryFrom,
        fmt::{Debug, Display, Error as FError, Formatter},
        ops::Deref,
        os::raw::{c_int, c_ulonglong, c_void},
        ptr::{null, null_mut},
        time::Duration,
    },
};

#[cfg(ruby_gt_3_0)]
use crate::ruby_sys::{rb_io_descriptor, rb_thread_fd_select};

#[cfg(unix)]
use {
    crate::ruby_sys::{rb_fd_clr, rb_fd_dup, rb_fd_isset, rb_fd_zero},
    std::os::unix::io::{AsRawFd, RawFd},
};

#[cfg(windows)]
use crate::ruby_sys::{rb_w32_fd_dup, rb_w32_fdclr, rb_w32_fdisset};

#[cfg(unix)]
#[allow(missing_docs)]
pub type RawRubyFd = RawFd;

#[cfg(windows)]
#[allow(missing_docs)]
pub type RawRubyFd = c_int;

/// A Value pointer to a Rio struct, Ruby's internal representation of IO.
#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct Rio(NonZeroValue);

impl Deref for Rio {
    type Target = Value;
    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
    }
}

impl TryConvert for Rio {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Self::from_value(val).ok_or_else(|| {
            Error::new(
                type_error(),
                format!("no implicit conversion of {} into IO", unsafe {
                    val.classname()
                }),
            )
        })
    }
}

impl From<Rio> for Value {
    fn from(f: Rio) -> Self {
        *f
    }
}

unsafe impl private::ReprValue for Rio {
    fn to_value(self) -> Value {
        *self
    }

    unsafe fn from_value_unchecked(val: Value) -> Self {
        Self(NonZeroValue::new_unchecked(val))
    }
}

impl ReprValue for Rio {}

impl Object for Rio {}

impl Display for Rio {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FError> {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl Debug for Rio {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FError> {
        write!(f, "{}", self.inspect())
    }
}

impl Rio {
    /// Return `Some(RIO)` if `val` is a `::IO`, `None` otherwise.
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        if val.is_kind_of(io()) {
            Some(Self(unsafe { NonZeroValue::new_unchecked(val) }))
        } else {
            None
        }
    }
}

impl Rio {
    /// Create `Rio` via raw FD
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{r_io::Rio};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let stdin = Rio::from_raw(0, Default::default(), Some("/dev/stdin")).unwrap();
    /// stdin.close();
    /// ```
    pub fn from_raw<P>(fd: RawRubyFd, flags: c_int, path: Option<P>) -> Result<Self, Error>
    where
        P: Into<RString>,
    {
        let val = protect(|| {
            Value::new(unsafe {
                let c_path = path.map_or_else(null, |p| {
                    let mut val = p.into().as_rb_value();
                    rb_string_value_cstr(&mut val as *mut _)
                });
                rb_io_fdopen(fd, flags, c_path)
            })
        })?;
        Ok(Self(unsafe { NonZeroValue::new_unchecked(val) }))
    }

    /// Close `Rio`
    pub fn close(&self) {
        let v = Value::new(unsafe { rb_io_close(self.as_rb_value()) });
        debug_assert!(v.is_nil());
    }

    #[cfg(ruby_gt_3_0)]
    /// Is the FD associated reserved by the Ruby interpreter
    pub fn is_reserved(&self) -> bool {
        unsafe { rb_reserved_fd_p(self.descriptor()) != 0 }
    }

    /// Return `true` if `Rio` is at `EOF`, else `false`
    pub fn is_eof(&self) -> Result<bool, Error> {
        let eof = protect(|| Value::new(unsafe { rb_io_eof(self.as_rb_value()) }))?.to_bool();
        Ok(eof)
    }

    /// Flush `Rio`
    pub fn flush(&self) -> Result<(), Error> {
        protect(|| Value::new(unsafe { rb_io_flush(self.as_rb_value()) }))?;
        Ok(())
    }

    /// Remove all encoding & textmode
    /// `io.binmode`
    pub fn binmode(&self) -> Result<(), Error> {
        protect(|| Value::new(unsafe { rb_io_ascii8bit_binmode(self.as_rb_value()) }))?;
        Ok(())
    }

    /// Read next byte
    pub fn get_byte(&self) -> Result<u8, Error> {
        protect(|| Value::new(unsafe { rb_io_getbyte(self.as_rb_value()) }))?.try_convert()
    }

    /// Read until next '\n' or EOF
    pub fn read_line(&self) -> Result<Option<RString>, Error> {
        protect(|| Value::new(unsafe { rb_io_gets(self.as_rb_value()) }))?.try_convert()
    }

    /// Return bytes written, this means partial writes is possible.
    pub fn write<B>(&self, buf: B) -> Result<usize, Error>
    where
        B: AsRef<[u8]>,
    {
        let buf = buf.as_ref();
        let mut size = -1;
        protect(|| {
            unsafe {
                size = rb_io_bufwrite(
                    self.as_rb_value(),
                    buf as *const _ as *const c_void,
                    buf.len() as c_ulonglong,
                )
            };
            Value::default()
        })?;
        debug_assert!(size >= 0);
        Ok(size as usize)
    }
}

impl Rio {
    /// ::IO.pipe
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{r_io::Rio};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let (r, w) = Rio::pipe().unwrap();
    /// r.close();
    /// w.close();
    /// ```
    pub fn pipe() -> Result<(Self, Self), Error> {
        let pipes = [Default::default(), Default::default()];
        let code = unsafe { rb_pipe(pipes.as_ptr() as *mut _) };
        if code != 0 {
            Err(Error::last_os_error())
        } else {
            let (r, w) = (pipes[0], pipes[1]);
            debug_assert!(r != 0 && w != 0);
            debug_assert!(unsafe { rb_reserved_fd_p(r) == 0 && rb_reserved_fd_p(w) == 0 });
            let read = Rio::from_raw(r, Default::default(), Option::<&str>::None)?;
            let write = Rio::from_raw(w, Default::default(), Option::<&str>::None)?;
            Ok((read, write))
        }
    }
}

#[cfg(ruby_gt_3_0)]
impl Rio {
    /// `io.fileno`
    pub fn descriptor(&self) -> RawRubyFd {
        unsafe { rb_io_descriptor(self.as_rb_value()) }
    }
}

#[cfg(unix)]
#[cfg(ruby_gt_3_0)]
impl AsRawFd for Rio {
    fn as_raw_fd(&self) -> RawFd {
        self.descriptor()
    }
}

/// OS agnostic `std::os::unix::io::AsRawFd`
pub trait AsRubyFd {
    /// `std::os::unix::io::AsRawFd::as_raw_fd`
    fn as_rb_fd(&self) -> RawRubyFd;

    /// Wait until `fileno` is readable
    fn wait_readable(&self) -> Result<(), Error> {
        let raw = self.as_rb_fd();
        protect(|| {
            unsafe { rb_thread_wait_fd(raw) };
            Value::default()
        })?;
        Ok(())
    }

    /// Wait until `fileno` is writable
    fn wait_writable(&self) -> Result<(), Error> {
        let raw = self.as_rb_fd();
        protect(|| {
            unsafe { rb_thread_fd_writable(raw) };
            Value::default()
        })?;
        Ok(())
    }

    /// Notify other Ruby threads when closing
    /// For when multiple threads wait for the same FD
    fn notify_closing(&self) {
        let raw = self.as_rb_fd();
        unsafe { rb_thread_fd_close(raw) }
    }
}

impl AsRubyFd for RawRubyFd {
    fn as_rb_fd(&self) -> RawRubyFd {
        *self
    }
}

#[cfg(ruby_gt_3_0)]
impl AsRubyFd for Rio {
    fn as_rb_fd(&self) -> RawRubyFd {
        self.descriptor()
    }
}

/// Used for `FDset::select`
pub struct FDset {
    inner: rb_fdset_t,
}

unsafe impl Send for FDset {}

impl Drop for FDset {
    fn drop(&mut self) {
        unsafe { rb_fd_term(&mut self.inner) }
    }
}

impl FDset {
    /// Create a new FD set
    pub fn new() -> Self {
        let mut inner = rb_fdset_t {
            #[cfg(unix)]
            maxfd: Default::default(),
            #[cfg(windows)]
            capa: Default::default(),
            fdset: null_mut(),
        };
        unsafe { rb_fd_init(&mut inner) };
        Self { inner }
    }
}

impl Default for FDset {
    fn default() -> Self {
        Self::new()
    }
}

impl Clone for FDset {
    fn clone(&self) -> Self {
        let mut new = Self::new();
        #[cfg(unix)]
        unsafe {
            rb_fd_dup(&mut new.inner, &self.inner)
        };
        #[cfg(windows)]
        unsafe {
            rb_w32_fd_dup(&mut new.inner, &self.inner)
        };
        new
    }
}

impl FDset {
    /// Number of `fd`s in FDset
    pub fn len(&self) -> usize {
        #[cfg(unix)]
        {
            let len = self.inner.maxfd;
            debug_assert!(len >= 0);
            len.unsigned_abs() as usize
        }
        #[cfg(windows)]
        unsafe {
            (*(self.inner.fdset)).fd_count as usize
        }
    }

    /// Check if `fd` is in FDset
    pub fn contains<D>(&self, fd: D) -> bool
    where
        D: AsRubyFd,
    {
        let raw = fd.as_rb_fd();
        #[cfg(unix)]
        unsafe {
            rb_fd_isset(raw, &self.inner) != 0
        }
        #[cfg(windows)]
        unsafe {
            rb_w32_fdisset(raw, self.inner.fdset) != 0
        }
    }

    /// Remove all `fd` from FDset
    pub fn clear(&mut self) {
        #[cfg(unix)]
        unsafe {
            rb_fd_zero(&mut self.inner);
        }
        #[cfg(windows)]
        unsafe {
            rb_fd_term(&mut self.inner);
            rb_fd_init(&mut self.inner);
        }
    }

    /// Add `fd` to FDset
    pub fn add<D>(&mut self, fd: D)
    where
        D: AsRubyFd,
    {
        let raw = fd.as_rb_fd();
        unsafe { rb_fd_set(raw, &mut self.inner) }
    }

    /// Remove `fd` from FDset
    pub fn remove<D>(&mut self, fd: D)
    where
        D: AsRubyFd,
    {
        let raw = fd.as_rb_fd();
        #[cfg(unix)]
        unsafe {
            rb_fd_clr(raw, &mut self.inner)
        }
        #[cfg(windows)]
        unsafe {
            rb_w32_fdclr(raw, self.inner.fdset);
        }
    }
}

#[cfg(ruby_gt_3_0)]
impl FDset {
    /// Like the `select` syscall, releases GVL.
    ///
    /// Return number of successes, if not timed out
    pub fn select(
        reads: &mut FDset,
        writes: &mut FDset,
        errors: &mut FDset,
        timeout: Option<Duration>,
    ) -> Result<Option<usize>, Error> {
        let time = timeout.map(|t| t.timeval()).transpose()?;
        let count = reads.len().max(writes.len()).max(errors.len());
        let fds = c_int::try_from(count).map_err(|e| Error::new(io_error(), e.to_string()))?;

        unsafe {
            let code = rb_thread_fd_select(
                fds,
                &mut reads.inner,
                &mut writes.inner,
                &mut errors.inner,
                match time {
                    Some(mut t) => &mut t as *mut _,
                    None => null_mut(),
                },
            );
            match code {
                -1 => {
                    let exn = protect(|| {
                        rb_sys_fail(null());
                        Value::default()
                    })
                    .unwrap_err();
                    Err(exn)
                }
                0 => Ok(None),
                c => Ok(Some(c as usize)),
            }
        }
    }
}
