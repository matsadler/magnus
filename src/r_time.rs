//!

use {
    crate::{
        class::time,
        error::{protect, Error},
        exception::{range_error, type_error},
        object::Object,
        ruby_sys::{
            rb_time_timespec, rb_time_timespec_new, rb_time_timeval, rb_time_utc_offset, timespec,
            timeval,
        },
        try_convert::TryConvert,
        value::{private, NonZeroValue, ReprValue, Value},
    },
    std::{
        convert::TryFrom,
        fmt::{Debug, Display, Error as FError, Formatter},
        ops::Deref,
        os::raw::{c_int, c_long, c_longlong},
        time::Duration,
    },
};

/// A Value pointer to a RTime struct, Ruby's internal representation of Time.
#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct RTime(NonZeroValue);

impl Deref for RTime {
    type Target = Value;
    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
    }
}

impl From<RTime> for Value {
    fn from(f: RTime) -> Self {
        *f
    }
}

unsafe impl private::ReprValue for RTime {
    fn to_value(self) -> Value {
        *self
    }

    unsafe fn from_value_unchecked(val: Value) -> Self {
        Self(NonZeroValue::new_unchecked(val))
    }
}

impl ReprValue for RTime {}

impl Object for RTime {}

impl Display for RTime {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FError> {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl Debug for RTime {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FError> {
        write!(f, "{}", self.inspect())
    }
}

impl TryConvert for RTime {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Self::from_value(val).ok_or_else(|| {
            Error::new(
                type_error(),
                format!("no implicit conversion of {} into Time", unsafe {
                    val.classname()
                }),
            )
        })
    }
}

impl RTime {
    /// Return `Some(RTime)` if `val` is a `RTime`, `None` otherwise.
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        if val.is_kind_of(time()) {
            Some(Self(unsafe { NonZeroValue::new_unchecked(val) }))
        } else {
            None
        }
    }
}

pub(crate) trait AsRawTime {
    fn timeval(&self) -> Result<timeval, Error>;
    fn timespec(&self) -> Result<timespec, Error>;
}

impl AsRawTime for Duration {
    fn timeval(&self) -> Result<timeval, Error> {
        let tv_sec = c_long::try_from(self.as_secs())
            .map_err(|e| Error::new(range_error(), e.to_string()))?;

        #[cfg(target_os = "linux")]
        let tv_usec = self.subsec_nanos().into();
        #[cfg(not(target_os = "linux"))]
        let tv_usec = c_int::try_from(self.subsec_nanos())
            .map_err(|e| Error::new(range_error(), e.to_string()))?;

        Ok(timeval { tv_sec, tv_usec })
    }

    fn timespec(&self) -> Result<timespec, Error> {
        let tv_sec = c_longlong::try_from(self.as_secs())
            .map_err(|e| Error::new(range_error(), e.to_string()))?;

        #[cfg(target_os = "linux")]
        let tv_nsec = self.subsec_nanos().into();
        #[cfg(target_os = "macos")]
        let tv_nsec = c_long::try_from(self.subsec_nanos())
            .map_err(|e| Error::new(range_error(), e.to_string()))?;
        #[cfg(target_os = "windows")]
        let tv_nsec = c_int::try_from(self.subsec_nanos())
            .map_err(|e| Error::new(range_error(), e.to_string()))?;

        Ok(timespec { tv_sec, tv_nsec })
    }
}

impl AsRawTime for RTime {
    fn timeval(&self) -> Result<timeval, Error> {
        let mut time = timeval {
            tv_sec: Default::default(),
            tv_usec: Default::default(),
        };
        protect(|| {
            time = unsafe { rb_time_timeval(self.as_rb_value()) };
            Value::default()
        })?;
        Ok(time)
    }

    fn timespec(&self) -> Result<timespec, Error> {
        let mut time = timespec {
            tv_sec: Default::default(),
            tv_nsec: Default::default(),
        };
        protect(|| {
            time = unsafe { rb_time_timespec(self.as_rb_value()) };
            Value::default()
        })?;
        Ok(time)
    }
}

/// Used in creating Ruby Time
///
/// TimeZone::Offset should be between -86400 to 86400
pub enum TimeZone {
    #[allow(missing_docs)]
    Local,
    #[allow(missing_docs)]
    UTC,
    /// should be between -86400 to 86400
    UTCoffset(c_int),
}

impl TimeZone {
    fn offset(&self) -> c_int {
        match self {
            Self::Local => c_int::MAX,
            Self::UTC => c_int::MAX - 1,
            Self::UTCoffset(offset) => *offset,
        }
    }
}

impl RTime {
    // # Examples
    //
    // ```
    // use magnus::r_time::{RTime, TimeZone};
    //
    // let t1 = RTime::new(0, 0, TimeZone::UTC).unwrap();
    // assert!(t1.utc_offset() == 0);
    //
    // let t2 = RTime::new(0, 0, TimeZone::UTCoffset(419)).unwrap();
    // assert!(t2.utc_offset() == 419);
    // ```
    //
    /// Create a new `RTime`.
    pub fn new(secs: c_longlong, nanos: c_long, timezone: TimeZone) -> Result<Self, Error> {
        let ts = timespec {
            tv_sec: secs,
            tv_nsec: nanos,
        };
        let tz = timezone.offset();

        let val = protect(|| Value::new(unsafe { rb_time_timespec_new(&ts as *const _, tz) }))?;
        Ok(Self(unsafe { NonZeroValue::new_unchecked(val) }))
    }

    /// Get seconds and nanoseconds
    pub fn value(&self) -> Result<(c_longlong, c_long), Error> {
        let time = self.timespec()?;
        Ok((time.tv_sec, time.tv_nsec))
    }

    /// Return UTC offset in seconds
    pub fn utc_offset(&self) -> c_int {
        Value::new(unsafe { rb_time_utc_offset(self.as_rb_value()) })
            .try_convert()
            .expect("offset should be int")
    }
}
