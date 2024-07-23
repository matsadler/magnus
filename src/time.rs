use std::{
    fmt,
    time::{Duration, SystemTime},
};

use rb_sys::{
    rb_time_nano_new, rb_time_new, rb_time_timespec, rb_time_utc_offset, timespec, VALUE,
};

use crate::{
    api::Ruby,
    error::{protect, Error},
    into_value::IntoValue,
    object::Object,
    r_typed_data::RTypedData,
    try_convert::TryConvert,
    value::{
        private::{self, ReprValue as _},
        Fixnum, ReprValue, Value,
    },
};

/// # `Time`
///
/// Functions to create and work with Ruby `Time` objects.
///
/// See also the [`Time`] type.
impl Ruby {
    /// Create a new `Time` in the local timezone.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let t = ruby.time_new(1654013280, 0)?;
    ///
    ///     rb_assert!(ruby, r#"t == Time.new(2022, 5, 31, 9, 8, 0, "-07:00")"#, t);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn time_new(&self, seconds: i64, microseconds: i64) -> Result<Time, Error> {
        protect(|| unsafe {
            Time::from_rb_value_unchecked(rb_time_new(
                seconds.try_into().unwrap(),
                microseconds.try_into().unwrap(),
            ))
        })
    }

    /// Create a new `Time` with nanosecond resolution in the local timezone.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{rb_assert, Error, Ruby};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let t = ruby.time_nano_new(1654013280, 0)?;
    ///
    ///     rb_assert!(ruby, r#"t == Time.new(2022, 5, 31, 9, 8, 0, "-07:00")"#, t);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn time_nano_new(&self, seconds: i64, nanoseconds: i64) -> Result<Time, Error> {
        protect(|| unsafe {
            Time::from_rb_value_unchecked(rb_time_nano_new(
                seconds.try_into().unwrap(),
                nanoseconds.try_into().unwrap(),
            ))
        })
    }
}

/// Wrapper type for a Value known to be an instance of Ruby's Time class.
///
/// See the [`ReprValue`] and [`Object`] traits for additional methods
/// available on this type. See [`Ruby`](Ruby#time) for methods to create a
/// `Time`.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Time(RTypedData);

impl Time {
    /// Return `Some(Time)` if `val` is a `Time`, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::eval;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(magnus::Time::from_value(eval("Time.now").unwrap()).is_some());
    /// assert!(magnus::Time::from_value(eval("0").unwrap()).is_none());
    /// ```
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        RTypedData::from_value(val)
            .filter(|_| val.is_kind_of(Ruby::get_with(val).class_time()))
            .map(Self)
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        Self(RTypedData::from_rb_value_unchecked(val))
    }

    /// Returns the timezone offset of `self` from UTC in seconds.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby, Time};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let t: Time = ruby.eval(r#"Time.new(2022, 5, 31, 9, 8, 0, "-07:00")"#)?;
    ///
    ///     assert_eq!(t.utc_offset(), -25_200);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn utc_offset(self) -> i64 {
        unsafe { Fixnum::from_rb_value_unchecked(rb_time_utc_offset(self.as_rb_value())).to_i64() }
    }

    #[inline]
    fn timespec(self) -> Result<timespec, Error> {
        let mut timespec = timespec {
            tv_sec: 0,
            tv_nsec: 0,
        };
        protect(|| unsafe {
            timespec = rb_time_timespec(self.as_rb_value());
            Ruby::get_unchecked().qnil()
        })?;
        Ok(timespec)
    }

    /// Returns value of `self` as seconds from the UNIX epoch.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby, Time};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let t: Time = ruby.eval(r#"Time.new(2022, 5, 31, 9, 8, 0, "-07:00")"#)?;
    ///
    ///     assert_eq!(t.tv_sec()?, 1654013280);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn tv_sec(self) -> Result<i64, Error> {
        Ok(self.timespec()?.tv_sec as _)
    }

    /// Returns the number of nanoseconds in the subseconds part of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby, Time};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let t: Time = ruby.eval(r#"Time.new(2022, 5, 31, 9, 8, 123456789/1000000000r, "-07:00")"#)?;
    ///
    ///     assert_eq!(t.tv_nsec()?, 123456789);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn tv_nsec(self) -> Result<i64, Error> {
        Ok(self.timespec()?.tv_nsec as _)
    }

    /// Returns the number of microseconds in the subseconds part of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby, Time};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let t: Time = ruby.eval(r#"Time.new(2022, 5, 31, 9, 8, 123456789/1000000000r, "-07:00")"#)?;
    ///
    ///     assert_eq!(t.tv_usec()?, 123456);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    #[inline]
    pub fn tv_usec(self) -> Result<i64, Error> {
        // fake tv_usec with timespec.tv_nsec so that calls to tv_sec and
        // tv_usec next to each other have a chance to optimise to a single
        // call to rb_time_timespec
        Ok((self.timespec()?.tv_nsec / 1_000) as _)
    }
}

impl fmt::Display for Time {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for Time {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl IntoValue for Time {
    #[inline]
    fn into_value_with(self, _: &Ruby) -> Value {
        self.0.as_value()
    }
}

impl IntoValue for SystemTime {
    #[inline]
    fn into_value_with(self, ruby: &Ruby) -> Value {
        match self.duration_since(Self::UNIX_EPOCH) {
            Ok(duration) => ruby
                .time_nano_new(
                    duration.as_secs().try_into().unwrap(),
                    duration.subsec_nanos().try_into().unwrap(),
                )
                .unwrap()
                .as_value(),
            Err(_) => {
                let duration = Self::UNIX_EPOCH.duration_since(self).unwrap();
                ruby.time_nano_new(
                    -i64::try_from(duration.as_secs()).unwrap(),
                    -i64::try_from(duration.subsec_nanos()).unwrap(),
                )
                .unwrap()
                .as_value()
            }
        }
    }
}

#[cfg(feature = "chrono")]
#[cfg_attr(docsrs, doc(cfg(feature = "chrono")))]
impl IntoValue for chrono::DateTime<chrono::Utc> {
    #[inline]
    fn into_value_with(self, ruby: &Ruby) -> Value {
        let delta = self.signed_duration_since(Self::UNIX_EPOCH);
        ruby.time_nano_new(delta.num_seconds(), delta.subsec_nanos() as _)
            .unwrap()
            .as_value()
    }
}

#[cfg(feature = "chrono")]
#[cfg_attr(docsrs, doc(cfg(feature = "chrono")))]
impl IntoValue for chrono::DateTime<chrono::FixedOffset> {
    #[inline]
    fn into_value_with(self, ruby: &Ruby) -> Value {
        use chrono::{DateTime, Utc};
        let epoch = DateTime::<Utc>::UNIX_EPOCH.with_timezone(&self.timezone());
        let delta = self.signed_duration_since(epoch);
        ruby.time_nano_new(delta.num_seconds(), delta.subsec_nanos() as _)
            .unwrap()
            .as_value()
    }
}

impl Object for Time {}

unsafe impl private::ReprValue for Time {}

impl ReprValue for Time {}

impl TryConvert for Time {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Self::from_value(val).ok_or_else(|| {
            Error::new(
                Ruby::get_with(val).exception_type_error(),
                format!("no implicit conversion of {} into Time", unsafe {
                    val.classname()
                },),
            )
        })
    }
}

impl TryConvert for SystemTime {
    fn try_convert(val: Value) -> Result<Self, Error> {
        let mut timespec = timespec {
            tv_sec: 0,
            tv_nsec: 0,
        };
        protect(|| unsafe {
            timespec = rb_time_timespec(val.as_rb_value());
            Ruby::get_unchecked().qnil()
        })?;
        if timespec.tv_sec >= 0 && timespec.tv_nsec >= 0 {
            let mut duration = Duration::from_secs(timespec.tv_sec as _);
            duration += Duration::from_nanos(timespec.tv_nsec as _);
            Ok(Self::UNIX_EPOCH + duration)
        } else {
            Err(Error::new(
                Ruby::get_with(val).exception_arg_error(),
                "time must not be negative",
            ))
        }
    }
}

#[cfg(feature = "chrono")]
#[cfg_attr(docsrs, doc(cfg(feature = "chrono")))]
impl TryConvert for chrono::DateTime<chrono::Utc> {
    fn try_convert(val: Value) -> Result<Self, Error> {
        let mut timespec = timespec {
            tv_sec: 0,
            tv_nsec: 0,
        };
        protect(|| unsafe {
            timespec = rb_time_timespec(val.as_rb_value());
            Ruby::get_unchecked().qnil()
        })?;
        if timespec.tv_sec >= 0 && timespec.tv_nsec >= 0 {
            let mut duration = Duration::from_secs(timespec.tv_sec as _);
            duration += Duration::from_nanos(timespec.tv_nsec as _);
            Ok(Self::UNIX_EPOCH + duration)
        } else {
            Err(Error::new(
                Ruby::get_with(val).exception_arg_error(),
                "time must not be negative",
            ))
        }
    }
}

#[cfg(feature = "chrono")]
#[cfg_attr(docsrs, doc(cfg(feature = "chrono")))]
impl TryConvert for chrono::DateTime<chrono::FixedOffset> {
    fn try_convert(val: Value) -> Result<Self, Error> {
        use chrono::{DateTime, FixedOffset, Utc};
        let offset: i32 = val.funcall("utc_offset", ())?;
        let dt: DateTime<Utc> = TryConvert::try_convert(val)?;
        let tz = match FixedOffset::east_opt(offset) {
            Some(tz) => tz,
            None => {
                return Err(Error::new(
                    Ruby::get_with(val).exception_arg_error(),
                    "invalid UTC offset",
                ))
            }
        };
        Ok(dt.with_timezone(&tz))
    }
}
