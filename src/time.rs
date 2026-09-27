//! Types and functions for working with Ruby's Time class.
//!
//! With the `jiff` feature, [`jiff::Timestamp`] converts to and from Ruby
//! `Time` as an exact instant. Magnus uses UTC for the Ruby representation
//! because `jiff::Timestamp` carries no timezone presentation. Ruby-to-Jiff
//! conversion inherits the platform range of Ruby's native `timespec` and
//! raises `RangeError` with `"out of Time range"` for values outside
//! [Jiff's supported timestamp range][jiff-timestamp-range].
//!
//! With the `jiff-zoned` feature, [`jiff::Zoned`] also converts in both
//! directions. Magnus preserves Jiff's timezone rules in an immutable Ruby
//! `Timezone` [timezone object][ruby-timezones]. The object supports
//! instant-based Ruby arithmetic, timezone names, unambiguous local
//! civil-time construction, and `Marshal` for named and fixed-offset zones.
//!
//! Magnus registers the timezone class as `TimeZoneMagnus_<version>`. It sets
//! the `Timezone` alias when absent or when it points to an older Magnus class;
//! a foreign or equal/newer alias is left alone. If the versioned constant
//! already holds a class at initialization, Magnus binds to that class and
//! leaves the alias and `Time.find_timezone` resolver untouched. Otherwise,
//! Magnus installs the resolver when absent or when replacing an older Magnus
//! alias.
//!
//! Local times in timezone gaps or folds raise `ArgumentError`. UTC and
//! fixed-offset Ruby times can also become `jiff::Zoned`. Magnus rejects other
//! Ruby timezone objects when the timezone rules do not have a provably
//! lossless Jiff representation. If Ruby cannot represent a Jiff offset,
//! Magnus warns and returns the same instant in UTC.
//!
//! Jiff civil and duration types remain intentionally unsupported: civil
//! values are wall-clock fields rather than instants, while [`jiff::Span`] and
//! [`jiff::SignedDuration`] have distinct duration semantics.
//!
//! [jiff-timestamp-range]: https://docs.rs/jiff/latest/jiff/struct.Timestamp.html#associatedconstant.MIN
//! [ruby-timezones]: https://docs.ruby-lang.org/en/3.2/timezones_rdoc.html
//!
//! See also [`Ruby`](Ruby#time) for more Time related methods.

use std::{
    ffi::c_int,
    fmt,
    time::{Duration, SystemTime},
};

use rb_sys::{
    VALUE, rb_time_nano_new, rb_time_new, rb_time_timespec, rb_time_timespec_new,
    rb_time_utc_offset, timespec,
};

#[cfg(feature = "jiff-zoned")]
use crate::{
    DataType, DataTypeFunctions, RClass, TypedData,
    class::Class,
    module::Module,
    typed_data::{DataTypeBuilder, Obj},
    value::Lazy,
};

use crate::{
    api::Ruby,
    error::{Error, IntoError, protect},
    into_value::IntoValue,
    object::Object,
    r_typed_data::RTypedData,
    try_convert::TryConvert,
    value::{
        Fixnum, ReprValue, Value,
        private::{self, ReprValue as _},
    },
};

#[cfg(feature = "jiff-zoned")]
const MAGNUS_TIMEZONE_VERSION: &str = "MAGNUS_JIFF_VERSION";

#[cfg(feature = "jiff-zoned")]
static JIFF_TIMEZONE_CLASS: Lazy<RClass> = Lazy::new(|ruby| {
    JiffTimeZone::create_class(ruby).expect("failed to initialize the Jiff timezone class")
});

#[cfg(feature = "jiff-zoned")]
fn magnus_timezone_version(version: &str) -> (u64, u64, u64) {
    let (major, rest) = version
        .split_once('.')
        .expect("Magnus version needs major.minor.patch");
    let (minor, patch) = rest
        .split_once('.')
        .expect("Magnus version needs major.minor.patch");
    (
        major.parse().expect("invalid Magnus major version"),
        minor.parse().expect("invalid Magnus minor version"),
        patch.parse().expect("invalid Magnus patch version"),
    )
}

#[cfg(feature = "jiff-zoned")]
const TIMEZONE: &str = "Timezone";

#[cfg(feature = "jiff-zoned")]
fn versioned_timezone_name() -> String {
    format!(
        "TimeZoneMagnus_{}",
        env!("CARGO_PKG_VERSION")
            .chars()
            .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
            .collect::<String>()
    )
}

#[cfg(feature = "jiff-zoned")]
fn ensure_versioned_timezone(ruby: &Ruby, cached: Option<RClass>) -> Result<bool, Error> {
    let object = ruby.class_object();
    let name = versioned_timezone_name();
    if object.const_defined_at(name.as_str()) {
        let existing: Value = object.const_get(name.as_str())?;
        if RClass::from_value(existing).is_none() {
            return Err(Error::new(
                ruby.exception_type_error(),
                format!("{name} must be a Class"),
            ));
        }
        if cached.is_none_or(|class| class.as_rb_value() != existing.as_rb_value()) {
            return Ok(false);
        }
    } else if let Some(class) = cached {
        object.const_set(name.as_str(), class)?;
    }
    Ok(true)
}

#[cfg(feature = "jiff-zoned")]
enum TimezoneExistence {
    Absent,
    OtherGem,
    Magnus(String),
}

/// Returns the current `Timezone` registration, if any.
#[cfg(feature = "jiff-zoned")]
fn existing_timezone_version(ruby: &Ruby) -> Result<TimezoneExistence, Error> {
    let object = ruby.class_object();
    let existing = object
        .const_defined_at(TIMEZONE)
        .then(|| object.const_get::<_, Value>(TIMEZONE))
        .transpose()?;
    let Some(existing) = existing else {
        return Ok(TimezoneExistence::Absent);
    };
    let version = if let Some(class) = RClass::from_value(existing) {
        class
            .const_defined_at(MAGNUS_TIMEZONE_VERSION)
            .then(|| class.const_get::<_, Value>(MAGNUS_TIMEZONE_VERSION))
            .transpose()?
            .and_then(|value| String::try_convert(value).ok())
    } else {
        None
    };
    Ok(match version {
        Some(version) => TimezoneExistence::Magnus(version),
        None => TimezoneExistence::OtherGem,
    })
}

#[cfg(feature = "jiff-zoned")]
fn replaces_older_magnus_timezone(existence: &TimezoneExistence) -> bool {
    matches!(existence, TimezoneExistence::Magnus(version) if
        magnus_timezone_version(version) < magnus_timezone_version(env!("CARGO_PKG_VERSION")))
}

#[cfg(feature = "jiff-zoned")]
fn register_timezone_alias(
    ruby: &Ruby,
    class: RClass,
    existence: &TimezoneExistence,
) -> Result<(), Error> {
    let object = ruby.class_object();
    match existence {
        TimezoneExistence::Absent => object.const_set(TIMEZONE, class),
        TimezoneExistence::Magnus(_) if replaces_older_magnus_timezone(existence) => {
            object.remove_const(TIMEZONE)?;
            object.const_set(TIMEZONE, class)
        }
        TimezoneExistence::Magnus(_) | TimezoneExistence::OtherGem => Ok(()),
    }
}

#[cfg(feature = "jiff-zoned")]
#[allow(clippy::macro_metavars_in_unsafe, unused_imports, unused_variables)]
fn install_timezone_resolver(ruby: &Ruby, existence: &TimezoneExistence) -> Result<(), Error> {
    let time = ruby.class_time();
    if replaces_older_magnus_timezone(existence)
        || (!matches!(existence, TimezoneExistence::Magnus(_))
            && !time.respond_to("find_timezone", true)?)
    {
        time.define_singleton_method(
            "find_timezone",
            crate::function!(JiffTimeZone::find_timezone, 1),
        )?;
    }
    Ok(())
}

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
    /// use magnus::{Error, Ruby, rb_assert};
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
            // types vary by plaftom so conversion isn't always useless
            #[allow(clippy::useless_conversion)]
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
    /// use magnus::{Error, Ruby, rb_assert};
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
            // types vary by plaftom so conversion isn't always useless
            #[allow(clippy::useless_conversion)]
            Time::from_rb_value_unchecked(rb_time_nano_new(
                seconds.try_into().unwrap(),
                nanoseconds.try_into().unwrap(),
            ))
        })
    }

    /// Create a new `Time` with nanosecond resolution with the given offset.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{
    ///     Error, Ruby,
    ///     error::IntoError,
    ///     rb_assert,
    ///     time::{Offset, Timespec},
    /// };
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let ts = Timespec {
    ///         tv_sec: 1654013280,
    ///         tv_nsec: 0,
    ///     };
    ///     let offset = Offset::from_hours(-7).map_err(|e| e.into_error(ruby))?;
    ///     let t = ruby.time_timespec_new(ts, offset)?;
    ///
    ///     rb_assert!(ruby, r#"t == Time.new(2022, 5, 31, 9, 8, 0, "-07:00")"#, t);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn time_timespec_new(&self, ts: Timespec, offset: Offset) -> Result<Time, Error> {
        protect(|| unsafe {
            Time::from_rb_value_unchecked(rb_time_timespec_new(
                &ts.into() as *const _,
                offset.as_c_int(),
            ))
        })
    }
}

/// Struct representing a point in time as an offset from the UNIX epoch.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Timespec {
    /// Seconds since the UNIX epoch.
    pub tv_sec: i64,
    /// Subsecond offset in nanoseconds.
    pub tv_nsec: i64,
}

impl From<timespec> for Timespec {
    fn from(val: timespec) -> Self {
        Self {
            tv_sec: val.tv_sec as _,
            tv_nsec: val.tv_nsec as _,
        }
    }
}

impl From<Timespec> for timespec {
    fn from(val: Timespec) -> Self {
        // timespec can't be built with a struct literal as on some targets
        // bindgen generates extra fields, e.g. on 32-bit musl targets
        // timespec's padding around tv_nsec appears as bitfield members.
        let mut ts: timespec = unsafe { std::mem::zeroed() };
        ts.tv_sec = val.tv_sec as _;
        ts.tv_nsec = val.tv_nsec as _;
        ts
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum OffsetType {
    Local,
    Utc,
    Offset(c_int),
}

/// Struct representing an offset from UTC.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Offset(OffsetType);

impl Offset {
    /// Creates a new `Offset` from the specified number of seconds.
    pub fn from_secs(offset: i32) -> Result<Self, OffsetError> {
        match offset {
            -86400..=86400 => Ok(Self(OffsetType::Offset(offset as _))),
            _ => Err(OffsetError(offset)),
        }
    }

    /// Creates a new `Offset` from the specified number of minutes.
    pub fn from_mins(offset: i32) -> Result<Self, OffsetError> {
        Self::from_secs(offset * 60)
    }

    /// Creates a new `Offset` from the specified number of hours.
    pub fn from_hours(offset: i32) -> Result<Self, OffsetError> {
        Self::from_secs(offset * 60)
    }

    /// Create a new `Offset` representing local time.
    pub fn local() -> Self {
        Self(OffsetType::Local)
    }

    /// Create a new `Offset` representing UTC.
    pub fn utc() -> Self {
        Self(OffsetType::Utc)
    }

    fn as_c_int(&self) -> c_int {
        match self.0 {
            OffsetType::Local => c_int::MAX,
            OffsetType::Utc => c_int::MAX - 1,
            OffsetType::Offset(i) => i,
        }
    }
}

/// An error returned when an [`Offset`] is out of range.
#[derive(Debug)]
pub struct OffsetError(i32);

impl fmt::Display for OffsetError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "utc_offset {} out of range (-86400 to 86400)", self.0)
    }
}

impl std::error::Error for OffsetError {}

impl IntoError for OffsetError {
    #[inline]
    fn into_error(self, ruby: &Ruby) -> Error {
        Error::new(ruby.exception_arg_error(), self.to_string())
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
        unsafe { Self(RTypedData::from_rb_value_unchecked(val)) }
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

    /// Returns `self` as a [`Timespec`].
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Error, Ruby, Time};
    ///
    /// fn example(ruby: &Ruby) -> Result<(), Error> {
    ///     let t: Time =
    ///         ruby.eval(r#"Time.new(2022, 5, 31, 9, 8, 123456789/1000000000r, "-07:00")"#)?;
    ///
    ///     assert_eq!(t.timespec()?.tv_sec, 1654013280);
    ///     assert_eq!(t.timespec()?.tv_nsec, 123456789);
    ///
    ///     Ok(())
    /// }
    /// # Ruby::init(example).unwrap()
    /// ```
    pub fn timespec(self) -> Result<Timespec, Error> {
        let mut timespec: timespec = unsafe { std::mem::zeroed() };
        protect(|| unsafe {
            timespec = rb_time_timespec(self.as_rb_value());
            Ruby::get_with(self).qnil()
        })?;
        Ok(timespec.into())
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
                    duration.subsec_nanos().into(),
                )
                .unwrap()
                .as_value(),
            Err(_) => {
                let duration = Self::UNIX_EPOCH.duration_since(self).unwrap();
                ruby.time_nano_new(
                    -i64::try_from(duration.as_secs()).unwrap(),
                    -i64::from(duration.subsec_nanos()),
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
        let ts = Timespec {
            tv_sec: delta.num_seconds(),
            tv_nsec: delta.subsec_nanos() as _,
        };
        ruby.time_timespec_new(ts, Offset::utc())
            .unwrap()
            .as_value()
    }
}

#[cfg(feature = "chrono")]
#[cfg_attr(docsrs, doc(cfg(feature = "chrono")))]
impl IntoValue for chrono::DateTime<chrono::FixedOffset> {
    #[inline]
    fn into_value_with(self, ruby: &Ruby) -> Value {
        use chrono::{DateTime, FixedOffset, Utc};
        let delta = self.signed_duration_since(DateTime::<Utc>::UNIX_EPOCH);
        let ts = Timespec {
            tv_sec: delta.num_seconds(),
            tv_nsec: delta.subsec_nanos() as _,
        };
        let offset: FixedOffset = self.timezone();
        let offset = Offset::from_secs(offset.local_minus_utc()).unwrap();
        ruby.time_timespec_new(ts, offset).unwrap().as_value()
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
        let mut timespec: timespec = unsafe { std::mem::zeroed() };
        protect(|| unsafe {
            timespec = rb_time_timespec(val.as_rb_value());
            Ruby::get_with(val).qnil()
        })?;
        if timespec.tv_nsec >= 0 {
            let mut duration = Duration::from_secs(timespec.tv_sec.unsigned_abs() as _);
            duration += Duration::from_nanos(timespec.tv_nsec as _);
            if timespec.tv_sec >= 0 {
                Ok(Self::UNIX_EPOCH + duration)
            } else {
                Ok(Self::UNIX_EPOCH - duration)
            }
        } else {
            Err(Error::new(
                Ruby::get_with(val).exception_arg_error(),
                "time nanos must not be negative",
            ))
        }
    }
}

#[cfg(feature = "chrono")]
#[cfg_attr(docsrs, doc(cfg(feature = "chrono")))]
impl TryConvert for chrono::DateTime<chrono::Utc> {
    fn try_convert(val: Value) -> Result<Self, Error> {
        let mut timespec: timespec = unsafe { std::mem::zeroed() };
        protect(|| unsafe {
            timespec = rb_time_timespec(val.as_rb_value());
            Ruby::get_with(val).qnil()
        })?;
        match chrono::Duration::new(timespec.tv_sec as _, timespec.tv_nsec as _) {
            Some(duration) => Ok(Self::UNIX_EPOCH + duration),
            None => Err(Error::new(
                Ruby::get_with(val).exception_arg_error(),
                "time out of range",
            )),
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
                ));
            }
        };
        Ok(dt.with_timezone(&tz))
    }
}

#[cfg(feature = "jiff")]
fn time_from_jiff_timestamp(
    ruby: &Ruby,
    timestamp: jiff::Timestamp,
    offset: Offset,
) -> Result<Time, Error> {
    ruby.time_timespec_new(
        Timespec {
            tv_sec: timestamp.as_second(),
            tv_nsec: i64::from(timestamp.subsec_nanosecond()),
        },
        offset,
    )
}

#[cfg(feature = "jiff")]
fn jiff_timestamp_from_value(val: Value) -> Result<jiff::Timestamp, Error> {
    let time = Time::try_convert(val)?;
    let ts = time.timespec()?;
    // Match CRuby's RangeError and message for an unrepresentable Time:
    // https://github.com/ruby/ruby/blob/16abdbdf18933922c42bf1542f18e2cb8f191c80/time.c#L2782
    let out_of_range = || {
        Error::new(
            Ruby::get_with(val).exception_range_error(),
            "out of Time range",
        )
    };
    let nanoseconds = i32::try_from(ts.tv_nsec).map_err(|_| out_of_range())?;
    jiff::Timestamp::new(ts.tv_sec, nanoseconds).map_err(|_| out_of_range())
}

#[cfg(feature = "jiff-zoned")]
pub(crate) fn init(ruby: &Ruby) -> Result<(), Error> {
    let Some(cached) = Lazy::try_get_inner(&JIFF_TIMEZONE_CLASS) else {
        ensure_versioned_timezone(ruby, None)?;
        let _ = JiffTimeZone::class(ruby);
        return Ok(());
    };
    let class = ruby.get_inner(cached);
    if !ensure_versioned_timezone(ruby, Some(class))? {
        return Ok(());
    }
    let object = ruby.class_object();
    if object.const_defined_at(TIMEZONE) {
        let current: Value = object.const_get(TIMEZONE)?;
        if current.as_rb_value() == class.as_rb_value() {
            return Ok(());
        }
    }
    let existence = existing_timezone_version(ruby)?;
    register_timezone_alias(ruby, class, &existence)?;
    install_timezone_resolver(ruby, &existence)
}

// Ruby passes the same Time::tm to dst? after either conversion callback.
// Store the resolved UTC instant on tm, not on the shared timezone object:
// https://github.com/ruby/ruby/blob/edce07a8c93895be8eeb2d27400aa138cc8a3cf9/time.c#L2442-L2484
#[cfg(feature = "jiff-zoned")]
const JIFF_RESOLVED_TIMESTAMP_INSTANCE_VARIABLE: &str = "@_resolved_ts";

#[cfg(feature = "jiff-zoned")]
fn set_resolved_timestamp(ruby: &Ruby, tm: Value, timestamp: jiff::Timestamp) -> Result<(), Error> {
    let tm_data = RTypedData::from_value(tm)
        .ok_or_else(|| Error::new(ruby.exception_type_error(), "expected a Time::tm or Time"))?;
    tm_data.ivar_set(
        JIFF_RESOLVED_TIMESTAMP_INSTANCE_VARIABLE,
        timestamp.as_second(),
    )
}

#[cfg(feature = "jiff-zoned")]
fn get_resolved_timestamp(ruby: &Ruby, tm: Value) -> Result<Option<jiff::Timestamp>, Error> {
    let tm_data = RTypedData::from_value(tm)
        .ok_or_else(|| Error::new(ruby.exception_type_error(), "expected a Time::tm or Time"))?;
    let seconds: Option<i64> = tm_data.ivar_get(JIFF_RESOLVED_TIMESTAMP_INSTANCE_VARIABLE)?;
    seconds
        .map(|seconds| {
            jiff::Timestamp::new(seconds, 0)
                .map_err(|_| Error::new(ruby.exception_range_error(), "out of Time range"))
        })
        .transpose()
}

/// Wraps Jiff's timezone rules as a Ruby `Timezone` object.
///
/// Magnus attaches this object to a Ruby `Time` as its timezone object; the
/// object is not itself a `Time`. Magnus can convert a `Time` with this
/// timezone object losslessly back to `jiff::Zoned`.
#[cfg(feature = "jiff-zoned")]
struct JiffTimeZone(jiff::tz::TimeZone);

#[cfg(feature = "jiff-zoned")]
impl JiffTimeZone {
    /// Resolves Ruby local civil-time fields to a UTC instant.
    ///
    /// # Arguments
    ///
    /// * `tm` - The Time-like object CRuby supplies with the local civil-time
    ///   fields to resolve.
    ///
    /// # Returns
    ///
    /// A UTC `Time` representing the resolved instant. Ruby uses it to
    /// construct the zoned `Time`.
    ///
    /// # Errors
    ///
    /// - Returns `ArgumentError` for a timezone gap or fold, or when Jiff
    ///   cannot represent the provisional or resolved instant.
    /// - Propagates errors from reading, converting, or updating `tm`.
    fn local_to_utc(ruby: &Ruby, this: &Self, tm: Value) -> Result<Time, Error> {
        // CRuby supplies whole seconds in Time::tm, but not fractional seconds.
        // Time::tm represents an UTC value.
        //
        // jiff's Timestamp range is:
        // -9999-01-02 01:59:59 through 9999-12-30 22:00:00 UTC;
        // read more https://docs.rs/jiff/latest/jiff/struct.Timestamp.html#panics.
        // A _rare_ civil time near the boundary can trigger errors.
        // We will use jiff to raise errors. Ruby also.
        //
        // Jiff rejects provisional or resolved instants outside its range.
        let provisional: i64 = tm.funcall("to_i", ())?;
        let timestamp = jiff::Timestamp::from_second(provisional)
            .map_err(|err| Error::new(ruby.exception_arg_error(), err.to_string()))?;
        let datetime = jiff::tz::Offset::UTC.to_datetime(timestamp);
        let timestamp = this
            .0
            .to_ambiguous_timestamp(datetime)
            .unambiguous()
            .map_err(|err| Error::new(ruby.exception_arg_error(), err.to_string()))?;
        // The civil-time fields in tm are provisional. Save the resolved UTC
        // instant for Ruby's subsequent dst? callback on this same object.
        set_resolved_timestamp(ruby, tm, timestamp)?;
        time_from_jiff_timestamp(ruby, timestamp, Offset::utc())
    }

    /// Converts a UTC instant to a `Time` with local wall-clock fields.
    ///
    /// # Returns
    ///
    /// A UTC `Time` whose clock fields represent the local wall time.
    fn utc_to_local(ruby: &Ruby, this: &Self, tm: Value) -> Result<Time, Error> {
        let timestamp = jiff_timestamp_from_time_like(ruby, tm)?;
        let offset = this.0.to_offset_info(timestamp).offset();
        let local_seconds = timestamp
            .as_second()
            .checked_add(i64::from(offset.seconds()))
            .ok_or_else(|| Error::new(ruby.exception_range_error(), "out of Time range"))?;
        set_resolved_timestamp(ruby, tm, timestamp)?;
        ruby.time_timespec_new(
            Timespec {
                tv_sec: local_seconds,
                tv_nsec: 0,
            },
            Offset::utc(),
        )
    }

    /// Returns the IANA name, or `nil` for another kind of timezone.
    fn iana_name(&self) -> Option<String> {
        self.0.iana_name().map(str::to_owned)
    }

    /// Returns a restorable name for an IANA zone.
    fn name(ruby: &Ruby, this: &Self) -> Result<String, Error> {
        this.0.iana_name().map(str::to_owned).ok_or_else(|| {
            Error::new(
                ruby.exception_type_error(),
                "jiff timezone does not have a restorable name",
            )
        })
    }

    fn to_s(&self) -> String {
        if let Some(name) = self.0.iana_name() {
            return name.to_owned();
        }
        if self.0.is_unknown() {
            return "Etc/Unknown".to_owned();
        }
        if let Ok(offset) = self.0.to_fixed_offset() {
            return offset.to_string();
        }
        "Jiff timezone".to_owned()
    }

    /// Returns the UTC timezone.
    fn utc(ruby: &Ruby) -> Obj<Self> {
        let zone = ruby.obj_wrap(Self(jiff::tz::TimeZone::UTC));
        zone.freeze();
        zone
    }

    /// Returns Jiff's unknown timezone, which behaves like UTC.
    fn unknown(ruby: &Ruby) -> Obj<Self> {
        let zone = ruby.obj_wrap(Self(jiff::tz::TimeZone::unknown()));
        zone.freeze();
        zone
    }

    /// Creates a fixed-offset timezone.
    ///
    /// # Examples
    ///
    /// ```ruby
    /// zone = Timezone.fixed(19_800) # UTC+05:30
    /// time = Time.at(0, in: zone)
    /// time.utc_offset # => 19_800
    /// ```
    ///
    /// # Arguments
    ///
    /// * `seconds` - The offset from UTC in seconds.
    ///
    /// # Errors
    ///
    /// Returns `ArgumentError` if Jiff cannot represent the offset.
    fn fixed(ruby: &Ruby, seconds: i32) -> Result<Obj<Self>, Error> {
        let offset = jiff::tz::Offset::from_seconds(seconds)
            .map_err(|err| Error::new(ruby.exception_arg_error(), err.to_string()))?;
        let zone = ruby.obj_wrap(Self(jiff::tz::TimeZone::fixed(offset)));
        zone.freeze();
        Ok(zone)
    }

    /// Parses a POSIX TZ string into a timezone.
    ///
    /// # Examples
    ///
    /// ```ruby
    /// zone = Timezone.posix('EST5EDT,M3.2.0,M11.1.0')
    /// winter = Time.new(2024, 1, 1, 12, 0, 0, in: zone)
    /// summer = Time.new(2024, 7, 1, 12, 0, 0, in: zone)
    /// winter.utc_offset # => -18_000
    /// summer.utc_offset # => -14_400
    /// summer.dst?      # => true
    /// ```
    ///
    /// # Errors
    ///
    /// Returns `ArgumentError` if Jiff cannot parse the rule.
    fn posix(ruby: &Ruby, rule: String) -> Result<Obj<Self>, Error> {
        let time_zone = jiff::tz::TimeZone::posix(&rule)
            .map_err(|err| Error::new(ruby.exception_arg_error(), err.to_string()))?;
        let zone = ruby.obj_wrap(Self(time_zone));
        zone.freeze();
        Ok(zone)
    }

    /// Looks up an IANA timezone in Jiff's global timezone database.
    ///
    /// Returns `nil` if the name is unknown.
    fn find_timezone(ruby: &Ruby, name: String) -> Option<Obj<Self>> {
        let time_zone = jiff::tz::TimeZone::get(&name).ok()?;
        let zone = ruby.obj_wrap(Self(time_zone));
        zone.freeze();
        Some(zone)
    }

    #[allow(clippy::macro_metavars_in_unsafe, unused_imports, unused_variables)]
    fn create_class(ruby: &Ruby) -> Result<RClass, Error> {
        let object = ruby.class_object();
        let cached = Lazy::try_get_inner(&JIFF_TIMEZONE_CLASS).map(|cached| ruby.get_inner(cached));
        let versioned_available = ensure_versioned_timezone(ruby, cached)?;
        let class = match cached {
            Some(class) => class,
            None if versioned_available => ruby.define_class(&versioned_timezone_name(), object)?,
            // Bind to the existing versioned class without replacing its constant.
            None => object.const_get(versioned_timezone_name().as_str())?,
        };
        class.const_set(MAGNUS_TIMEZONE_VERSION, env!("CARGO_PKG_VERSION"))?;
        class.undef_default_alloc_func();
        class.define_singleton_method(
            "find_timezone",
            crate::function!(JiffTimeZone::find_timezone, 1),
        )?;
        class.define_singleton_method("utc", crate::function!(JiffTimeZone::utc, 0))?;
        class.define_singleton_method("unknown", crate::function!(JiffTimeZone::unknown, 0))?;
        class.define_singleton_method("fixed", crate::function!(JiffTimeZone::fixed, 1))?;
        class.define_singleton_method("posix", crate::function!(JiffTimeZone::posix, 1))?;
        class.define_method(
            "local_to_utc",
            crate::method!(JiffTimeZone::local_to_utc, 1),
        )?;
        class.define_method(
            "utc_to_local",
            crate::method!(JiffTimeZone::utc_to_local, 1),
        )?;
        class.define_method("abbr", crate::method!(JiffTimeZone::abbr, 1))?;
        class.define_method("dst?", crate::method!(JiffTimeZone::is_dst, 1))?;
        class.define_method("name", crate::method!(JiffTimeZone::name, 0))?;
        class.define_method("iana_name", crate::method!(JiffTimeZone::iana_name, 0))?;
        class.define_method("to_s", crate::method!(JiffTimeZone::to_s, 0))?;
        if versioned_available {
            let existence = existing_timezone_version(ruby)?;
            register_timezone_alias(ruby, class, &existence)?;
            install_timezone_resolver(ruby, &existence)?;
        }
        Ok(class)
    }

    fn abbr(ruby: &Ruby, this: &Self, tm: Value) -> Result<String, Error> {
        let timestamp = jiff_timestamp_from_time_like(ruby, tm)?;
        Ok(this.0.to_offset_info(timestamp).abbreviation().to_owned())
    }

    /// Reports whether the callback time observes DST.
    ///
    /// # Arguments
    ///
    /// * `tm` - The Time-like object CRuby supplies. After either timezone
    ///   conversion callback, it carries the resolved UTC instant.
    ///
    /// # Errors
    ///
    /// - Returns `RangeError` if the time falls outside Jiff's supported range.
    /// - Propagates other errors from accessing or converting `tm`.
    fn is_dst(ruby: &Ruby, this: &Self, tm: Value) -> Result<bool, Error> {
        let timestamp = match get_resolved_timestamp(ruby, tm)? {
            Some(timestamp) => timestamp,
            None => jiff_timestamp_from_time_like(ruby, tm)?,
        };
        Ok(this.0.to_offset_info(timestamp).dst().is_dst())
    }
}

#[cfg(feature = "jiff-zoned")]
impl DataTypeFunctions for JiffTimeZone {}

#[cfg(feature = "jiff-zoned")]
unsafe impl TypedData for JiffTimeZone {
    fn class(ruby: &Ruby) -> RClass {
        ruby.get_inner(&JIFF_TIMEZONE_CLASS)
    }

    fn data_type() -> &'static DataType {
        static DATA_TYPE: DataType = DataTypeBuilder::<JiffTimeZone>::new(c"jiff timezone")
            .free_immediately()
            .build();
        &DATA_TYPE
    }
}

/// Extracts the instant from CRuby's Time-like timezone callback object.
///
/// # Arguments
///
/// * `ruby` - The Ruby handle for the callback.
/// * `tm` - The Time-like object CRuby supplies to a timezone callback.
///
/// # Errors
///
/// - Propagates errors from [`rb_time_timespec`] when it cannot convert `tm` or
///   the value does not fit the platform `timespec`.
/// - Returns `RangeError` when the instant falls outside Jiff's supported range.
#[cfg(feature = "jiff-zoned")]
fn jiff_timestamp_from_time_like(ruby: &Ruby, tm: Value) -> Result<jiff::Timestamp, Error> {
    // rb_time_timespec accepts Time, Time::tm (time-like) or numeric values.
    // use Ruby API to avoid converting to unnecessary classes.
    let mut ts: timespec = unsafe { std::mem::zeroed() };
    protect(|| unsafe {
        ts = rb_time_timespec(tm.as_rb_value());
        ruby.qnil()
    })?;
    let out_of_range = || Error::new(ruby.exception_range_error(), "out of Time range");
    let nanoseconds = i32::try_from(ts.tv_nsec).map_err(|_| out_of_range())?;
    jiff::Timestamp::new(ts.tv_sec as i64, nanoseconds).map_err(|_| out_of_range())
}

#[cfg(feature = "jiff-zoned")]
fn jiff_time_zone_from_time(time: Time) -> Result<jiff::tz::TimeZone, Error> {
    let ruby = Ruby::get_with(time);
    let zone: Value = time.funcall("zone", ())?;
    if let Ok(zone) = Obj::<JiffTimeZone>::try_convert(zone) {
        return Ok(zone.0.clone());
    }

    if time.funcall::<_, _, bool>("utc?", ())? {
        return Ok(jiff::tz::TimeZone::UTC);
    }

    if zone.is_nil() {
        let seconds = i32::try_from(time.utc_offset()).map_err(|_| {
            Error::new(
                ruby.exception_range_error(),
                "UTC offset out of range for jiff::tz::Offset",
            )
        })?;
        let offset = jiff::tz::Offset::from_seconds(seconds).map_err(|err| {
            Error::new(
                ruby.exception_range_error(),
                format!("UTC offset out of range for jiff::tz::Offset: {err}"),
            )
        })?;
        return Ok(jiff::tz::TimeZone::fixed(offset));
    }

    Err(Error::new(
        ruby.exception_type_error(),
        "Ruby Time timezone cannot be represented losslessly as jiff::TimeZone",
    ))
}

#[cfg(feature = "jiff")]
#[cfg_attr(docsrs, doc(cfg(feature = "jiff")))]
impl IntoValue for jiff::Timestamp {
    #[inline]
    fn into_value_with(self, ruby: &Ruby) -> Value {
        time_from_jiff_timestamp(ruby, self, Offset::utc())
            .expect("jiff timestamp to be in range for Ruby Time")
            .as_value()
    }
}

/// Converts a Jiff zoned timestamp to a Ruby `Time`.
///
/// If Ruby rejects the Jiff zone's offset for the represented instant, Magnus
/// emits a warning and returns the same instant as a UTC `Time`.
#[cfg(feature = "jiff-zoned")]
#[cfg_attr(docsrs, doc(cfg(feature = "jiff-zoned")))]
impl IntoValue for jiff::Zoned {
    fn into_value_with(self, ruby: &Ruby) -> Value {
        let timestamp = self.timestamp();
        if self.time_zone() == &jiff::tz::TimeZone::UTC {
            return time_from_jiff_timestamp(ruby, timestamp, Offset::utc())
                .expect("jiff timestamp to be in range for Ruby Time")
                .as_value();
        }
        // A fixed zone needs only an offset, which Ruby Time stores directly.
        // Unlike a wrapped JiffTimeZone, it survives Marshal without a zone
        // name. Keep the unknown zone as an object to preserve its identity.
        let fixed_offset = self
            .time_zone()
            .to_fixed_offset()
            .ok()
            .filter(|offset| self.time_zone() == &jiff::tz::TimeZone::fixed(*offset));
        let result = if let Some(offset) = fixed_offset {
            Offset::from_secs(offset.seconds())
                .map_err(|err| err.into_error(ruby))
                .and_then(|offset| time_from_jiff_timestamp(ruby, timestamp, offset))
        } else {
            let zone = ruby.obj_wrap(JiffTimeZone(self.time_zone().clone()));
            zone.freeze();
            time_from_jiff_timestamp(ruby, timestamp, Offset::utc())
                .and_then(|time| time.funcall("getlocal", (zone,)))
        };
        match result {
            Ok(time) => time.as_value(),
            Err(err) => {
                ruby.warning(&format!(
                    "could not represent jiff timezone in Ruby Time ({err}); using UTC"
                ));
                time_from_jiff_timestamp(ruby, timestamp, Offset::utc())
                    .expect("jiff timestamp to be in range for Ruby Time")
                    .as_value()
            }
        }
    }
}

/// Converts a Ruby `Time` to a Jiff timestamp.
///
/// # Errors
///
/// Returns Ruby `RangeError` with `"out of Time range"` when the `Time` falls
/// outside Jiff's [`Timestamp::MIN`](jiff::Timestamp::MIN) through
/// [`Timestamp::MAX`](jiff::Timestamp::MAX) range.
#[cfg(feature = "jiff")]
#[cfg_attr(docsrs, doc(cfg(feature = "jiff")))]
impl TryConvert for jiff::Timestamp {
    fn try_convert(val: Value) -> Result<Self, Error> {
        jiff_timestamp_from_value(val)
    }
}

/// Converts a Ruby `Time` to a Jiff zoned timestamp.
///
/// # Errors
///
/// Returns Ruby `RangeError` with `"out of Time range"` when the `Time` falls
/// outside Jiff's [`Timestamp::MIN`](jiff::Timestamp::MIN) through
/// [`Timestamp::MAX`](jiff::Timestamp::MAX) range. Returns Ruby `TypeError`
/// when the `Time` has a timezone that Magnus cannot represent losslessly as a
/// Jiff timezone.
#[cfg(feature = "jiff-zoned")]
#[cfg_attr(docsrs, doc(cfg(feature = "jiff-zoned")))]
impl TryConvert for jiff::Zoned {
    fn try_convert(val: Value) -> Result<Self, Error> {
        let time = Time::try_convert(val)?;
        let timestamp = jiff_timestamp_from_value(val)?;
        let time_zone = jiff_time_zone_from_time(time)?;
        Ok(Self::new(timestamp, time_zone))
    }
}
