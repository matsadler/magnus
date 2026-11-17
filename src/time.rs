//! Types and functions for working with Ruby's Time class.
//!
//! With the `jiff` feature, [`jiff::Timestamp`] converts to and from Ruby
//! `Time` as an exact instant. Magnus uses UTC for the Ruby representation
//! because `jiff::Timestamp` carries no timezone presentation. Ruby-to-Jiff
//! conversion inherits the platform range of Ruby's native `timespec` and
//! raises `RangeError` with `"out of Time range"` for values outside
//! [Jiff's supported timestamp range][jiff-timestamp-range].
//!
//! With `jiff-zoned`, Magnus converts [`jiff::ZonedDateTime`] using [`JiffTimeZone`].
//! Core conversions install no public constant or resolver because multiple extensions
//! could use the same `jiff-zoned` feature with different jiff and magnus.
//! A companion `jiff-magnus` gem provides a public class. Independent extensions can
//! exchange portable strings through `src/include/magnus_timezone.h`.
//!
//! [jiff-timestamp-range]: https://docs.rs/jiff/latest/jiff/struct.Timestamp.html#associatedconstant.MIN
//!
//! See also [`Ruby`](Ruby#time) for more Time related methods.

#[cfg(feature = "jiff-zoned")]
use std::ffi::{CStr, CString, c_char};

#[cfg(feature = "jiff-zoned")]
use jiff::{
    Timestamp,
    fmt::temporal::{DateTimeParser, DateTimePrinter},
    tz::TimeZone,
};

#[cfg(feature = "jiff-zoned")]
use crate::{
    DataType, DataTypeFunctions, RClass, TypedData,
    class::Class,
    module::Module,
    typed_data::{DataTypeBuilder, Obj},
    value::Lazy,
};

use std::{
    ffi::c_int,
    fmt,
    time::{Duration, SystemTime},
};

use rb_sys::{
    VALUE, rb_time_nano_new, rb_time_new, rb_time_timespec, rb_time_timespec_new,
    rb_time_utc_offset, timespec,
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

#[cfg(feature = "jiff")]
#[cfg_attr(docsrs, doc(cfg(feature = "jiff")))]
impl IntoValue for jiff::Timestamp {
    #[inline]
    fn into_value_with(self, ruby: &Ruby) -> Value {
        ruby.time_timespec_new(
            Timespec {
                tv_sec: self.as_second(),
                tv_nsec: i64::from(self.subsec_nanosecond()),
            },
            Offset::utc(),
        )
        .expect("jiff timestamp to be in range for Ruby Time")
        .as_value()
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
        let time = Time::try_convert(val)?;
        let ts = time.timespec()?;
        let out_of_range = || {
            Error::new(
                Ruby::get_with(val).exception_range_error(),
                "out of Time range",
            )
        };
        let nanoseconds = i32::try_from(ts.tv_nsec).map_err(|_| out_of_range())?;
        Self::new(ts.tv_sec, nanoseconds).map_err(|_| out_of_range())
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

// CRuby reuses the conversion argument for its following dst? callback. Keep
// the resolved instant on that argument, never on the shared timezone object.
#[cfg(feature = "jiff-zoned")]
const RESOLVED_TIMESTAMP: &str = "@_magnus_jiff_resolved_ts";

#[cfg(feature = "jiff-zoned")]
const DATA_TYPE_NAME: &CStr = c"magnus-jiff-timezone";
// The version of jiff-zoned ABI.
#[cfg(feature = "jiff-zoned")]
const ABI_VERSION: u8 = 1;

// Arbitrary default
#[cfg(feature = "jiff-zoned")]
const MAX_TIMEZONE_BYTES: usize = 128;

// Keep interchange string-only rather than retain TZif snapshots. Unnamed
// TZif can fail to print; the original rules remain available to Ruby callbacks.
// https://docs.rs/jiff/1.0.0/jiff/fmt/temporal/struct.DateTimePrinter.html#method.time_zone_to_string
#[cfg(feature = "jiff-zoned")]
const UNREPRESENTABLE: &CStr = c"magnus:timezone:unrepresentable";

#[cfg(feature = "jiff-zoned")]
const UNKNOWN_TIMEZONE_ID: &str = "Etc/Unknown";

#[cfg(feature = "jiff-zoned")]
const UNKNOWN_TIMEZONE_NAME: &str = "unknown-timezone";

#[cfg(feature = "jiff-zoned")]
#[repr(C)]
struct MagnusTimeZone {
    abi_version: u8,
    jiff_timezone: *const c_char,
}

/// Stores a Jiff [`TimeZone`] for Ruby `Time` timezone methods.
///
/// Ruby `Time` calls methods on a timezone object to resolve local times and
/// calculate offsets, abbreviations, and DST. This backing type retains the
/// original Jiff rules so those operations keep working across transitions;
/// storing only the current UTC offset would lose that behavior.
///
/// Magnus attaches this object when converting a named, POSIX, or unknown
/// [`jiff::ZonedDateTime`] timezone to Ruby. This remains a private class.
/// The `jiff-magnus` companion gem can further installs a public `JiffTimezone` class,
/// constructors, and `Time.find_timezone` resolver. As a user of `jiff-zoned`,
/// you could either use `jiff-magnus` code or implement these features.
///
/// Native extensions can subclass the anonymous backing class to provide
/// their own constructors:
///
/// ```
/// use jiff::tz::TimeZone;
/// use magnus::{Error, RClass, Ruby, TypedData, prelude::*, time::JiffTimeZone};
///
/// fn example(ruby: &Ruby) -> Result<(), Error> {
///     let class = RClass::new(JiffTimeZone::class(ruby))?;
///     ruby.class_object().const_set("JiffTimezone", class)?;
///     let zone = ruby.obj_wrap_as(JiffTimeZone::new(TimeZone::UTC), class);
///     zone.freeze();
///     Ok(())
/// }
/// # Ruby::init(example).unwrap()
/// ```
///
/// # Limitations
///
/// - Timezone objects can have different Ruby classes across Magnus builds.
/// - Cross-build conversion transfers a string, not the original timezone rules.
///
/// Consider two gems, A and B, each built with Magnus's `jiff-zoned` feature.
/// Gem A uses Magnus to create an unnamed Ruby timezone class. It defines
/// `JiffTimezone` as a subclass of that class, inheriting its timezone methods.
/// When A converts [`jiff::ZonedDateTime`] to Ruby [`Time`], Magnus checks this
/// inheritance and reuses `JiffTimezone` so Rust- and Ruby-created zones have
/// the same public class.
///
/// Gem B links a different Magnus copy, which creates a separate unnamed
/// class. B uses that class because A's timezone methods cannot read B's Rust
/// payload. A [`Time`] returned by B may therefore have a zone that is not a
/// `JiffTimezone` instance, even after the companion loads. Existing objects
/// keep their original class.
///
/// Independently built extensions read the C header and portable timezone
/// string defined in `src/include/magnus_timezone.h`, never private Rust fields.
/// IANA names resolve against the receiver's database, so rules can differ and
/// custom named TZif rules transfer only their name. Unnamed TZif rules without
/// a printable representation retain their local behavior but cannot cross
/// builds; foreign conversion raises `TypeError`.
#[cfg(feature = "jiff-zoned")]
#[cfg_attr(docsrs, doc(cfg(feature = "jiff-zoned")))]
#[repr(C)]
pub struct JiffTimeZone {
    // Must stay first: native readers borrow this C prefix.
    header: MagnusTimeZone,
    zone: TimeZone,
    timezone_string: CString,
}

#[cfg(feature = "jiff-zoned")]
unsafe impl Send for JiffTimeZone {}

#[cfg(feature = "jiff-zoned")]
impl JiffTimeZone {
    /// Creates timezone data retaining the supplied Jiff rules.
    pub fn new(zone: TimeZone) -> Self {
        let timezone_string = DateTimePrinter::new()
            .time_zone_to_string(&zone)
            .ok()
            .filter(|text| text.len() < MAX_TIMEZONE_BYTES)
            .and_then(|text| CString::new(text).ok())
            .unwrap_or_else(|| UNREPRESENTABLE.to_owned());
        Self {
            header: MagnusTimeZone {
                abi_version: ABI_VERSION,
                jiff_timezone: timezone_string.as_ptr(),
            },
            zone,
            timezone_string,
        }
    }

    fn local_to_utc(ruby: &Ruby, this: &Self, tm: Value) -> Result<Time, Error> {
        let seconds = time_argument_timespec(ruby, tm)?.tv_sec as i64;
        // Civil dates have a wider range than timestamps; validate the instant
        // only after applying the timezone's rules.
        let civil = jiff::civil::date(1970, 1, 1)
            .at(0, 0, 0, 0)
            .checked_add(jiff::SignedDuration::from_secs(seconds))
            .map_err(|err| Error::new(ruby.exception_arg_error(), err.to_string()))?;
        let timestamp = this
            .zone
            .to_ambiguous_timestamp(civil)
            .unambiguous()
            .map_err(|err| Error::new(ruby.exception_arg_error(), err.to_string()))?;
        set_resolved_timestamp(ruby, tm, timestamp)?;
        time_from_timestamp(ruby, timestamp, Offset::utc())
    }

    fn utc_to_local(ruby: &Ruby, this: &Self, tm: Value) -> Result<Time, Error> {
        let timestamp = time_argument_timestamp(ruby, tm)?;
        let offset = this.zone.to_offset_info(timestamp).offset();
        let seconds = timestamp
            .as_second()
            .checked_add(i64::from(offset.seconds()))
            .ok_or_else(|| Error::new(ruby.exception_range_error(), "out of Time range"))?;
        set_resolved_timestamp(ruby, tm, timestamp)?;
        ruby.time_timespec_new(
            Timespec {
                tv_sec: seconds,
                tv_nsec: 0,
            },
            Offset::utc(),
        )
    }

    fn abbr(ruby: &Ruby, this: &Self, tm: Value) -> Result<String, Error> {
        let timestamp = time_argument_timestamp(ruby, tm)?;
        Ok(this
            .zone
            .to_offset_info(timestamp)
            .abbreviation()
            .to_owned())
    }

    fn is_dst(ruby: &Ruby, this: &Self, tm: Value) -> Result<bool, Error> {
        let data = time_argument_data(ruby, tm)?;
        let seconds: Option<i64> = data.ivar_get(RESOLVED_TIMESTAMP)?;
        let timestamp = match seconds {
            Some(seconds) => Timestamp::from_second(seconds)
                .map_err(|_| Error::new(ruby.exception_range_error(), "out of Time range"))?,
            None => time_argument_timestamp(ruby, tm)?,
        };
        Ok(this.zone.to_offset_info(timestamp).dst().is_dst())
    }

    fn name(ruby: &Ruby, this: &Self) -> Result<String, Error> {
        this.iana_name().ok_or_else(|| {
            Error::new(
                ruby.exception_type_error(),
                "Jiff timezone does not have a restorable name",
            )
        })
    }

    fn iana_name(&self) -> Option<String> {
        self.zone.iana_name().map(str::to_owned)
    }

    fn to_s(&self) -> String {
        if let Some(name) = self.zone.iana_name() {
            name.to_owned()
        } else if self.zone.is_unknown() {
            UNKNOWN_TIMEZONE_ID.to_owned()
        } else if let Ok(offset) = self.zone.to_fixed_offset() {
            offset.to_string()
        } else {
            UNKNOWN_TIMEZONE_NAME.to_owned()
        }
    }

    fn inspect(this: Obj<Self>) -> Result<String, Error> {
        let class: Option<String> = this.class().funcall("name", ())?;
        let class = class.as_deref().unwrap_or("JiffTimezone (internal)");
        let representation = if this.timezone_string.as_c_str() == UNREPRESENTABLE {
            "unrepresentable".into()
        } else {
            this.timezone_string.to_string_lossy()
        };
        Ok(format!(
            "#<{class} timezone={:?} representation={representation:?}>",
            Self::to_s(&this)
        ))
    }
}

#[cfg(feature = "jiff-zoned")]
impl DataTypeFunctions for JiffTimeZone {}

// Implement TypedData manually because the derive macro requires a named class,
// while core conversions must work without jiff-magnus.
#[cfg(feature = "jiff-zoned")]
unsafe impl TypedData for JiffTimeZone {
    /// Jiff timezone objects implement Ruby's timezone methods. If users need a
    /// created object for a declared timezone class, users can reconstruct timezone
    /// through the jiff-magnus's lookup and use `Time#getlocal` to preserve the instant.
    #[allow(unused_imports)] // Binding macros import both receiver variants.
    fn class(ruby: &Ruby) -> RClass {
        static CLASS: Lazy<RClass> = Lazy::new(|ruby| {
            let class = RClass::new(ruby.class_object())
                .expect("failed to create Jiff timezone backing class");
            class.undef_default_alloc_func();
            class
                .define_method(
                    "local_to_utc",
                    crate::method!(JiffTimeZone::local_to_utc, 1),
                )
                .expect("failed to define Jiff timezone local_to_utc");
            class
                .define_method(
                    "utc_to_local",
                    crate::method!(JiffTimeZone::utc_to_local, 1),
                )
                .expect("failed to define Jiff timezone utc_to_local");
            class
                .define_method("abbr", crate::method!(JiffTimeZone::abbr, 1))
                .expect("failed to define Jiff timezone abbr");
            class
                .define_method("dst?", crate::method!(JiffTimeZone::is_dst, 1))
                .expect("failed to define Jiff timezone dst?");
            class
                .define_method("name", crate::method!(JiffTimeZone::name, 0))
                .expect("failed to define Jiff timezone name");
            class
                .define_method("iana_name", crate::method!(JiffTimeZone::iana_name, 0))
                .expect("failed to define Jiff timezone iana_name");
            class
                .define_method("to_s", crate::method!(JiffTimeZone::to_s, 0))
                .expect("failed to define Jiff timezone to_s");
            class
                .define_method("inspect", crate::method!(JiffTimeZone::inspect, 0))
                .expect("failed to define Jiff timezone inspect");
            class.freeze();
            class
        });
        ruby.get_inner(&CLASS)
    }

    fn data_type() -> &'static DataType {
        static DATA_TYPE: DataType = DataTypeBuilder::<JiffTimeZone>::new(DATA_TYPE_NAME)
            .free_immediately()
            .build();
        &DATA_TYPE
    }
}

#[cfg(feature = "jiff-zoned")]
fn time_argument_data(ruby: &Ruby, tm: Value) -> Result<RTypedData, Error> {
    RTypedData::from_value(tm)
        .ok_or_else(|| Error::new(ruby.exception_type_error(), "expected a Time::tm or Time"))
}

#[cfg(feature = "jiff-zoned")]
fn set_resolved_timestamp(ruby: &Ruby, tm: Value, timestamp: Timestamp) -> Result<(), Error> {
    time_argument_data(ruby, tm)?.ivar_set(RESOLVED_TIMESTAMP, timestamp.as_second())
}

#[cfg(feature = "jiff-zoned")]
fn time_argument_timespec(ruby: &Ruby, tm: Value) -> Result<rb_sys::timespec, Error> {
    // Time::tm is not a Time subclass, so read its shared native data type.
    let mut ts: rb_sys::timespec = unsafe { std::mem::zeroed() };
    protect(|| unsafe {
        ts = rb_sys::rb_time_timespec(tm.as_rb_value());
        ruby.qnil()
    })?;
    Ok(ts)
}

#[cfg(feature = "jiff-zoned")]
fn time_argument_timestamp(ruby: &Ruby, tm: Value) -> Result<Timestamp, Error> {
    let ts = time_argument_timespec(ruby, tm)?;
    let out_of_range = || Error::new(ruby.exception_range_error(), "out of Time range");
    let nanoseconds = i32::try_from(ts.tv_nsec).map_err(|_| out_of_range())?;
    Timestamp::new(ts.tv_sec as _, nanoseconds).map_err(|_| out_of_range())
}

#[cfg(feature = "jiff-zoned")]
fn time_from_timestamp(ruby: &Ruby, timestamp: Timestamp, offset: Offset) -> Result<Time, Error> {
    ruby.time_timespec_new(
        Timespec {
            tv_sec: timestamp.as_second(),
            tv_nsec: i64::from(timestamp.subsec_nanosecond()),
        },
        offset,
    )
}

#[cfg(feature = "jiff-zoned")]
impl crate::IntoValue for jiff::ZonedDateTime {
    fn into_value_with(self, ruby: &Ruby) -> Value {
        let timestamp = self.timestamp();
        let zone = self.time_zone();
        let result = (|| -> Result<Time, Error> {
            if zone == &TimeZone::UTC {
                time_from_timestamp(ruby, timestamp, Offset::utc())
            } else if let Some(offset) = zone
                .to_fixed_offset()
                .ok()
                .filter(|offset| zone == &TimeZone::fixed(*offset))
            {
                use crate::error::IntoError;
                Offset::from_secs(offset.seconds())
                    .map_err(|err| err.into_error(ruby))
                    .and_then(|offset| time_from_timestamp(ruby, timestamp, offset))
            } else {
                let mut class = JiffTimeZone::class(ruby);
                let object = ruby.class_object();
                if object.const_defined("JiffTimezone")? {
                    let candidate: Value = object.const_get("JiffTimezone")?;
                    if let Some(candidate) = RClass::from_value(candidate) {
                        // Inheritance from our class establishes native compatibility;
                        // another build's public name or ABI version does not.
                        if candidate.is_inherited(class) {
                            class = candidate;
                        }
                    }
                }
                let object = ruby.obj_wrap_as(JiffTimeZone::new(zone.clone()), class);
                object.freeze();
                time_from_timestamp(ruby, timestamp, Offset::utc())?.funcall("getlocal", (object,))
            }
        })();
        match result {
            Ok(time) => time.as_value(),
            Err(err) => {
                let message = CString::new(
                    format!("could not represent Jiff timezone in Ruby Time ({err}); using UTC")
                        .replace('\0', "\\0"),
                )
                .expect("warning text contains no NUL");
                // A custom warning handler must not prevent this infallible fallback.
                let _ = protect(|| {
                    unsafe { rb_sys::rb_warn(c"%s".as_ptr(), message.as_ptr()) };
                    ruby.qnil()
                });
                timestamp.into_value_with(ruby)
            }
        }
    }
}

/// Unknown ABI versions, invalid strings, names the receiver cannot resolve,
/// and representations exceeding 128 bytes including NUL raise `TypeError`.
/// Oversized strings use the unrepresentable marker when creating an object.
#[cfg(feature = "jiff-zoned")]
impl TryConvert for jiff::ZonedDateTime {
    fn try_convert(value: Value) -> Result<Self, Error> {
        let time = Time::try_convert(value)?;
        let timestamp = Timestamp::try_convert(value)?;
        let ruby = Ruby::get_with(time);
        let zone: Value = time.funcall("zone", ())?;
        // Only descriptor identity permits native Rust access; the portable ABI does not.
        let local_zone =
            RTypedData::from_value(zone).and_then(|_| Obj::<JiffTimeZone>::try_convert(zone).ok());
        let timezone = if let Some(zone) = local_zone {
            Some(zone.zone.clone())
        } else if let Some(data) = RTypedData::from_value(zone) {
            let invalid =
                |message: &str| Error::new(ruby.exception_type_error(), message.to_owned());
            // SAFETY: Ruby owns the TypedData descriptor. A native extension using
            // DATA_TYPE_NAME promises the public header layout, not Rust compatibility.
            // Magnus never casts its private Jiff value or invokes its Rust drop glue.
            let text = unsafe {
                let descriptor = rb_sys::RTYPEDDATA_TYPE(data.as_rb_value());
                let name = (*descriptor).wrap_struct_name;
                if name.is_null() || CStr::from_ptr(name) != DATA_TYPE_NAME {
                    None
                } else {
                    let pointer = rb_sys::RTYPEDDATA_GET_DATA(data.as_rb_value());
                    if pointer.is_null() {
                        return Err(invalid("uninitialized Magnus timezone"));
                    }
                    // Read only the first byte until the ABI version is validated.
                    let version = pointer.cast::<u8>().read();
                    if version != ABI_VERSION {
                        return Err(invalid("unsupported Magnus timezone ABI version"));
                    }
                    let header = &*pointer.cast::<MagnusTimeZone>();
                    if header.jiff_timezone.is_null() {
                        return Err(invalid("Magnus timezone representation must not be NULL"));
                    }
                    let bytes = header.jiff_timezone.cast::<u8>();
                    let mut length = 0;
                    while length < MAX_TIMEZONE_BYTES && bytes.add(length).read() != 0 {
                        length += 1;
                    }
                    if length == MAX_TIMEZONE_BYTES {
                        return Err(invalid(
                            "Magnus timezone representation exceeds the byte limit or is not NUL-terminated",
                        ));
                    }
                    Some(std::slice::from_raw_parts(bytes, length).to_vec())
                }
            };
            if let Some(text) = text {
                if text == UNREPRESENTABLE.to_bytes() {
                    return Err(invalid(
                        "Magnus timezone rules cannot be transferred: no portable representation",
                    ));
                }
                let text = std::str::from_utf8(&text)
                    .map_err(|_| invalid("Magnus timezone representation is not UTF-8"))?;
                Some(DateTimeParser::new().parse_time_zone(text).map_err(|err| {
                    invalid(&format!(
                        "could not reconstruct Magnus timezone from its portable representation: {err}"
                    ))
                })?)
            } else {
                None
            }
        } else {
            None
        };
        let timezone = if let Some(zone) = timezone {
            zone
        } else if time.funcall::<_, _, bool>("utc?", ())? {
            TimeZone::UTC
        } else if zone.is_nil() {
            let seconds = i32::try_from(time.utc_offset()).map_err(|_| {
                Error::new(ruby.exception_range_error(), "UTC offset out of Jiff range")
            })?;
            let offset = jiff::tz::Offset::from_seconds(seconds)
                .map_err(|err| Error::new(ruby.exception_range_error(), err.to_string()))?;
            TimeZone::fixed(offset)
        } else {
            return Err(Error::new(
                ruby.exception_type_error(),
                "Ruby Time timezone cannot be represented losslessly as a Jiff timezone",
            ));
        };
        Ok(Self::new(timestamp, timezone))
    }
}
