use std::time::SystemTime;

#[cfg(feature = "jiff-zoned")]
use jiff::{Timestamp, ZonedDateTime, tz::TimeZone};
#[cfg(feature = "jiff")]
use magnus::value::ReprValue;
use magnus::{Error, Ruby, rb_assert};
#[cfg(feature = "jiff-zoned")]
use magnus::{
    IntoValue, RClass, TryConvert, TypedData, Value, prelude::*, time::JiffTimeZone,
    typed_data::Obj,
};

#[test]
fn test_all() {
    magnus::Ruby::init(|ruby| {
        test_supports_system_time(ruby)?;
        #[cfg(feature = "chrono")]
        test_supports_chrono(ruby)?;
        #[cfg(feature = "jiff")]
        test_supports_jiff(ruby)?;
        #[cfg(feature = "jiff-zoned")]
        {
            test_native_zones_do_not_initialize_timezone_wrappers(ruby)?;
            test_named_zone_round_trips_without_registration(ruby)?;
            test_named_zone_metadata(ruby)?;
            test_timezone_callbacks_resolve_instants_and_dst(ruby)?;
            test_fixed_zones_use_native_ruby_offsets(ruby)?;
            test_local_construction_rejects_out_of_range_instants(ruby)?;
            test_direct_zoned_binding(ruby)?;
            let zone = test_local_construction_resolves_civil_time(ruby)?;
            test_local_construction_rejects_gaps_and_folds(ruby, zone)?;
            test_utc_fixed_posix_and_unknown_zone_round_trips(ruby)?;
            test_foreign_timezone_headers(ruby)?;
            test_zoned_conversion_rejects_unrepresentable_ruby_times(ruby)?;
        }
        Ok(())
    })
    .unwrap();
}

fn test_supports_system_time(ruby: &Ruby) -> Result<(), Error> {
    let t = ruby.eval::<SystemTime>("Time.new(1971)").unwrap();
    rb_assert!(ruby, "t.year == 1971", t);

    let t = ruby.eval::<SystemTime>("Time.new(1960)").unwrap();
    rb_assert!(ruby, "t.year == 1960", t);

    Ok(())
}

#[cfg(feature = "jiff")]
fn test_supports_jiff(ruby: &Ruby) -> Result<(), Error> {
    use jiff::Timestamp;
    use magnus::{IntoValue, TryConvert};

    let cases = [
        (0, 0),
        (1, 0),
        (-1, 0),
        (1, 123_456_789),
        (-1, 500_000_000),
        (0, 1),
        (0, 999_999_999),
    ];
    for (sec, nsec) in cases {
        let time = ruby.time_nano_new(sec, nsec)?;
        let got = Timestamp::try_convert(time.as_value())?;
        assert_eq!(got, Timestamp::new(sec, nsec as i32).unwrap());
    }

    for expected in [Timestamp::MIN, Timestamp::MAX] {
        let time = expected.into_value_with(ruby);
        assert_eq!(Timestamp::try_convert(time)?, expected);
        rb_assert!(ruby, "t.utc? && t.utc_offset == 0", t = time);
    }

    for nanos in [1_i128, 123_456_789, 999_999_999, -500_000_000] {
        let expected = Timestamp::from_nanosecond(nanos).unwrap();
        let time = expected.into_value_with(ruby);
        let got = Timestamp::try_convert(time)?;
        assert_eq!(got, expected);
        rb_assert!(ruby, "t.utc? && t.utc_offset == 0", t = time);
    }

    let negative = Timestamp::from_nanosecond(-500_000_000)
        .unwrap()
        .into_value_with(ruby);
    rb_assert!(ruby, "t.to_i == -1 && t.nsec == 500000000", t = negative);

    let instant = Timestamp::new(1_654_013_280, 123_456_789).unwrap();
    let utc = ruby.time_timespec_new(
        magnus::time::Timespec {
            tv_sec: 1_654_013_280,
            tv_nsec: 123_456_789,
        },
        magnus::time::Offset::utc(),
    )?;
    let plus = ruby.eval("Time.at(1654013280, 123456789, :nsec, in: '+05:30')")?;
    let minus = ruby.eval("Time.at(1654013280, 123456789, :nsec, in: '-07:00')")?;
    assert_eq!(Timestamp::try_convert(utc.as_value())?, instant);
    assert_eq!(Timestamp::try_convert(plus)?, instant);
    assert_eq!(Timestamp::try_convert(minus)?, instant);

    for value in [ruby.eval("nil")?, ruby.eval("0")?] {
        let err = Timestamp::try_convert(value).unwrap_err();
        assert!(err.is_kind_of(ruby.exception_type_error()), "{err}");
    }

    for value in [
        ruby.eval("Time.at(-377705023202)")?,
        ruby.eval("Time.at(253402207201)")?,
    ] {
        let err = Timestamp::try_convert(value).unwrap_err();
        assert!(err.is_kind_of(ruby.exception_range_error()), "{err}");
        assert!(err.to_string().contains("out of Time range"), "{err}");
    }

    Ok(())
}

#[cfg(feature = "jiff-zoned")]
fn test_native_zones_do_not_initialize_timezone_wrappers(ruby: &Ruby) -> Result<(), Error> {
    let wrapper_count: Value = ruby.eval(
        "-> { ObjectSpace.each_object(Class).count { |class_| \
         class_.name.nil? && class_.instance_methods(false).include?(:local_to_utc) && \
         class_.instance_methods(false).include?(:utc_to_local) } }",
    )?;
    let before: usize = wrapper_count.funcall("call", ())?;
    for (source, expected_offset) in [("Time.at(0).utc", 0), ("Time.at(0, in: '+05:30')", 19_800)] {
        let value: Value = ruby.eval(source)?;
        let zoned = ZonedDateTime::try_convert(value)?;
        assert_eq!(zoned.offset().seconds(), expected_offset);
        let _: Value = zoned.into_value_with(ruby);
        let after: usize = wrapper_count.funcall("call", ())?;
        assert_eq!(
            after, before,
            "native timezone conversion allocated a wrapper class"
        );
    }
    Ok(())
}

#[cfg(feature = "jiff-zoned")]
fn test_named_zone_round_trips_without_registration(ruby: &Ruby) -> Result<(), Error> {
    assert!(!ruby.class_time().respond_to("find_timezone", true)?);
    let new_york = TimeZone::get("America/New_York").unwrap();
    for timestamp in [
        Timestamp::MIN,
        Timestamp::MAX,
        Timestamp::from_nanosecond(-500_000_000).unwrap(),
        "2024-11-03T05:30:00.123456789Z".parse().unwrap(),
        "2024-11-03T06:30:00.123456789Z".parse().unwrap(),
    ] {
        let expected = ZonedDateTime::new(timestamp, new_york.clone());
        let time = expected.clone().into_value_with(ruby);
        let actual = ZonedDateTime::try_convert(time)?;
        assert_eq!(actual, expected);
        assert_eq!(actual.time_zone(), expected.time_zone());
        rb_assert!(
            ruby,
            "t.zone.class.name.nil? && t.zone.frozen? && \
             t.zone.inspect.include?('JiffTimezone') && \
             t.zone.inspect.include?('America/New_York')",
            t = time
        );
    }
    rb_assert!(
        ruby,
        "!Object.const_defined?(:JiffTimezone, false) && \
        !Time.respond_to?(:find_timezone, true)"
    );

    ruby.eval::<Value>("class JiffTimezone; end")?;
    let unrelated =
        ZonedDateTime::new(Timestamp::UNIX_EPOCH, new_york.clone()).into_value_with(ruby);
    rb_assert!(ruby, "t.zone.class.name.nil?", t = unrelated);
    ruby.eval::<Value>("Object.send(:remove_const, :JiffTimezone)")?;
    Ok(())
}

#[cfg(feature = "jiff-zoned")]
fn test_named_zone_metadata(ruby: &Ruby) -> Result<(), Error> {
    let new_york = TimeZone::get("America/New_York").unwrap();
    for (stamp, offset, abbreviation, dst) in [
        ("2024-01-01T12:00:00Z", -18_000, "EST", false),
        ("2024-07-01T12:00:00Z", -14_400, "EDT", true),
    ] {
        let time =
            ZonedDateTime::new(stamp.parse().unwrap(), new_york.clone()).into_value_with(ruby);
        rb_assert!(
            ruby,
            "t.utc_offset == offset && t.strftime('%Z') == abbreviation && \
            t.dst? == dst",
            t = time,
            offset,
            abbreviation,
            dst
        );
    }

    Ok(())
}

#[cfg(feature = "jiff-zoned")]
fn test_timezone_callbacks_resolve_instants_and_dst(ruby: &Ruby) -> Result<(), Error> {
    let zone = ruby.obj_wrap(JiffTimeZone::new(
        TimeZone::get("America/New_York").unwrap(),
    ));
    let local: Value = ruby.eval(
        "Time.utc(2024, 3, 10, 3, 30).tap do |tm| \
         def tm.to_i; raise 'timezone callbacks must use native Time data'; end; end",
    )?;
    rb_assert!(
        ruby,
        "zone.local_to_utc(tm) == Time.utc(2024, 3, 10, 7, 30) && zone.dst?(tm)",
        zone,
        tm = local,
    );
    let before: Value = ruby.eval("Time.utc(2024, 3, 10, 6, 30)")?;
    let after: Value = ruby.eval("Time.utc(2024, 3, 10, 7, 30)")?;
    rb_assert!(
        ruby,
        "zone.utc_to_local(before) == Time.utc(2024, 3, 10, 1, 30) && \
         zone.abbr(before) == 'EST' && !zone.dst?(before) && \
         zone.utc_to_local(after) == Time.utc(2024, 3, 10, 3, 30) && \
         zone.abbr(after) == 'EDT' && zone.dst?(after)",
        zone,
        before,
        after,
    );
    let fixed = ruby.obj_wrap(JiffTimeZone::new(TimeZone::fixed(
        jiff::tz::Offset::from_seconds(3600).unwrap(),
    )));
    for month in [1, 7] {
        rb_assert!(
            ruby,
            "fixed.local_to_utc(Time.utc(2024, month, 1, 12)) == Time.utc(2024, month, 1, 11) && \
             fixed.utc_to_local(Time.utc(2024, month, 1, 11)) == Time.utc(2024, month, 1, 12)",
            fixed,
            month,
        );
    }
    let error = zone
        .funcall::<_, _, Value>("dst?", (ruby.qnil(),))
        .unwrap_err();
    assert!(error.is_kind_of(ruby.exception_type_error()), "{error}");
    Ok(())
}

#[cfg(feature = "jiff-zoned")]
fn test_fixed_zones_use_native_ruby_offsets(ruby: &Ruby) -> Result<(), Error> {
    for seconds in [19_800, -86_399, 86_399] {
        let expected = ZonedDateTime::new(
            Timestamp::new(1_654_013_280, 123_456_789).unwrap(),
            TimeZone::fixed(jiff::tz::Offset::from_seconds(seconds).unwrap()),
        );
        let time = expected.clone().into_value_with(ruby);
        let actual = ZonedDateTime::try_convert(time)?;
        assert_eq!(actual, expected);
        assert_eq!(actual.time_zone(), expected.time_zone());
        rb_assert!(
            ruby,
            "t.utc_offset == offset && !t.utc? && t.zone.nil? && t.nsec == 123456789",
            t = time,
            offset = seconds,
        );
    }
    for offset in [jiff::tz::Offset::MIN, jiff::tz::Offset::MAX] {
        let time = ZonedDateTime::new(Timestamp::UNIX_EPOCH, TimeZone::fixed(offset))
            .into_value_with(ruby);
        rb_assert!(ruby, "t.utc? && t.to_i == 0", t = time);
    }
    let warning: Value = ruby.eval("Warning")?;
    let original: Value = warning.funcall("method", ("warn",))?;
    ruby.eval::<Value>("def Warning.warn(*); raise 'warning handler failed'; end")?;
    let time = ZonedDateTime::new(
        Timestamp::UNIX_EPOCH,
        TimeZone::fixed(jiff::tz::Offset::MAX),
    )
    .into_value_with(ruby);
    warning.funcall::<_, _, Value>("define_singleton_method", ("warn", original))?;
    rb_assert!(ruby, "t.utc? && t.to_i == 0", t = time);
    Ok(())
}

#[cfg(feature = "jiff-zoned")]
fn test_local_construction_rejects_out_of_range_instants(ruby: &Ruby) -> Result<(), Error> {
    for (year, month, day, hour, offset, expected) in [
        (-9999, 1, 1, 12, -72_000, Some("-009999-01-02T08:00:00Z")),
        (9999, 12, 31, 12, 72_000, Some("9999-12-30T16:00:00Z")),
        (-9999, 1, 2, 2, 72_000, None),
        (9999, 12, 30, 22, -72_000, None),
    ] {
        let zone = ruby.obj_wrap(JiffTimeZone::new(TimeZone::fixed(
            jiff::tz::Offset::from_seconds(offset).unwrap(),
        )));
        let result = ruby.class_time().funcall::<_, _, Value>(
            "new",
            (
                year,
                month,
                day,
                hour,
                0,
                0,
                magnus::kwargs!(ruby, "in" => zone),
            ),
        );
        if let Some(expected) = expected {
            assert_eq!(
                Timestamp::try_convert(result?)?,
                expected.parse::<Timestamp>().unwrap()
            );
        } else {
            let error = result.unwrap_err();
            assert!(error.is_kind_of(ruby.exception_arg_error()), "{error}");
        }
    }
    let utc = ruby.obj_wrap(JiffTimeZone::new(TimeZone::UTC));
    for year in [10000, -10000, 999999999] {
        let error = ruby
            .class_time()
            .funcall::<_, _, Value>("new", (year, 1, 1, magnus::kwargs!(ruby, "in" => utc)))
            .unwrap_err();
        assert!(
            error.is_kind_of(ruby.exception_arg_error()),
            "{year}: {error}"
        );
    }
    Ok(())
}

#[cfg(feature = "jiff-zoned")]
fn test_direct_zoned_binding(ruby: &Ruby) -> Result<(), Error> {
    let new_york = TimeZone::get("America/New_York").unwrap();
    // A direct Jiff type works in a binding without a public newtype or
    // any provider registration in Magnus.
    fn identity(time: ZonedDateTime) -> ZonedDateTime {
        time
    }
    ruby.define_global_function("core_jiff_identity", magnus::function!(identity, 1))?;
    let time = ZonedDateTime::new("2024-03-10T06:30:00.123456789Z".parse().unwrap(), new_york)
        .into_value_with(ruby);
    rb_assert!(
        ruby,
        "result = core_jiff_identity(t); result == t && result.nsec == 123456789 && \
         result.zone.iana_name == 'America/New_York' && result.utc_offset == -18000 && \
         (after = result + 3600).hour == 3 && after.utc_offset == -14400 && \
         result.zone.equal?(after.zone)",
        t = time
    );

    Ok(())
}

#[cfg(feature = "jiff-zoned")]
fn test_local_construction_resolves_civil_time(ruby: &Ruby) -> Result<Value, Error> {
    // A public subclass exercises compatible class selection and inherited
    // timezone callbacks in core conversions.
    let class = ruby.define_class("JiffTimezone", JiffTimeZone::class(ruby))?;
    fn find(ruby: &Ruby, class: RClass, name: String) -> Result<Obj<JiffTimeZone>, Error> {
        let zone = TimeZone::get(&name)
            .map_err(|err| Error::new(ruby.exception_arg_error(), err.to_string()))?;
        let object = ruby.obj_wrap_as(JiffTimeZone::new(zone), class);
        object.freeze();
        Ok(object)
    }
    class.define_singleton_method("find", magnus::method!(find, 1))?;
    let local: Value = ruby.eval(
        "Time.new(2024, 7, 1, 12, 0, 123456789/1000000000r, \
        in: JiffTimezone.find('America/New_York'))",
    )?;
    let converted = ZonedDateTime::try_convert(local)?;
    assert_eq!(converted.time_zone().iana_name(), Some("America/New_York"));
    assert_eq!(converted.timestamp().subsec_nanosecond(), 123_456_789);
    rb_assert!(
        ruby,
        "t.zone.class == JiffTimezone && t.dst? && t.utc_offset == -14400",
        t = local
    );
    let returned = converted.into_value_with(ruby);
    rb_assert!(
        ruby,
        "t.zone.instance_of?(JiffTimezone) && \
         t.zone.inspect.start_with?('#<JiffTimezone ')",
        t = returned
    );
    local.funcall("zone", ())
}

#[cfg(feature = "jiff-zoned")]
fn test_local_construction_rejects_gaps_and_folds(ruby: &Ruby, zone: Value) -> Result<(), Error> {
    for (month, day, hour) in [(3, 10, 2), (11, 3, 1)] {
        let error = ruby
            .class_time()
            .funcall::<_, _, Value>(
                "new",
                (
                    2024,
                    month,
                    day,
                    hour,
                    30,
                    0,
                    magnus::kwargs!(ruby, "in" => zone),
                ),
            )
            .unwrap_err();
        assert!(error.is_kind_of(ruby.exception_arg_error()), "{error}");
    }

    Ok(())
}

#[cfg(feature = "jiff-zoned")]
fn test_utc_fixed_posix_and_unknown_zone_round_trips(ruby: &Ruby) -> Result<(), Error> {
    for zone in [
        TimeZone::UTC,
        TimeZone::unknown(),
        TimeZone::fixed(jiff::tz::Offset::from_seconds(19_800).unwrap()),
        TimeZone::posix("EST5EDT,M3.2.0,M11.1.0").unwrap(),
    ] {
        for timestamp in [
            Timestamp::UNIX_EPOCH,
            Timestamp::MIN,
            Timestamp::MAX,
            Timestamp::from_nanosecond(-500_000_000).unwrap(),
        ] {
            let expected = ZonedDateTime::new(timestamp, zone.clone());
            let actual = ZonedDateTime::try_convert(expected.clone().into_value_with(ruby))?;
            assert_eq!(actual, expected);
            assert_eq!(actual.time_zone(), expected.time_zone());
        }
    }
    Ok(())
}

#[cfg(feature = "jiff-zoned")]
fn test_foreign_timezone_headers(ruby: &Ruby) -> Result<(), Error> {
    use std::ffi::c_char;

    use magnus::{
        DataTypeFunctions,
        typed_data::{DataType, DataTypeBuilder},
    };

    // This fixture implements only the public C header, with its own descriptor.
    // It has no Jiff payload, so a successful conversion must reconstruct the text.
    #[derive(DataTypeFunctions)]
    #[repr(C)]
    struct ForeignZone {
        version: u8,
        timezone: *const c_char,
    }

    // SAFETY: The pointer is null or borrows immutable static test data.
    unsafe impl Send for ForeignZone {}

    unsafe impl TypedData for ForeignZone {
        fn class(ruby: &Ruby) -> RClass {
            ruby.class_object()
        }

        fn data_type() -> &'static DataType {
            static DATA_TYPE: DataType =
                DataTypeBuilder::<ForeignZone>::new(c"magnus-jiff-timezone")
                    .free_immediately()
                    .build();
            &DATA_TYPE
        }
    }

    fn foreign_time(ruby: &Ruby, version: u8, text: Option<&'static [u8]>) -> Result<Value, Error> {
        let zone = ruby.obj_wrap(ForeignZone {
            version,
            timezone: text.map_or(std::ptr::null(), |text| text.as_ptr().cast()),
        });
        magnus::eval!(
            ruby,
            "Time.at(0, 123456789, :nsec).utc.tap { |time| \
             time.define_singleton_method(:zone) { zone } }",
            zone,
        )
    }

    let valid: &[(&'static [u8], TimeZone)] = &[
        (b"UTC\0", TimeZone::UTC),
        (b"Etc/Unknown\0", TimeZone::unknown()),
        (b"Asia/Tokyo\0", TimeZone::get("Asia/Tokyo").unwrap()),
        (
            b"+05:30\0",
            TimeZone::fixed(jiff::tz::Offset::from_seconds(19_800).unwrap()),
        ),
        (
            b"EST5EDT,M3.2.0,M11.1.0\0",
            TimeZone::posix("EST5EDT,M3.2.0,M11.1.0").unwrap(),
        ),
    ];
    for (text, expected) in valid {
        let converted = ZonedDateTime::try_convert(foreign_time(ruby, 1, Some(text))?)?;
        assert_eq!(
            converted.timestamp(),
            Timestamp::new(0, 123_456_789).unwrap()
        );
        assert_eq!(converted.time_zone(), expected);
    }

    let invalid: &[(u8, Option<&'static [u8]>, &str)] = &[
        (2, None, "unsupported Magnus timezone ABI version"),
        (1, None, "must not be NULL"),
        (
            1,
            Some(&[b'x'; 128]),
            "exceeds the byte limit or is not NUL-terminated",
        ),
        (1, Some(b"\xff\0"), "not UTF-8"),
        (
            1,
            Some(b"magnus:timezone:unrepresentable\0"),
            "no portable representation",
        ),
        (1, Some(b"Not/A_Zone\0"), "could not reconstruct"),
    ];
    for (version, text, message) in invalid {
        let error = ZonedDateTime::try_convert(foreign_time(ruby, *version, *text)?).unwrap_err();
        assert!(error.is_kind_of(ruby.exception_type_error()), "{error}");
        assert!(error.to_string().contains(message), "{error}");
    }
    Ok(())
}

#[cfg(feature = "jiff-zoned")]
fn test_zoned_conversion_rejects_unrepresentable_ruby_times(ruby: &Ruby) -> Result<(), Error> {
    for value in [ruby.qnil().as_value(), ruby.integer_from_i64(0).as_value()] {
        assert!(
            ZonedDateTime::try_convert(value)
                .unwrap_err()
                .is_kind_of(ruby.exception_type_error())
        );
    }
    let outside: Value = ruby.eval("Time.at(253402207201)")?;
    assert!(
        ZonedDateTime::try_convert(outside)
            .unwrap_err()
            .is_kind_of(ruby.exception_range_error())
    );
    let custom: Value = ruby.eval(
        "zone = Class.new do; \
         def local_to_utc(time) = time - 3600; \
         def utc_to_local(time) = time + 3600; \
         def name = 'Europe/London'; end.new; \
         Time.at(1654013280, in: zone)",
    )?;
    let error = ZonedDateTime::try_convert(custom).unwrap_err();
    assert!(error.is_kind_of(ruby.exception_type_error()), "{error}");
    assert!(
        error
            .to_string()
            .contains("cannot be represented losslessly"),
        "{error}"
    );
    Ok(())
}

#[cfg(feature = "chrono")]
fn test_supports_chrono(ruby: &Ruby) -> Result<(), Error> {
    use chrono::{DateTime, Datelike, FixedOffset, Utc};

    let t = ruby.eval::<DateTime<Utc>>("Time.at(0, 10, :nsec)").unwrap();
    assert_eq!(t.year(), 1970);
    assert_eq!(t.month(), 1);
    assert_eq!(t.day(), 1);
    assert_eq!(t.timestamp_subsec_nanos(), 10);

    let dt = ruby
        .eval::<DateTime<Utc>>(r#"Time.new(1971, 1, 1, 2, 2, 2.0000001, "Z")"#)
        .unwrap();
    assert_eq!(&dt.to_rfc3339(), "1971-01-01T02:02:02.000000099+00:00");
    rb_assert!(ruby, "dt.utc?", dt);
    rb_assert!(ruby, "dt.utc_offset == 0", dt);

    let dt = ruby
        .eval::<DateTime<Utc>>(r#"Time.new(1950, 1, 1, 0, 0, 0, "Z")"#)
        .unwrap();
    assert_eq!(&dt.to_rfc3339(), "1950-01-01T00:00:00+00:00");

    let dt = ruby
        .eval::<DateTime<Utc>>(r#"Time.new(1971, 1, 1, 2, 2, 2.0000001, "-07:00")"#)
        .unwrap();
    assert_eq!(&dt.to_rfc3339(), "1971-01-01T09:02:02.000000099+00:00");

    let dt = ruby
        .eval::<DateTime<FixedOffset>>(
            r#"Time.new(2022, 5, 31, 9, 8, 123456789/1000000000r, "-07:00")"#,
        )
        .unwrap();
    assert_eq!(&dt.to_rfc3339(), "2022-05-31T09:08:00.123456789-07:00");
    rb_assert!(ruby, "!dt.utc?", dt);
    rb_assert!(ruby, "dt.utc_offset == -25200", dt);

    let dt = ruby
        .eval::<DateTime<FixedOffset>>(
            r#"Time.new(2022, 5, 31, 9, 8, 123456789/1000000000r, "+05:30")"#,
        )
        .unwrap();
    assert_eq!(&dt.to_rfc3339(), "2022-05-31T09:08:00.123456789+05:30");
    rb_assert!(ruby, "!dt.utc?", dt);
    rb_assert!(ruby, "dt.utc_offset == 19800", dt);

    Ok(())
}
