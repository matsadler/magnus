use std::time::SystemTime;

use magnus::{Error, Ruby, rb_assert};

#[cfg(feature = "jiff")]
use magnus::value::ReprValue;

#[cfg(feature = "jiff-zoned")]
use jiff::{
    Timestamp, Zoned,
    tz::{Offset, TimeZone},
};
#[cfg(feature = "jiff-zoned")]
use magnus::{IntoValue, Time, TryConvert, Value};

// Ruby::init can only initialize the VM once per test binary, so run each
// focused case through this single entry point.
#[test]
fn test_all() {
    magnus::Ruby::init(|ruby| {
        test_supports_system_time(ruby)?;
        #[cfg(feature = "chrono")]
        test_supports_chrono(ruby)?;
        #[cfg(feature = "jiff")]
        test_supports_jiff(ruby)?;
        #[cfg(feature = "jiff-zoned")]
        named_zone_arithmetic_and_fold_preserve_the_instant(ruby)?;
        #[cfg(feature = "jiff-zoned")]
        timezone_callbacks_resolve_instants_and_dst(ruby)?;
        #[cfg(feature = "jiff-zoned")]
        zoned_conversion_rejects_unrepresentable_ruby_times(ruby)?;
        #[cfg(feature = "jiff-zoned")]
        fixed_zones_use_native_ruby_offsets(ruby)?;
        #[cfg(feature = "jiff-zoned")]
        local_construction_resolves_civil_time(ruby)?;
        #[cfg(feature = "jiff-zoned")]
        local_construction_rejects_gaps_and_folds(ruby)?;
        #[cfg(feature = "jiff-zoned")]
        local_construction_rejects_out_of_range_instants(ruby)?;
        #[cfg(feature = "jiff-zoned")]
        named_time_survives_marshal(ruby)?;
        #[cfg(feature = "jiff-zoned")]
        fixed_time_survives_marshal(ruby)?;
        #[cfg(feature = "jiff-zoned")]
        named_zone_round_trips_with_seasonal_offsets_and_metadata(ruby)?;
        #[cfg(feature = "jiff-zoned")]
        posix_zone_observes_rules_in_both_conversion_directions(ruby)?;
        #[cfg(feature = "jiff-zoned")]
        timezone_find_returns_named_zone_and_timestamp(ruby)?;
        #[cfg(feature = "jiff-zoned")]
        resolver_parses_time_subclass(ruby)?;
        #[cfg(feature = "jiff-zoned")]
        resolver_finds_named_zones_for_ruby_time(ruby)?;
        #[cfg(feature = "jiff-zoned")]
        unknown_zone_remains_distinct_from_utc(ruby)?;
        #[cfg(feature = "jiff-zoned")]
        utc_zone_round_trips(ruby)?;
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

    // 2022-05-31 16:08:00 UTC
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

    for value in [ruby.qnil().as_value(), ruby.eval("0")?] {
        let err = Timestamp::try_convert(value).unwrap_err();
        assert!(err.is_kind_of(ruby.exception_type_error()), "{err}");
    }

    // -9999-01-02 01:59:58 UTC, before Jiff's supported range.
    // 9999-12-30 22:00:01 UTC, after Jiff's supported range.
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
fn named_zone_arithmetic_and_fold_preserve_the_instant(ruby: &Ruby) -> Result<(), Error> {
    let new_york = TimeZone::get("America/New_York").unwrap();
    let before = Zoned::new(
        "2024-03-10T06:30:00Z".parse::<Timestamp>().unwrap(),
        new_york.clone(),
    )
    .into_value_with(ruby);
    rb_assert!(
        ruby,
        "before.hour == 1 && before.utc_offset == -18000 && \
         (after = before + 3600).hour == 3 && after.utc_offset == -14400 && \
         before.zone.equal?(after.zone)",
        before,
    );
    for (timestamp, offset) in [
        ("2024-11-03T05:30:00Z", -14_400),
        ("2024-11-03T06:30:00Z", -18_000),
    ] {
        let expected = Zoned::new(timestamp.parse::<Timestamp>().unwrap(), new_york.clone());
        let time = expected.clone().into_value_with(ruby);
        assert_eq!(Zoned::try_convert(time)?, expected);
        rb_assert!(
            ruby,
            "t.hour == 1 && t.utc_offset == offset",
            t = time,
            offset
        );
    }
    Ok(())
}

#[cfg(feature = "jiff-zoned")]
fn timezone_callbacks_resolve_instants_and_dst(ruby: &Ruby) -> Result<(), Error> {
    let zone: Value = ruby.eval("Timezone.find_timezone('America/New_York')")?;
    let local: Value = ruby.eval("Time.utc(2024, 3, 10, 3, 30)")?;
    rb_assert!(
        ruby,
        "zone.local_to_utc(tm) == Time.utc(2024, 3, 10, 7, 30) && \
         zone.dst?(tm)",
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
    for month in [1, 7] {
        let result: Time = ruby.eval(&format!(
            "Timezone.fixed(3600).local_to_utc(Time.utc(2024, {month}, 1, 12))"
        ))?;
        rb_assert!(
            ruby,
            "result.utc? && result == Time.utc(2024, month, 1, 11)",
            result,
            month
        );
    }
    for month in [1, 7] {
        let result: Time = ruby.eval(&format!(
            "Timezone.fixed(3600).utc_to_local(Time.utc(2024, {month}, 1, 11))"
        ))?;
        rb_assert!(
            ruby,
            "result.utc? && result == Time.utc(2024, month, 1, 12)",
            result,
            month
        );
    }
    let err = zone
        .funcall::<_, _, Value>("dst?", (ruby.qnil(),))
        .unwrap_err();
    assert!(err.is_kind_of(ruby.exception_type_error()), "{err}");
    Ok(())
}

#[cfg(feature = "jiff-zoned")]
fn zoned_conversion_rejects_unrepresentable_ruby_times(ruby: &Ruby) -> Result<(), Error> {
    for value in [ruby.qnil().as_value(), ruby.integer_from_i64(0).as_value()] {
        let err = Zoned::try_convert(value).unwrap_err();
        assert!(err.is_kind_of(ruby.exception_type_error()), "{err}");
    }
    // 9999-12-30 22:00:01 UTC, outside Jiff's supported range.
    let outside: Value = ruby.eval("Time.at(253402207201)")?;
    let err = Zoned::try_convert(outside).unwrap_err();
    assert!(err.is_kind_of(ruby.exception_range_error()), "{err}");
    // 2022-05-31 16:08:00 UTC
    let custom: Value = ruby.eval(
        r#"
        zone = Class.new do
          def local_to_utc(time) = time - 3600
          def utc_to_local(time) = time + 3600
          def name = "Europe/London"
        end.new
        Time.at(1654013280, in: zone)
        "#,
    )?;
    let err = Zoned::try_convert(custom).unwrap_err();
    assert!(err.is_kind_of(ruby.exception_type_error()), "{err}");
    assert!(
        err.to_string()
            .contains("Ruby Time timezone cannot be represented losslessly as jiff::TimeZone"),
        "{err}"
    );
    Ok(())
}

#[cfg(feature = "jiff-zoned")]
fn fixed_zones_use_native_ruby_offsets(ruby: &Ruby) -> Result<(), Error> {
    let zone: Value = ruby.eval("Timezone.fixed(19800)")?;
    // 1970-01-01 00:00:00 UTC
    let time: Value = magnus::eval!(ruby, "Time.at(0, in: zone)", zone)?;
    rb_assert!(
        ruby,
        "zone.frozen? && zone.to_s == '+05:30' && \
         t.utc_offset == 19800 && t.zone.equal?(zone)",
        zone,
        t = time,
    );
    assert_eq!(Zoned::try_convert(time)?.offset().seconds(), 19_800);
    rb_assert!(ruby, "zone.iana_name.nil?", zone);
    let err = zone.funcall::<_, _, String>("name", ()).unwrap_err();
    assert!(err.is_kind_of(ruby.exception_type_error()), "{err}");
    let err = ruby.eval::<Value>("Timezone.fixed(100000)").unwrap_err();
    assert!(err.is_kind_of(ruby.exception_arg_error()), "{err}");

    // 2022-05-31 16:08:00 UTC
    let fixed: Value = ruby.eval("Time.at(1654013280, 123456789, :nsec, in: '+05:30')")?;
    let expected = Zoned::try_convert(fixed)?;
    assert_eq!(expected.offset().seconds(), 19_800);
    assert_eq!(expected.time_zone().iana_name(), None);
    let time = expected.clone().into_value_with(ruby);
    assert_eq!(Zoned::try_convert(time)?, expected);
    rb_assert!(
        ruby,
        "t.utc_offset == 19800 && t.nsec == 123456789 && t.zone.nil?",
        t = time
    );
    for seconds in [-86_399, 86_399] {
        let offset = Offset::from_seconds(seconds).unwrap();
        // 1970-01-01 00:00:00 UTC
        let expected = Zoned::new(Timestamp::UNIX_EPOCH, TimeZone::fixed(offset));
        let time = expected.clone().into_value_with(ruby);
        assert_eq!(Zoned::try_convert(time)?, expected);
        rb_assert!(
            ruby,
            "t.utc_offset == offset && !t.utc? && t.zone.nil?",
            t = time,
            offset = seconds,
        );
    }
    // 1970-01-01 00:00:00 UTC
    for offset in [Offset::MIN, Offset::MAX] {
        // 1970-01-01 00:00:00 UTC
        let time = Zoned::new(Timestamp::UNIX_EPOCH, TimeZone::fixed(offset)).into_value_with(ruby);
        rb_assert!(ruby, "t.utc? && t.to_i == 0", t = time);
    }
    Ok(())
}

#[cfg(feature = "jiff-zoned")]
fn local_construction_resolves_civil_time(ruby: &Ruby) -> Result<(), Error> {
    let zone: Value = ruby.eval("Timezone.find_timezone('America/New_York')")?;
    let local: Value = ruby.class_time().funcall(
        "new",
        (2024, 1, 11, 2, 30, 0, magnus::kwargs!(ruby, "in" => zone)),
    )?;
    rb_assert!(
        ruby,
        "t == Time.utc(2024, 1, 11, 7, 30) && t.hour == 2 && \
         t.utc_offset == -18000 && !t.dst?",
        t = local,
    );
    assert_eq!(
        Zoned::try_convert(local)?.time_zone().iana_name(),
        Some("America/New_York")
    );
    let named: Value = ruby.eval("Time.new(2024, 1, 11, 2, 30, 0, in: 'America/New_York')")?;
    assert_eq!(Zoned::try_convert(named)?, Zoned::try_convert(local)?);
    let after_gap: Value = ruby.eval("Time.new(2024, 3, 10, 3, 30, 0, in: 'America/New_York')")?;
    rb_assert!(
        ruby,
        "t == Time.utc(2024, 3, 10, 7, 30) && t.utc_offset == -14400 && t.dst?",
        t = after_gap,
    );
    let subsecond: Value = ruby.eval(
        "Time.new(2024, 1, 11, 2, 30, 123456789/1000000000r, \
         in: 'America/New_York')",
    )?;
    rb_assert!(ruby, "t.nsec == 123456789", t = subsecond);
    Ok(())
}

#[cfg(feature = "jiff-zoned")]
fn local_construction_rejects_gaps_and_folds(ruby: &Ruby) -> Result<(), Error> {
    for code in [
        "Time.new(2024, 3, 10, 2, 30, 0, in: 'America/New_York')",
        "Time.new(2024, 11, 3, 1, 30, 0, in: 'America/New_York')",
    ] {
        let err = ruby.eval::<Value>(code).unwrap_err();
        assert!(err.is_kind_of(ruby.exception_arg_error()), "{code}: {err}");
    }
    Ok(())
}

#[cfg(feature = "jiff-zoned")]
fn local_construction_rejects_out_of_range_instants(ruby: &Ruby) -> Result<(), Error> {
    // A provisional civil timestamp or its resolved instant can fall
    // outside Jiff's supported range even if the other is representable.
    for code in [
        "Time.new(-9999, 1, 1, 12, 0, 0, in: Timezone.fixed(-72000))",
        "Time.new(-9999, 1, 2, 2, 0, 0, in: Timezone.fixed(72000))",
    ] {
        let err = ruby.eval::<Value>(code).unwrap_err();
        assert!(err.is_kind_of(ruby.exception_arg_error()), "{code}: {err}");
    }
    for year in [10000, -10000, 999999999] {
        let code = format!("Time.new({year}, 1, 1, in: Timezone.utc)");
        let err = ruby.eval::<Value>(&code).unwrap_err();
        assert!(err.is_kind_of(ruby.exception_arg_error()), "{code}: {err}");
    }
    Ok(())
}

#[cfg(feature = "jiff-zoned")]
fn named_time_survives_marshal(ruby: &Ruby) -> Result<(), Error> {
    // 2024-01-11 02:46:44 UTC
    let named = Zoned::new(
        Timestamp::new(1_704_941_204, 123_456_789).unwrap(),
        TimeZone::get("America/New_York").unwrap(),
    )
    .into_value_with(ruby);
    let marshal: Value = ruby.eval("Marshal")?;
    let dumped: Value = marshal.funcall("dump", (named,))?;
    let loaded: Value = marshal.funcall("load", (dumped,))?;
    assert_eq!(Zoned::try_convert(loaded)?, Zoned::try_convert(named)?);
    rb_assert!(
        ruby,
        "loaded.zone.name == 'America/New_York' && loaded.nsec == named.nsec",
        loaded,
        named,
    );
    Ok(())
}

#[cfg(feature = "jiff-zoned")]
fn fixed_time_survives_marshal(ruby: &Ruby) -> Result<(), Error> {
    // 2022-05-31 16:08:00 UTC
    // 2022-05-31 16:08:00 UTC
    let loaded: Value = ruby
        .eval("Marshal.load(Marshal.dump(Time.at(1654013280, 123456789, :nsec, in: '+05:30')))")?;
    let expected = Zoned::new(
        Timestamp::new(1_654_013_280, 123_456_789).unwrap(),
        TimeZone::fixed(Offset::from_seconds(19_800).unwrap()),
    );
    assert_eq!(Zoned::try_convert(loaded)?, expected);
    Ok(())
}

#[cfg(feature = "jiff-zoned")]
fn named_zone_round_trips_with_seasonal_offsets_and_metadata(ruby: &Ruby) -> Result<(), Error> {
    let new_york = TimeZone::get("America/New_York").unwrap();
    // 2024-07-09 02:46:44 UTC and 2024-01-11 02:46:44 UTC.
    for (seconds, offset, abbreviation, dst) in [
        (1_720_493_204, -14_400, "EDT", true),
        (1_704_941_204, -18_000, "EST", false),
    ] {
        let expected = Zoned::new(
            Timestamp::new(seconds, 123_456_789).unwrap(),
            new_york.clone(),
        );
        let time = expected.clone().into_value_with(ruby);
        assert_eq!(Zoned::try_convert(time)?, expected);
        rb_assert!(
            ruby,
            "t.utc_offset == offset && t.strftime('%Z') == abbreviation && \
             t.dst? == dst && t.nsec == 123456789",
            t = time,
            offset,
            abbreviation,
            dst,
        );
    }
    // 1970-01-01 00:00:00 UTC
    let time = Zoned::new(Timestamp::UNIX_EPOCH, new_york).into_value_with(ruby);
    let zone: Value = time.funcall("zone", ())?;
    rb_assert!(
        ruby,
        "zone.frozen? && zone.name == 'America/New_York' && \
         zone.iana_name == 'America/New_York' && \
         zone.to_s == 'America/New_York' && zone.class == Timezone",
        zone,
    );
    assert!(!zone.respond_to("to_str", false)?);
    Ok(())
}

#[cfg(feature = "jiff-zoned")]
fn posix_zone_observes_rules_in_both_conversion_directions(ruby: &Ruby) -> Result<(), Error> {
    let zone: Value = ruby.eval("Timezone.posix('EST5EDT,M3.2.0,M11.1.0')")?;
    rb_assert!(ruby, "zone.frozen? && zone.to_s == 'Jiff timezone'", zone);
    rb_assert!(ruby, "zone.iana_name.nil?", zone);
    rb_assert!(ruby, "zone.name rescue TypeError", zone);
    let err = ruby
        .eval::<Value>("Timezone.posix('not a POSIX rule')")
        .unwrap_err();
    assert!(err.is_kind_of(ruby.exception_arg_error()), "{err}");

    let winter: Value =
        ruby.eval("Time.new(2024, 1, 1, 12, 0, 0, in: Timezone.posix('EST5EDT,M3.2.0,M11.1.0'))")?;
    let summer: Value = ruby
        .class_time()
        .funcall("at", (1_720_493_204, magnus::kwargs!(ruby, "in" => zone)))?;
    rb_assert!(
        ruby,
        "winter.utc_offset == -18000 && !winter.dst? && \
         summer.utc_offset == -14400 && summer.strftime('%Z') == 'EDT' && summer.dst?",
        winter,
        summer,
    );
    let posix = TimeZone::posix("EST5EDT,M3.2.0,M11.1.0").unwrap();
    let from_ruby: Value = ruby.eval(
        "Time.new(2024, 7, 1, 12, 0, 0, \
         in: Timezone.posix('EST5EDT,M3.2.0,M11.1.0'))",
    )?;
    let converted = Zoned::try_convert(from_ruby)?;
    assert_eq!(
        converted.timestamp(),
        "2024-07-01T16:00:00Z".parse::<Timestamp>().unwrap()
    );
    assert_eq!(converted.time_zone(), &posix);

    for (instant, offset, abbreviation, dst) in [
        ("2024-01-01T12:00:00Z", -18_000, "EST", false),
        ("2024-07-01T12:00:00Z", -14_400, "EDT", true),
    ] {
        let expected = Zoned::new(instant.parse::<Timestamp>().unwrap(), posix.clone());
        let time = expected.clone().into_value_with(ruby);
        assert_eq!(Zoned::try_convert(time)?, expected);
        rb_assert!(
            ruby,
            "t.zone.instance_of?(Timezone) && t.utc_offset == offset && \
             t.strftime('%Z') == abbreviation && t.dst? == dst",
            t = time,
            offset,
            abbreviation,
            dst,
        );
    }
    Ok(())
}

#[cfg(feature = "jiff-zoned")]
fn timezone_find_returns_named_zone_and_timestamp(ruby: &Ruby) -> Result<(), Error> {
    let time_class = ruby.class_time();
    assert!(!ruby.eval::<bool>("Timezone.respond_to?(:get)")?);
    let exposed: Value = ruby.eval("Timezone.find_timezone('America/New_York')")?;
    rb_assert!(
        ruby,
        "zone.frozen? && zone.name == 'America/New_York' && \
         zone.iana_name == 'America/New_York'",
        zone = exposed,
    );
    // 2024-01-11 02:46:44 UTC
    let time: Value = time_class.funcall(
        "at",
        (1_704_941_204, magnus::kwargs!(ruby, "in" => exposed)),
    )?;
    assert_eq!(
        Zoned::try_convert(time)?.time_zone().iana_name(),
        Some("America/New_York")
    );
    assert_eq!(
        Timestamp::try_convert(time)?,
        Timestamp::new(1_704_941_204, 0).unwrap()
    );
    // 2024-01-11 02:46:44 UTC
    let fractional: Value =
        ruby.eval("Time.at(1704941204, 123456789, :nsec, in: 'America/New_York')")?;
    assert_eq!(
        Timestamp::try_convert(fractional)?,
        Timestamp::new(1_704_941_204, 123_456_789).unwrap()
    );
    let err = ruby.eval::<Value>("Timezone.new").unwrap_err();
    assert!(err.is_kind_of(ruby.exception_type_error()), "{err}");
    Ok(())
}

#[cfg(feature = "jiff-zoned")]
fn resolver_parses_time_subclass(ruby: &Ruby) -> Result<(), Error> {
    ruby.eval::<Value>(
        "class TimeWithTimezone < Time; \
         def self.find_timezone(z) = Timezone.find_timezone(z); end",
    )?;
    let parsed: Value = ruby.eval("TimeWithTimezone.new('2023-12-25 America/New_York')")?;
    rb_assert!(
        ruby,
        "t.to_s == '2023-12-25 00:00:00 -0500' && \
         t == Time.utc(2023, 12, 25, 5) && t.zone.name == 'America/New_York'",
        t = parsed,
    );
    assert_eq!(
        Zoned::try_convert(parsed)?.time_zone().iana_name(),
        Some("America/New_York")
    );
    Ok(())
}

#[cfg(feature = "jiff-zoned")]
fn resolver_finds_named_zones_for_ruby_time(ruby: &Ruby) -> Result<(), Error> {
    let time_class = ruby.class_time();
    let timezone_class: magnus::RClass = ruby.eval("Timezone")?;
    let instant = 1_704_067_200; // 2024-01-01 00:00:00 UTC
    for (name, year, month, day, hour, offset) in [
        ("America/New_York", 2023, 12, 31, 19, -18_000),
        ("Asia/Tokyo", 2024, 1, 1, 9, 32_400),
    ] {
        let on_time: Value = time_class.funcall("find_timezone", (name,))?;
        let on_timezone: Value = timezone_class.funcall("find_timezone", (name,))?;
        for zone in [on_time, on_timezone] {
            rb_assert!(
                ruby,
                "zone.instance_of?(Timezone) && zone.name == name",
                zone,
                name
            );
            // 2024-01-01 00:00:00 UTC
            let from_instant: Value =
                magnus::eval!(ruby, "Time.at(instant, in: zone)", instant, zone)?;
            rb_assert!(
                ruby,
                "t.to_i == instant && t.utc_offset == offset && \
                 t.year == year && t.month == month && t.day == day && \
                 t.hour == hour && t.zone.equal?(zone)",
                t = from_instant,
                instant,
                offset,
                year,
                month,
                day,
                hour,
                zone,
            );
            assert_eq!(
                Zoned::try_convert(from_instant)?.time_zone().iana_name(),
                Some(name)
            );
            let from_local: Value = magnus::eval!(
                ruby,
                "Time.new(year, month, day, hour, 0, 0, in: zone)",
                year,
                month,
                day,
                hour,
                zone
            )?;
            rb_assert!(
                ruby,
                "t.to_i == instant && t.utc_offset == offset && t.zone.equal?(zone)",
                t = from_local,
                instant,
                offset,
                zone,
            );
        }
        let from_name: Value = ruby.eval(&format!("Time.at({instant}, in: '{name}')"))?;
        rb_assert!(
            ruby,
            "t.zone.instance_of?(Timezone) && t.zone.name == name && \
             t.to_i == instant && t.utc_offset == offset",
            t = from_name,
            name,
            instant,
            offset,
        );
    }
    // 2024-01-11 02:46:44 UTC
    let time: Value = ruby.eval("Time.at(1704941204).getlocal('America/New_York')")?;
    let zoned = Zoned::try_convert(time)?;
    assert_eq!(zoned.time_zone().iana_name(), Some("America/New_York"));
    assert_eq!(zoned.offset().seconds(), -18_000);
    rb_assert!(
        ruby,
        "Time.find_timezone('Not/A_Zone').nil? && \
         Timezone.find_timezone('Not/A_Zone').nil?"
    );
    Ok(())
}

#[cfg(feature = "jiff-zoned")]
fn unknown_zone_remains_distinct_from_utc(ruby: &Ruby) -> Result<(), Error> {
    let unknown: Value = ruby.eval("Timezone.unknown")?;
    rb_assert!(
        ruby,
        "unknown.frozen? && unknown.to_s == 'Etc/Unknown' && unknown.iana_name.nil? && \
         Time.at(0, in: unknown).zone.equal?(unknown) && \
         Time.at(0, in: unknown).strftime('%Z') == 'UTC' && \
         !Time.at(0, in: unknown).dst?",
        unknown,
    );
    rb_assert!(ruby, "unknown.name rescue TypeError", unknown);

    // 1970-01-01 00:00:00 UTC
    let expected = Zoned::new(Timestamp::UNIX_EPOCH, TimeZone::unknown());
    let time = expected.clone().into_value_with(ruby);
    assert_eq!(Zoned::try_convert(time)?, expected);
    rb_assert!(
        ruby,
        "t.utc_offset == 0 && !t.utc? && !t.zone.nil?",
        t = time
    );
    Ok(())
}

#[cfg(feature = "jiff-zoned")]
fn utc_zone_round_trips(ruby: &Ruby) -> Result<(), Error> {
    let utc: Value = ruby.eval("Timezone.utc")?;
    rb_assert!(
        ruby,
        "utc.frozen? && utc.to_s == 'UTC' && utc.iana_name == 'UTC' && Time.at(0, in: utc).utc_offset == 0",
        utc
    );
    // 2022-05-31 16:08:00 UTC
    let time: Value = ruby.eval("Time.at(1654013280, in: 'UTC')")?;
    let expected = Zoned::try_convert(time)?;
    assert_eq!(expected.time_zone(), &TimeZone::UTC);
    let time = expected.clone().into_value_with(ruby);
    assert_eq!(Zoned::try_convert(time)?, expected);
    rb_assert!(ruby, "t.utc? && t.zone == 'UTC'", t = time);
    Ok(())
}
