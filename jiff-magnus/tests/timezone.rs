use jiff::{Timestamp, ZonedDateTime, tz::TimeZone};
use jiff_magnus::{init, register};
use magnus::{Error, IntoValue, Ruby, TryConvert, Value, prelude::*, rb_assert};

// Core owns conversions and timezone protocol details. These cases exercise
// the companion's constructors, resolver, and public class with native conversion.
#[test]
fn test_all() {
    Ruby::init(|ruby| {
        init(ruby)?;
        register(ruby)?;
        test_local_construction_resolves_civil_time(ruby)?;
        test_named_time_survives_marshal(ruby)?;
        test_outgoing_conversion_uses_companion_class(ruby)?;
        test_posix_zone_observes_rules_in_both_conversion_directions(ruby)?;
        test_resolver_parses_time_subclass(ruby)?;
        test_resolver_finds_named_zones_for_ruby_time(ruby)?;
        Ok(())
    })
    .unwrap();
}

fn test_local_construction_resolves_civil_time(ruby: &Ruby) -> Result<(), Error> {
    let zone: Value = ruby.eval("JiffTimezone.find_timezone('America/New_York')")?;
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
        ZonedDateTime::try_convert(local)?.time_zone().iana_name(),
        Some("America/New_York")
    );
    let named: Value = ruby.eval("Time.new(2024, 1, 11, 2, 30, 0, in: 'America/New_York')")?;
    let named = ZonedDateTime::try_convert(named)?;
    let expected = ZonedDateTime::try_convert(local)?;
    assert_eq!(named, expected);
    assert_eq!(named.time_zone(), expected.time_zone());
    let after_gap: Value = ruby.eval("Time.new(2024, 3, 10, 3, 30, 0, in: 'America/New_York')")?;
    rb_assert!(
        ruby,
        "t == Time.utc(2024, 3, 10, 7, 30) && t.utc_offset == -14400 && t.dst?",
        t = after_gap,
    );
    Ok(())
}

fn test_named_time_survives_marshal(ruby: &Ruby) -> Result<(), Error> {
    let named = ZonedDateTime::new(
        Timestamp::new(1_704_941_204, 123_456_789).unwrap(),
        TimeZone::get("America/New_York").unwrap(),
    )
    .into_value_with(ruby);
    let marshal: Value = ruby.eval("Marshal")?;
    let dumped: Value = marshal.funcall("dump", (named,))?;
    let loaded: Value = marshal.funcall("load", (dumped,))?;
    let expected = ZonedDateTime::try_convert(named)?;
    let actual = ZonedDateTime::try_convert(loaded)?;
    assert_eq!(actual, expected);
    assert_eq!(actual.time_zone(), expected.time_zone());
    rb_assert!(
        ruby,
        "loaded.zone.name == 'America/New_York' && loaded.nsec == named.nsec",
        loaded,
        named,
    );
    Ok(())
}

fn test_outgoing_conversion_uses_companion_class(ruby: &Ruby) -> Result<(), Error> {
    let time = ZonedDateTime::new(
        Timestamp::UNIX_EPOCH,
        TimeZone::get("America/New_York").unwrap(),
    )
    .into_value_with(ruby);
    let zone: Value = time.funcall("zone", ())?;
    rb_assert!(
        ruby,
        "zone.instance_of?(JiffTimezone) && zone.name == 'America/New_York' && \
         zone.inspect.include?('representation=\"America/New_York\"')",
        zone,
    );
    assert!(!zone.respond_to("to_str", false)?);
    Ok(())
}

fn test_posix_zone_observes_rules_in_both_conversion_directions(ruby: &Ruby) -> Result<(), Error> {
    let posix = TimeZone::posix("EST5EDT,M3.2.0,M11.1.0").unwrap();
    let from_ruby: Value = ruby.eval(
        "Time.new(2024, 7, 1, 12, 0, 0, \
         in: JiffTimezone.posix('EST5EDT,M3.2.0,M11.1.0'))",
    )?;
    let converted = ZonedDateTime::try_convert(from_ruby)?;
    assert_eq!(
        converted.timestamp(),
        "2024-07-01T16:00:00Z".parse::<Timestamp>().unwrap()
    );
    assert_eq!(converted.time_zone(), &posix);

    for (instant, offset, abbreviation, dst) in [
        ("2024-01-01T12:00:00Z", -18_000, "EST", false),
        ("2024-07-01T12:00:00Z", -14_400, "EDT", true),
    ] {
        let expected = ZonedDateTime::new(instant.parse::<Timestamp>().unwrap(), posix.clone());
        let time = expected.clone().into_value_with(ruby);
        let actual = ZonedDateTime::try_convert(time)?;
        assert_eq!(actual, expected);
        assert_eq!(actual.time_zone(), expected.time_zone());
        rb_assert!(
            ruby,
            "t.zone.instance_of?(JiffTimezone) && t.utc_offset == offset && \
             t.strftime('%Z') == abbreviation && t.dst? == dst",
            t = time,
            offset,
            abbreviation,
            dst,
        );
    }
    Ok(())
}

fn test_resolver_parses_time_subclass(ruby: &Ruby) -> Result<(), Error> {
    ruby.eval::<Value>(
        "class TimeWithTimezone < Time; \
         def self.find_timezone(z) = JiffTimezone.find_timezone(z); end",
    )?;
    let parsed: Value = ruby.eval("TimeWithTimezone.new('2023-12-25 America/New_York')")?;
    rb_assert!(
        ruby,
        "t.to_s == '2023-12-25 00:00:00 -0500' && \
         t == Time.utc(2023, 12, 25, 5) && t.zone.name == 'America/New_York'",
        t = parsed,
    );
    assert_eq!(
        ZonedDateTime::try_convert(parsed)?.time_zone().iana_name(),
        Some("America/New_York")
    );
    Ok(())
}

fn test_resolver_finds_named_zones_for_ruby_time(ruby: &Ruby) -> Result<(), Error> {
    let time_class = ruby.class_time();
    let timezone_class: magnus::RClass = ruby.eval("JiffTimezone")?;
    let instant = 1_704_067_200; // 2024-01-01 00:00:00 UTC
    for (name, offset) in [("America/New_York", -18_000), ("Asia/Tokyo", 32_400)] {
        let on_time: Value = time_class.funcall("find_timezone", (name,))?;
        let on_timezone: Value = timezone_class.funcall("find_timezone", (name,))?;
        for zone in [on_time, on_timezone] {
            rb_assert!(
                ruby,
                "zone.instance_of?(JiffTimezone) && zone.name == name",
                zone,
                name,
            );
            let from_instant: Value =
                magnus::eval!(ruby, "Time.at(instant, in: zone)", instant, zone)?;
            rb_assert!(
                ruby,
                "t.to_i == instant && t.utc_offset == offset && t.zone.equal?(zone)",
                t = from_instant,
                instant,
                offset,
                zone,
            );
            assert_eq!(
                ZonedDateTime::try_convert(from_instant)?
                    .time_zone()
                    .iana_name(),
                Some(name)
            );
        }
        let from_name: Value = ruby.eval(&format!("Time.at({instant}, in: '{name}')"))?;
        rb_assert!(
            ruby,
            "t.zone.instance_of?(JiffTimezone) && t.zone.name == name && \
             t.to_i == instant && t.utc_offset == offset",
            t = from_name,
            name,
            instant,
            offset,
        );
    }
    let time: Value = ruby.eval("Time.at(1704941204).getlocal('America/New_York')")?;
    let zoned = ZonedDateTime::try_convert(time)?;
    assert_eq!(zoned.time_zone().iana_name(), Some("America/New_York"));
    assert_eq!(zoned.offset().seconds(), -18_000);
    Ok(())
}
