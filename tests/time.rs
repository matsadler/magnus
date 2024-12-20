use std::time::SystemTime;

use magnus::{rb_assert, Error, Ruby};

#[test]
fn test_all() {
    magnus::Ruby::init(|ruby| {
        test_supports_system_time(ruby)?;
        #[cfg(feature = "chrono")]
        test_supports_chrono(ruby)?;
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
