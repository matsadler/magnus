use std::os::raw::c_long;

use magnus::{eval, Error, Integer, Ruby};

const RUBY_FIXNUM_MAX: u64 = (c_long::MAX / 2) as u64;
const RUBY_FIXNUM_MIN: i64 = (c_long::MIN / 2) as i64;

#[test]
fn test_all() {
    magnus::Ruby::init(|ruby| {
        test_add(ruby)?;
        test_sub(ruby)?;
        test_mul(ruby)?;
        test_div(ruby)?;
        test_ord(ruby)?;
        Ok(())
    })
    .unwrap();
}

fn test_add(ruby: &Ruby) -> Result<(), Error> {
    assert_eq!(
        ruby.integer_from_i64(1) + ruby.integer_from_i64(2),
        ruby.integer_from_i64(3)
    );
    assert_eq!(
        ruby.integer_from_i64(-1) + ruby.integer_from_i64(-2),
        ruby.integer_from_i64(-3)
    );
    assert_eq!(
        ruby.integer_from_i64(1) + ruby.integer_from_i64(-2),
        ruby.integer_from_i64(-1)
    );
    assert_eq!(
        ruby.integer_from_i64(-1) + ruby.integer_from_i64(2),
        ruby.integer_from_i64(1)
    );
    assert_eq!(
        ruby.integer_from_u64(RUBY_FIXNUM_MAX) + ruby.integer_from_i64(1),
        ruby.integer_from_u64(RUBY_FIXNUM_MAX + 1)
    );
    assert_eq!(
        ruby.integer_from_i64(RUBY_FIXNUM_MIN) + ruby.integer_from_i64(-1),
        ruby.integer_from_i64(RUBY_FIXNUM_MIN - 1)
    );
    let a: Integer = ruby.eval("2**1000")?;
    let b: Integer = ruby.eval("2**1000")?;
    let a_b: Integer = ruby.eval("2**1000 + 2**1000")?;
    assert_eq!(a + b, a_b);

    let a: Integer = ruby.eval("2**1000")?;
    let b = ruby.integer_from_i64(1);
    let a_b: Integer = ruby.eval("2**1000 + 1")?;
    assert_eq!(a + b, a_b);

    let a = ruby.integer_from_i64(1);
    let b: Integer = ruby.eval("2**1000")?;
    let a_b: Integer = ruby.eval("2**1000 + 1")?;
    assert_eq!(a + b, a_b);

    let mut a = ruby.integer_from_i64(1);
    a += ruby.integer_from_i64(1);
    assert_eq!(a, ruby.integer_from_i64(2));

    Ok(())
}

fn test_sub(ruby: &Ruby) -> Result<(), Error> {
    assert_eq!(
        ruby.integer_from_i64(1) - ruby.integer_from_i64(2),
        ruby.integer_from_i64(-1)
    );
    assert_eq!(
        ruby.integer_from_i64(-1) - ruby.integer_from_i64(-2),
        ruby.integer_from_i64(1)
    );
    assert_eq!(
        ruby.integer_from_i64(1) - ruby.integer_from_i64(-2),
        ruby.integer_from_i64(3)
    );
    assert_eq!(
        ruby.integer_from_i64(-1) - ruby.integer_from_i64(2),
        ruby.integer_from_i64(-3)
    );
    assert_eq!(
        ruby.integer_from_u64(RUBY_FIXNUM_MAX) - ruby.integer_from_i64(-1),
        ruby.integer_from_u64(RUBY_FIXNUM_MAX + 1)
    );
    assert_eq!(
        ruby.integer_from_i64(RUBY_FIXNUM_MIN) - ruby.integer_from_i64(1),
        ruby.integer_from_i64(RUBY_FIXNUM_MIN - 1)
    );
    let a: Integer = ruby.eval("2**1000")?;
    let b: Integer = ruby.eval("2**999")?;
    let a_b: Integer = ruby.eval("2**1000 - 2**999")?;
    assert_eq!(a - b, a_b);

    let a: Integer = ruby.eval("2**1000")?;
    let b = ruby.integer_from_i64(1);
    let a_b: Integer = ruby.eval("2**1000 - 1")?;
    assert_eq!(a - b, a_b);

    let a = ruby.integer_from_i64(1);
    let b: Integer = ruby.eval("2**1000")?;
    let a_b: Integer = ruby.eval("1 - 2**1000")?;
    assert_eq!(a - b, a_b);

    let mut a = ruby.integer_from_i64(1);
    a -= ruby.integer_from_i64(1);
    assert_eq!(a, ruby.integer_from_i64(0));

    Ok(())
}

fn test_mul(ruby: &Ruby) -> Result<(), Error> {
    assert_eq!(
        ruby.integer_from_i64(1) * ruby.integer_from_i64(2),
        ruby.integer_from_i64(2)
    );
    assert_eq!(
        ruby.integer_from_i64(-1) * ruby.integer_from_i64(-2),
        ruby.integer_from_i64(2)
    );
    assert_eq!(
        ruby.integer_from_i64(1) * ruby.integer_from_i64(-2),
        ruby.integer_from_i64(-2)
    );
    assert_eq!(
        ruby.integer_from_i64(-1) * ruby.integer_from_i64(2),
        ruby.integer_from_i64(-2)
    );
    assert_eq!(
        ruby.integer_from_u64(RUBY_FIXNUM_MAX) * ruby.integer_from_i64(4),
        Integer::from_value(eval(&format!("{} * 4", RUBY_FIXNUM_MAX)).unwrap()).unwrap()
    );
    assert_eq!(
        ruby.integer_from_i64(RUBY_FIXNUM_MIN) * ruby.integer_from_i64(4),
        Integer::from_value(eval(&format!("{} * 4", RUBY_FIXNUM_MIN)).unwrap()).unwrap()
    );

    let a: Integer = ruby.eval("2**1000")?;
    let b: Integer = ruby.eval("2**999")?;
    let a_b: Integer = ruby.eval("2**1000 * 2**999")?;
    assert_eq!(a * b, a_b);

    let a: Integer = ruby.eval("2**1000")?;
    let b = ruby.integer_from_i64(2);
    let a_b: Integer = ruby.eval("2**1000 * 2")?;
    assert_eq!(a * b, a_b);

    let a = ruby.integer_from_i64(2);
    let b: Integer = ruby.eval("2**1000")?;
    let a_b: Integer = ruby.eval("2 * 2**1000")?;
    assert_eq!(a * b, a_b);

    let mut a = ruby.integer_from_i64(1);
    a *= ruby.integer_from_i64(2);
    assert_eq!(a, ruby.integer_from_i64(2));

    Ok(())
}

fn test_div(ruby: &Ruby) -> Result<(), Error> {
    assert_eq!(
        ruby.integer_from_i64(1) / ruby.integer_from_i64(2),
        ruby.integer_from_i64(0)
    );
    assert_eq!(
        ruby.integer_from_i64(-4) / ruby.integer_from_i64(2),
        ruby.integer_from_i64(-2)
    );
    assert_eq!(
        ruby.integer_from_i64(7) / ruby.integer_from_i64(2),
        ruby.integer_from_i64(3)
    );

    let a: Integer = ruby.eval("2**1000")?;
    let b: Integer = ruby.eval("2**999")?;
    let a_b: Integer = ruby.eval("2**1000 / 2**999")?;
    assert_eq!(a / b, a_b);

    let a: Integer = ruby.eval("2**1000")?;
    let b = ruby.integer_from_i64(2);
    let a_b: Integer = ruby.eval("2**1000 / 2")?;
    assert_eq!(a / b, a_b);

    let a = ruby.integer_from_i64(2);
    let b: Integer = ruby.eval("2**1000")?;
    let a_b: Integer = ruby.eval("2 / 2**1000")?;
    assert_eq!(a / b, a_b);

    let mut a = ruby.integer_from_i64(4);
    a /= ruby.integer_from_i64(2);
    assert_eq!(a, ruby.integer_from_i64(2));

    Ok(())
}

fn test_ord(ruby: &Ruby) -> Result<(), Error> {
    assert!(ruby.integer_from_i64(1) < ruby.integer_from_i64(2));
    assert!(ruby.integer_from_i64(2) > ruby.integer_from_i64(1));
    assert!(ruby.integer_from_i64(1) <= ruby.integer_from_i64(2));
    assert!(ruby.integer_from_i64(2) >= ruby.integer_from_i64(1));
    assert!(ruby.integer_from_i64(1) <= ruby.integer_from_i64(1));
    assert!(ruby.integer_from_i64(1) == ruby.integer_from_i64(1));
    assert!(ruby.integer_from_i64(1) >= ruby.integer_from_i64(1));
    let a: Integer = ruby.eval("2**1000")?;
    let b: Integer = ruby.eval("2**999")?;
    let c: Integer = ruby.eval("2**1000")?;
    assert!(a > b);
    assert!(a >= b);
    assert!(b < a);
    assert!(b <= a);
    assert!(a == c);
    assert!(a >= c);
    assert!(a <= c);
    assert!(a > ruby.integer_from_i64(1));
    assert!(a >= ruby.integer_from_i64(1));
    assert!(ruby.integer_from_i64(1) < a);
    assert!(ruby.integer_from_i64(1) <= a);

    Ok(())
}
