use std::os::raw::{c_long, c_ulong};

use magnus::{eval, Integer};

const RUBY_FIXNUM_MAX: c_ulong = (c_long::MAX / 2) as c_ulong;
const RUBY_FIXNUM_MIN: c_long = c_long::MIN / 2;

#[test]
fn test_all() {
    let _cleanup = unsafe { magnus::embed::init() };
    test_add();
    test_sub();
    test_mul();
    test_div();
    test_ord();
}

fn test_add() {
    assert_eq!(
        Integer::from_i64(1) + Integer::from_i64(2),
        Integer::from_i64(3)
    );
    assert_eq!(
        Integer::from_i64(-1) + Integer::from_i64(-2),
        Integer::from_i64(-3)
    );
    assert_eq!(
        Integer::from_i64(1) + Integer::from_i64(-2),
        Integer::from_i64(-1)
    );
    assert_eq!(
        Integer::from_i64(-1) + Integer::from_i64(2),
        Integer::from_i64(1)
    );
    assert_eq!(
        Integer::from_u64(RUBY_FIXNUM_MAX) + Integer::from_i64(1),
        Integer::from_u64(RUBY_FIXNUM_MAX + 1)
    );
    assert_eq!(
        Integer::from_i64(RUBY_FIXNUM_MIN) + Integer::from_i64(-1),
        Integer::from_i64(RUBY_FIXNUM_MIN - 1)
    );
    let a = Integer::from_value(eval("2**1000").unwrap()).unwrap();
    let b = Integer::from_value(eval("2**1000").unwrap()).unwrap();
    let a_b = Integer::from_value(eval("2**1000 + 2**1000").unwrap()).unwrap();
    assert_eq!(a + b, a_b);

    let a = Integer::from_value(eval("2**1000").unwrap()).unwrap();
    let b = Integer::from_i64(1);
    let a_b = Integer::from_value(eval("2**1000 + 1").unwrap()).unwrap();
    assert_eq!(a + b, a_b);

    let a = Integer::from_i64(1);
    let b = Integer::from_value(eval("2**1000").unwrap()).unwrap();
    let a_b = Integer::from_value(eval("2**1000 + 1").unwrap()).unwrap();
    assert_eq!(a + b, a_b);

    let mut a = Integer::from_i64(1);
    a += Integer::from_i64(1);
    assert_eq!(a, Integer::from_i64(2));
}

fn test_sub() {
    assert_eq!(
        Integer::from_i64(1) - Integer::from_i64(2),
        Integer::from_i64(-1)
    );
    assert_eq!(
        Integer::from_i64(-1) - Integer::from_i64(-2),
        Integer::from_i64(1)
    );
    assert_eq!(
        Integer::from_i64(1) - Integer::from_i64(-2),
        Integer::from_i64(3)
    );
    assert_eq!(
        Integer::from_i64(-1) - Integer::from_i64(2),
        Integer::from_i64(-3)
    );
    assert_eq!(
        Integer::from_u64(RUBY_FIXNUM_MAX) - Integer::from_i64(-1),
        Integer::from_u64(RUBY_FIXNUM_MAX + 1)
    );
    assert_eq!(
        Integer::from_i64(RUBY_FIXNUM_MIN) - Integer::from_i64(1),
        Integer::from_i64(RUBY_FIXNUM_MIN - 1)
    );
    let a = Integer::from_value(eval("2**1000").unwrap()).unwrap();
    let b = Integer::from_value(eval("2**999").unwrap()).unwrap();
    let a_b = Integer::from_value(eval("2**1000 - 2**999").unwrap()).unwrap();
    assert_eq!(a - b, a_b);

    let a = Integer::from_value(eval("2**1000").unwrap()).unwrap();
    let b = Integer::from_i64(1);
    let a_b = Integer::from_value(eval("2**1000 - 1").unwrap()).unwrap();
    assert_eq!(a - b, a_b);

    let a = Integer::from_i64(1);
    let b = Integer::from_value(eval("2**1000").unwrap()).unwrap();
    let a_b = Integer::from_value(eval("1 - 2**1000").unwrap()).unwrap();
    assert_eq!(a - b, a_b);

    let mut a = Integer::from_i64(1);
    a -= Integer::from_i64(1);
    assert_eq!(a, Integer::from_i64(0));
}

fn test_mul() {
    assert_eq!(
        Integer::from_i64(1) * Integer::from_i64(2),
        Integer::from_i64(2)
    );
    assert_eq!(
        Integer::from_i64(-1) * Integer::from_i64(-2),
        Integer::from_i64(2)
    );
    assert_eq!(
        Integer::from_i64(1) * Integer::from_i64(-2),
        Integer::from_i64(-2)
    );
    assert_eq!(
        Integer::from_i64(-1) * Integer::from_i64(2),
        Integer::from_i64(-2)
    );
    assert_eq!(
        Integer::from_u64(RUBY_FIXNUM_MAX) * Integer::from_i64(4),
        Integer::from_value(eval(&format!("{} * 4", RUBY_FIXNUM_MAX)).unwrap()).unwrap()
    );
    assert_eq!(
        Integer::from_i64(RUBY_FIXNUM_MIN) * Integer::from_i64(4),
        Integer::from_value(eval(&format!("{} * 4", RUBY_FIXNUM_MIN)).unwrap()).unwrap()
    );

    let a = Integer::from_value(eval("2**1000").unwrap()).unwrap();
    let b = Integer::from_value(eval("2**999").unwrap()).unwrap();
    let a_b = Integer::from_value(eval("2**1000 * 2**999").unwrap()).unwrap();
    assert_eq!(a * b, a_b);

    let a = Integer::from_value(eval("2**1000").unwrap()).unwrap();
    let b = Integer::from_i64(2);
    let a_b = Integer::from_value(eval("2**1000 * 2").unwrap()).unwrap();
    assert_eq!(a * b, a_b);

    let a = Integer::from_i64(2);
    let b = Integer::from_value(eval("2**1000").unwrap()).unwrap();
    let a_b = Integer::from_value(eval("2 * 2**1000").unwrap()).unwrap();
    assert_eq!(a * b, a_b);

    let mut a = Integer::from_i64(1);
    a *= Integer::from_i64(2);
    assert_eq!(a, Integer::from_i64(2));
}

fn test_div() {
    assert_eq!(
        Integer::from_i64(1) / Integer::from_i64(2),
        Integer::from_i64(0)
    );
    assert_eq!(
        Integer::from_i64(-4) / Integer::from_i64(2),
        Integer::from_i64(-2)
    );
    assert_eq!(
        Integer::from_i64(7) / Integer::from_i64(2),
        Integer::from_i64(3)
    );

    let a = Integer::from_value(eval("2**1000").unwrap()).unwrap();
    let b = Integer::from_value(eval("2**999").unwrap()).unwrap();
    let a_b = Integer::from_value(eval("2**1000 / 2**999").unwrap()).unwrap();
    assert_eq!(a / b, a_b);

    let a = Integer::from_value(eval("2**1000").unwrap()).unwrap();
    let b = Integer::from_i64(2);
    let a_b = Integer::from_value(eval("2**1000 / 2").unwrap()).unwrap();
    assert_eq!(a / b, a_b);

    let a = Integer::from_i64(2);
    let b = Integer::from_value(eval("2**1000").unwrap()).unwrap();
    let a_b = Integer::from_value(eval("2 / 2**1000").unwrap()).unwrap();
    assert_eq!(a / b, a_b);

    let mut a = Integer::from_i64(4);
    a /= Integer::from_i64(2);
    assert_eq!(a, Integer::from_i64(2));
}

fn test_ord() {
    assert!(Integer::from_i64(1) < Integer::from_i64(2));
    assert!(Integer::from_i64(2) > Integer::from_i64(1));
    assert!(Integer::from_i64(1) <= Integer::from_i64(2));
    assert!(Integer::from_i64(2) >= Integer::from_i64(1));
    assert!(Integer::from_i64(1) <= Integer::from_i64(1));
    assert!(Integer::from_i64(1) == Integer::from_i64(1));
    assert!(Integer::from_i64(1) >= Integer::from_i64(1));
    let a = Integer::from_value(eval("2**1000").unwrap()).unwrap();
    let b = Integer::from_value(eval("2**999").unwrap()).unwrap();
    let c = Integer::from_value(eval("2**1000").unwrap()).unwrap();
    assert!(a > b);
    assert!(a >= b);
    assert!(b < a);
    assert!(b <= a);
    assert!(a == c);
    assert!(a >= c);
    assert!(a <= c);
    assert!(a > Integer::from_i64(1));
    assert!(a >= Integer::from_i64(1));
    assert!(Integer::from_i64(1) < a);
    assert!(Integer::from_i64(1) <= a);
}
