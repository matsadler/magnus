//! Implementation of standard traits like Add, Sub, etc. for the Integer struct

use crate::{integer::IntegerType, value::private::ReprValue, Integer};
use std::ops::{Add, Div, Mul, Sub};

impl PartialEq for Integer {
    fn eq(&self, other: &Self) -> bool {
        match (self.integer_type(), other.integer_type()) {
            (IntegerType::Fixnum(a), IntegerType::Fixnum(b)) => a.as_rb_value() == b.as_rb_value(),
            (IntegerType::Bignum(a), IntegerType::Bignum(b)) => unsafe {
                rb_sys::rb_big_eq(a.as_rb_value(), b.as_rb_value()) == rb_sys::Qtrue.into()
            },
            (IntegerType::Fixnum(a), IntegerType::Bignum(b)) => unsafe {
                let a = rb_sys::rb_int2big(a.to_isize());
                rb_sys::rb_big_eq(a, b.as_rb_value()) == rb_sys::Qtrue.into()
            },
            (IntegerType::Bignum(a), IntegerType::Fixnum(b)) => unsafe {
                rb_sys::rb_big_eq(a.as_rb_value(), b.as_rb_value()) == rb_sys::Qtrue.into()
            },
        }
    }
}

impl PartialEq<i64> for Integer {
    fn eq(&self, other: &i64) -> bool {
        self.eq(&Integer::from_i64(*other))
    }
}

impl PartialEq<Integer> for i64 {
    fn eq(&self, other: &Integer) -> bool {
        Integer::from_i64(*self).eq(other)
    }
}

impl PartialOrd for Integer {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self.integer_type(), other.integer_type()) {
            (IntegerType::Fixnum(a), IntegerType::Fixnum(b)) => {
                (a.as_rb_value() as i64).partial_cmp(&(b.as_rb_value() as i64))
            }
            (IntegerType::Bignum(a), IntegerType::Bignum(b)) => unsafe {
                let result = rb_sys::rb_big_cmp(a.as_rb_value(), b.as_rb_value());
                Integer::from_rb_value_unchecked(result)
                    .to_i8()
                    .unwrap()
                    .partial_cmp(&0)
            },
            (IntegerType::Fixnum(a), IntegerType::Bignum(b)) => unsafe {
                let a = rb_sys::rb_int2big(a.to_isize());
                let result = rb_sys::rb_big_cmp(a, b.as_rb_value());
                Integer::from_rb_value_unchecked(result)
                    .to_i8()
                    .unwrap()
                    .partial_cmp(&0)
            },
            (IntegerType::Bignum(a), IntegerType::Fixnum(b)) => unsafe {
                let result = rb_sys::rb_big_cmp(a.as_rb_value(), b.as_rb_value());
                Integer::from_rb_value_unchecked(result)
                    .to_i8()
                    .unwrap()
                    .partial_cmp(&0)
            },
        }
    }
}

impl PartialOrd<i64> for Integer {
    fn partial_cmp(&self, other: &i64) -> Option<std::cmp::Ordering> {
        self.partial_cmp(&Integer::from_i64(*other))
    }
}

impl PartialOrd<Integer> for i64 {
    fn partial_cmp(&self, other: &Integer) -> Option<std::cmp::Ordering> {
        Integer::from_i64(*self).partial_cmp(other)
    }
}

impl Add for Integer {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        match (self.integer_type(), other.integer_type()) {
            (IntegerType::Fixnum(a), IntegerType::Fixnum(b)) => {
                let raw_a = a.as_rb_value() as i64;
                let raw_b = b.as_rb_value() as i64;
                let result = raw_a.checked_add(raw_b).and_then(|i| i.checked_sub(1));
                if let Some(result) = result {
                    unsafe { Integer::from_rb_value_unchecked(result as u64) }
                } else {
                    let a = unsafe { rb_sys::rb_int2big(a.to_isize()) };
                    let result = unsafe { rb_sys::rb_big_plus(a, b.as_rb_value()) };
                    unsafe { Integer::from_rb_value_unchecked(result) }
                }
            }
            (IntegerType::Bignum(a), IntegerType::Fixnum(b)) => {
                let result = unsafe { rb_sys::rb_big_plus(a.as_rb_value(), b.as_rb_value()) };
                unsafe { Integer::from_rb_value_unchecked(result) }
            }
            (IntegerType::Fixnum(a), IntegerType::Bignum(b)) => {
                let a = unsafe { rb_sys::rb_int2big(a.to_isize()) };
                let result = unsafe { rb_sys::rb_big_plus(a, b.as_rb_value()) };
                unsafe { Integer::from_rb_value_unchecked(result) }
            }
            (IntegerType::Bignum(a), IntegerType::Bignum(b)) => {
                let result = unsafe { rb_sys::rb_big_plus(a.as_rb_value(), b.as_rb_value()) };
                unsafe { Integer::from_rb_value_unchecked(result) }
            }
        }
    }
}

impl Add<i64> for Integer {
    type Output = Self;

    fn add(self, other: i64) -> Self {
        self + Integer::from_i64(other)
    }
}

impl Add<Integer> for i64 {
    type Output = Integer;

    fn add(self, other: Integer) -> Integer {
        Integer::from_i64(self) + other
    }
}

impl Sub for Integer {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        match (self.integer_type(), other.integer_type()) {
            (IntegerType::Fixnum(a), IntegerType::Fixnum(b)) => {
                let raw_a = a.as_rb_value() as i64;
                let raw_b = b.as_rb_value() as i64;
                let result = raw_a.checked_sub(raw_b).and_then(|i| i.checked_add(1));
                if let Some(result) = result {
                    unsafe { Integer::from_rb_value_unchecked(result as u64) }
                } else {
                    let a = unsafe { rb_sys::rb_int2big(a.to_isize()) };
                    let result = unsafe { rb_sys::rb_big_minus(a, b.as_rb_value()) };
                    unsafe { Integer::from_rb_value_unchecked(result) }
                }
            }
            (IntegerType::Bignum(a), IntegerType::Fixnum(b)) => {
                let result = unsafe { rb_sys::rb_big_minus(a.as_rb_value(), b.as_rb_value()) };
                unsafe { Integer::from_rb_value_unchecked(result) }
            }
            (IntegerType::Fixnum(a), IntegerType::Bignum(b)) => {
                let a = unsafe { rb_sys::rb_int2big(a.to_isize()) };
                let result = unsafe { rb_sys::rb_big_minus(a, b.as_rb_value()) };
                unsafe { Integer::from_rb_value_unchecked(result) }
            }
            (IntegerType::Bignum(a), IntegerType::Bignum(b)) => {
                let result = unsafe { rb_sys::rb_big_minus(a.as_rb_value(), b.as_rb_value()) };
                unsafe { Integer::from_rb_value_unchecked(result) }
            }
        }
    }
}

impl Sub<i64> for Integer {
    type Output = Self;

    fn sub(self, other: i64) -> Self {
        self - Integer::from_i64(other)
    }
}

impl Sub<Integer> for i64 {
    type Output = Integer;

    fn sub(self, other: Integer) -> Integer {
        Integer::from_i64(self) - other
    }
}

impl Mul for Integer {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        match (self.integer_type(), other.integer_type()) {
            (IntegerType::Fixnum(a), IntegerType::Fixnum(b)) => {
                let raw_a = a.to_i64();
                let raw_b = b.to_i64();
                let result = raw_a.checked_mul(raw_b);
                if let Some(result) = result {
                    Integer::from_i64(result)
                } else {
                    let a = unsafe { rb_sys::rb_int2big(a.to_isize()) };
                    let result = unsafe { rb_sys::rb_big_mul(a, b.as_rb_value()) };
                    unsafe { Integer::from_rb_value_unchecked(result) }
                }
            }
            (IntegerType::Bignum(a), IntegerType::Fixnum(b)) => {
                let result = unsafe { rb_sys::rb_big_mul(a.as_rb_value(), b.as_rb_value()) };
                unsafe { Integer::from_rb_value_unchecked(result) }
            }
            (IntegerType::Fixnum(a), IntegerType::Bignum(b)) => {
                let a = unsafe { rb_sys::rb_int2big(a.to_isize()) };
                let result = unsafe { rb_sys::rb_big_mul(a, b.as_rb_value()) };
                unsafe { Integer::from_rb_value_unchecked(result) }
            }
            (IntegerType::Bignum(a), IntegerType::Bignum(b)) => {
                let result = unsafe { rb_sys::rb_big_mul(a.as_rb_value(), b.as_rb_value()) };
                unsafe { Integer::from_rb_value_unchecked(result) }
            }
        }
    }
}

impl Mul<i64> for Integer {
    type Output = Self;

    fn mul(self, other: i64) -> Self {
        self * Integer::from_i64(other)
    }
}

impl Mul<Integer> for i64 {
    type Output = Integer;

    fn mul(self, other: Integer) -> Integer {
        Integer::from_i64(self) * other
    }
}

impl Div for Integer {
    type Output = Self;

    fn div(self, other: Self) -> Self {
        match (self.integer_type(), other.integer_type()) {
            (IntegerType::Fixnum(a), IntegerType::Fixnum(b)) => {
                let raw_a = a.to_i64();
                let raw_b = b.to_i64();
                // the only case when division can overflow is when dividing
                // i64::MIN by -1, but Fixnum can't represent that I64::MIN
                // so we can safely not use checked_div here
                Integer::from_i64(raw_a / raw_b)
            }
            (IntegerType::Bignum(a), IntegerType::Fixnum(b)) => {
                let result = unsafe { rb_sys::rb_big_div(a.as_rb_value(), b.as_rb_value()) };
                unsafe { Integer::from_rb_value_unchecked(result) }
            }
            (IntegerType::Fixnum(a), IntegerType::Bignum(b)) => {
                let a = unsafe { rb_sys::rb_int2big(a.to_isize()) };
                let result = unsafe { rb_sys::rb_big_div(a, b.as_rb_value()) };
                unsafe { Integer::from_rb_value_unchecked(result) }
            }
            (IntegerType::Bignum(a), IntegerType::Bignum(b)) => {
                let result = unsafe { rb_sys::rb_big_div(a.as_rb_value(), b.as_rb_value()) };
                unsafe { Integer::from_rb_value_unchecked(result) }
            }
        }
    }
}

impl Div<i64> for Integer {
    type Output = Self;

    fn div(self, other: i64) -> Self {
        self / Integer::from_i64(other)
    }
}

impl Div<Integer> for i64 {
    type Output = Integer;

    fn div(self, other: Integer) -> Integer {
        Integer::from_i64(self) / other
    }
}

#[cfg(test)]
mod tests {
    use crate::eval;

    use super::*;

    #[test]
    fn test_all() {
        let _cleanup = unsafe { magnus::embed::init() };
        test_add();
        test_add_with_i64();
        test_sub();
        test_sub_with_i64();
        test_mul();
        test_mul_with_i64();
        test_div();
        test_div_with_i64();
        test_ord();
        test_ord_with_i64();
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
            Integer::from_u64(rb_sys::RUBY_FIXNUM_MAX) + Integer::from_i64(1),
            Integer::from_u64(rb_sys::RUBY_FIXNUM_MAX + 1)
        );
        assert_eq!(
            Integer::from_i64(rb_sys::RUBY_FIXNUM_MIN) + Integer::from_i64(-1),
            Integer::from_i64(rb_sys::RUBY_FIXNUM_MIN - 1)
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
    }

    fn test_add_with_i64() {
        assert!(Integer::from_i64(1) + 2 == Integer::from_i64(3));
        assert!(1 + Integer::from_i64(2) == Integer::from_i64(3));
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
            Integer::from_u64(rb_sys::RUBY_FIXNUM_MAX) - Integer::from_i64(-1),
            Integer::from_u64(rb_sys::RUBY_FIXNUM_MAX + 1)
        );
        assert_eq!(
            Integer::from_i64(rb_sys::RUBY_FIXNUM_MIN) - Integer::from_i64(1),
            Integer::from_i64(rb_sys::RUBY_FIXNUM_MIN - 1)
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
    }

    fn test_sub_with_i64() {
        assert!(Integer::from_i64(1) - 2 == Integer::from_i64(-1));
        assert!(1 - Integer::from_i64(2) == Integer::from_i64(-1));
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
            Integer::from_u64(rb_sys::RUBY_FIXNUM_MAX) * Integer::from_i64(4),
            Integer::from_value(eval(&format!("{} * 4", rb_sys::RUBY_FIXNUM_MAX)).unwrap())
                .unwrap()
        );
        assert_eq!(
            Integer::from_i64(rb_sys::RUBY_FIXNUM_MIN) * Integer::from_i64(4),
            Integer::from_value(eval(&format!("{} * 4", rb_sys::RUBY_FIXNUM_MIN)).unwrap())
                .unwrap()
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
    }

    fn test_mul_with_i64() {
        assert!(Integer::from_i64(1) * 2 == Integer::from_i64(2));
        assert!(1 * Integer::from_i64(2) == Integer::from_i64(2));
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
    }

    fn test_div_with_i64() {
        assert!(Integer::from_i64(4) / 2 == Integer::from_i64(2));
        assert!(4 / Integer::from_i64(2) == Integer::from_i64(2));
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

    fn test_ord_with_i64() {
        assert!(Integer::from_i64(1) < 2);
        assert!(Integer::from_i64(2) > 1);
        assert!(Integer::from_i64(1) == 1);
        assert!(1 < Integer::from_i64(2));
        assert!(2 > Integer::from_i64(1));
        assert!(1 == Integer::from_i64(1));

        let a = Integer::from_value(eval("2**1000").unwrap()).unwrap();
        assert!(a > 1);
        assert!(1 < a);
    }
}
