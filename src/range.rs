use std::ops::{Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive};

use crate::{
    error::protect,
    ruby_sys::rb_range_new,
    value::{Value, QNIL},
};

impl<T> From<Range<T>> for Value
where
    T: Into<Value>,
{
    fn from(value: Range<T>) -> Self {
        protect(|| unsafe {
            Value::new(rb_range_new(
                value.start.into().as_rb_value(),
                value.end.into().as_rb_value(),
                1,
            ))
        })
        .unwrap()
    }
}

impl<T> From<RangeFrom<T>> for Value
where
    T: Into<Value>,
{
    fn from(value: RangeFrom<T>) -> Self {
        protect(|| unsafe {
            Value::new(rb_range_new(
                value.start.into().as_rb_value(),
                QNIL.as_rb_value(),
                0,
            ))
        })
        .unwrap()
    }
}

impl From<RangeFull> for Value {
    fn from(_: RangeFull) -> Self {
        protect(|| unsafe { Value::new(rb_range_new(QNIL.as_rb_value(), QNIL.as_rb_value(), 0)) })
            .unwrap()
    }
}

impl<T> From<RangeInclusive<T>> for Value
where
    T: Into<Value>,
{
    fn from(value: RangeInclusive<T>) -> Self {
        let (start, end) = value.into_inner();
        protect(|| unsafe {
            Value::new(rb_range_new(
                start.into().as_rb_value(),
                end.into().as_rb_value(),
                0,
            ))
        })
        .unwrap()
    }
}

impl<T> From<RangeTo<T>> for Value
where
    T: Into<Value>,
{
    fn from(value: RangeTo<T>) -> Self {
        protect(|| unsafe {
            Value::new(rb_range_new(
                QNIL.as_rb_value(),
                value.end.into().as_rb_value(),
                1,
            ))
        })
        .unwrap()
    }
}

impl<T> From<RangeToInclusive<T>> for Value
where
    T: Into<Value>,
{
    fn from(value: RangeToInclusive<T>) -> Self {
        protect(|| unsafe {
            Value::new(rb_range_new(
                QNIL.as_rb_value(),
                value.end.into().as_rb_value(),
                0,
            ))
        })
        .unwrap()
    }
}
