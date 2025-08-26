use std::fmt;

use rb_sys::VALUE;

use crate::{
    Ruby,
    error::Error,
    into_value::IntoValue,
    object::Object,
    try_convert::TryConvert,
    value::{
        NonZeroValue, ReprValue, Value,
        private::{self, ReprValue as _},
    },
};

/// Wrapper type for a Value known to be an instance of Ruby's Enumerator class.
///
/// `Enumerator` implements [`Iterator`], however Rust's iterators are a pull
/// based model, whereas Ruby's enumerators are a push based model. Bridging
/// these two models incurs a performance penalty, so `Enumerator` may not be
/// the most performant way of iterating a collection.
///
/// See the [`ReprValue`] and [`Object`] traits for additional methods
/// available on this type.
///
/// # Examples
///
/// ```
/// use magnus::{Error, Ruby, prelude::*, rb_assert};
///
/// fn example(ruby: &Ruby) -> Result<(), Error> {
///     let s = ruby.str_new("foo\nbar\nbaz");
///     let results = ruby.ary_new();
///
///     // `enumeratorize` returns `Enumerator`
///     for line in s.enumeratorize("each_line", ()) {
///         results.push(line?)?;
///     }
///     rb_assert!(r#"results == ["foo\n", "bar\n", "baz"]"#, results);
///
///     Ok(())
/// }
/// # Ruby::init(example).unwrap()
/// ```
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Enumerator(NonZeroValue);

impl Enumerator {
    /// Return `Some(Enumerator)` if `val` is an `Enumerator`, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Enumerator, eval};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(Enumerator::from_value(eval("[1, 2, 3].each").unwrap()).is_some());
    /// assert!(Enumerator::from_value(eval("[1, 2, 3]").unwrap()).is_none());
    /// ```
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            val.is_kind_of(Ruby::get_with(val).class_enumerator())
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        unsafe { Self(NonZeroValue::new_unchecked(Value::new(val))) }
    }
}

impl Iterator for Enumerator {
    type Item = Result<Value, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.funcall("next", ()) {
            Ok(v) => Some(Ok(v)),
            Err(e) if e.is_kind_of(Ruby::get_with(*self).exception_stop_iteration()) => None,
            Err(e) => Some(Err(e)),
        }
    }
}

impl fmt::Display for Enumerator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for Enumerator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", ReprValue::inspect(*self))
    }
}

impl IntoValue for Enumerator {
    #[inline]
    fn into_value_with(self, _: &Ruby) -> Value {
        self.0.get()
    }
}

impl Object for Enumerator {}

unsafe impl private::ReprValue for Enumerator {}

impl ReprValue for Enumerator {}

impl TryConvert for Enumerator {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Self::from_value(val).ok_or_else(|| {
            Error::new(
                Ruby::get_with(val).exception_type_error(),
                format!("no implicit conversion of {} into Enumerator", unsafe {
                    val.classname()
                },),
            )
        })
    }
}
