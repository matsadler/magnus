use std::{
    cmp::Ordering, convert::TryInto, fmt, iter::FromIterator, ops::Deref, os::raw::c_long, slice,
};

use rb_sys::{
    self, rb_ary_assoc, rb_ary_cat, rb_ary_clear, rb_ary_cmp, rb_ary_concat, rb_ary_delete,
    rb_ary_delete_at, rb_ary_entry, rb_ary_includes, rb_ary_join, rb_ary_new, rb_ary_new_capa,
    rb_ary_new_from_values, rb_ary_plus, rb_ary_pop, rb_ary_push, rb_ary_rassoc, rb_ary_replace,
    rb_ary_resize, rb_ary_reverse, rb_ary_rotate, rb_ary_shared_with_p, rb_ary_shift,
    rb_ary_sort_bang, rb_ary_store, rb_ary_subseq, rb_ary_to_ary, rb_ary_unshift,
    rb_check_array_type, ruby_value_type, RARRAY_CONST_PTR, RARRAY_LEN, VALUE,
};

use crate::{
    enumerator::Enumerator,
    error::{protect, Error},
    exception,
    into_value::{IntoValue, IntoValueFromNative},
    object::Object,
    r_string::{IntoRString, RString},
    ruby_handle::RubyHandle,
    try_convert::{TryConvert, TryConvertOwned},
    value::{private, NonZeroValue, ReprValue, Value, QNIL},
};

impl RubyHandle {
    pub fn ary_new(&self) -> RArray {
        unsafe { RArray::from_rb_value_unchecked(rb_ary_new()) }
    }

    pub fn ary_new_capa(&self, n: usize) -> RArray {
        unsafe { RArray::from_rb_value_unchecked(rb_ary_new_capa(n as c_long)) }
    }

    pub fn ary_from_vec<T>(&self, vec: Vec<T>) -> RArray
    where
        T: IntoValueFromNative,
    {
        let ary = self.ary_new_capa(vec.len());
        for v in vec {
            ary.push(v).unwrap();
        }
        ary
    }

    pub fn ary_new_from_values<T>(&self, slice: &[T]) -> RArray
    where
        T: ReprValue,
    {
        let ptr = slice.as_ptr() as *const VALUE;
        unsafe {
            RArray::from_rb_value_unchecked(rb_ary_new_from_values(slice.len() as c_long, ptr))
        }
    }
}

/// A Value pointer to a RArray struct, Ruby's internal representation of an
/// Array.
///
/// All [`Value`] methods should be available on this type through [`Deref`],
/// but some may be missed by this documentation.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RArray(NonZeroValue);

impl RArray {
    /// Return `Some(RArray)` if `val` is a `RArray`, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RArray};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(RArray::from_value(eval(r#"[true, 0, "example"]"#).unwrap()).is_some());
    /// assert!(RArray::from_value(eval(r#"{"answer" => 42}"#).unwrap()).is_none());
    /// assert!(RArray::from_value(eval(r"nil").unwrap()).is_none());
    /// ```
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            (val.rb_type() == ruby_value_type::RUBY_T_ARRAY)
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        Self(NonZeroValue::new_unchecked(Value::new(val)))
    }

    /// Create a new empty `RArray`.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RArray};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = RArray::new();
    /// assert!(ary.is_empty());
    /// ```
    #[inline]
    pub fn new() -> Self {
        get_ruby!().ary_new()
    }

    /// Create a new empty `RArray` with capacity for `n` elements
    /// pre-allocated.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RArray};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = RArray::with_capacity(16);
    /// assert!(ary.is_empty());
    /// ```
    #[inline]
    pub fn with_capacity(n: usize) -> Self {
        get_ruby!().ary_new_capa(n)
    }

    /// Convert or wrap a Ruby [`Value`] to a `RArray`.
    ///
    /// If `val` responds to `#to_ary` calls that and passes on the returned
    /// array, otherwise returns a single element array containing `val`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RArray, Value};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = RArray::to_ary(Value::from(1)).unwrap();
    /// let res: bool = eval!("[1] == ary", ary).unwrap();
    /// assert!(res);
    ///
    /// let ary = RArray::to_ary(Value::from(vec![1, 2, 3])).unwrap();
    /// let res: bool = eval!("[1, 2, 3] == ary", ary).unwrap();
    /// assert!(res);
    /// ```
    ///
    /// This can fail in the case of a misbehaving `#to_ary` method:
    ///
    /// ```
    /// use magnus::{eval, RArray};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let val = eval(r#"
    /// o = Object.new
    /// def o.to_ary
    ///   "not an array"
    /// end
    /// o
    /// "#).unwrap();
    /// assert!(RArray::to_ary(val).is_err());
    /// ```
    pub fn to_ary(val: Value) -> Result<Self, Error> {
        protect(|| unsafe { Self::from_rb_value_unchecked(rb_ary_to_ary(val.as_rb_value())) })
    }

    /// Create a new `RArray` that is a duplicate of `self`.
    ///
    /// The new array is only a shallow clone.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RArray};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let a = RArray::from_vec(vec![1, 2, 3]);
    /// let b = a.dup();
    /// let res: bool = eval!("a == b", a, b).unwrap();
    /// assert!(res);
    /// a.push(4);
    /// b.push(5);
    /// let res: bool = eval!("a == [1, 2, 3, 4]", a).unwrap();
    /// assert!(res);
    /// let res: bool = eval!("b == [1, 2, 3, 5]", b).unwrap();
    /// assert!(res);
    /// ```
    pub fn dup(self) -> Self {
        // rb_ary_subseq does a cheep copy-on-write
        unsafe { Self::from_rb_value_unchecked(rb_ary_subseq(self.as_rb_value(), 0, c_long::MAX)) }
    }

    /// Return the number of entries in `self` as a Rust [`usize`].
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RArray};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = RArray::new();
    /// assert_eq!(ary.len(), 0);
    ///
    /// let ary = eval::<RArray>("[:a, :b, :c]").unwrap();
    /// assert_eq!(ary.len(), 3)
    /// ```
    pub fn len(self) -> usize {
        debug_assert_value!(self);
        unsafe { RARRAY_LEN(self.as_rb_value()) as _ }
    }

    /// Return whether self contains any entries or not.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RArray};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = RArray::new();
    /// assert!(ary.is_empty());
    /// ```
    pub fn is_empty(self) -> bool {
        self.len() == 0
    }

    /// Returns `true` if `val` is in `self`, `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RArray, Symbol, QNIL};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = eval::<RArray>(r#"[:foo, "bar", 2]"#).unwrap();
    /// assert!(ary.includes(Symbol::new("foo")));
    /// assert!(ary.includes("bar"));
    /// assert!(ary.includes(2));
    /// // 2.0 == 2 in Ruby
    /// assert!(ary.includes(2.0));
    /// assert!(!ary.includes("foo"));
    /// assert!(!ary.includes(QNIL));
    /// ```
    pub fn includes<T>(self, val: T) -> bool
    where
        T: IntoValue,
    {
        unsafe {
            Value::new(rb_ary_includes(
                self.as_rb_value(),
                val.into_value_unchecked().as_rb_value(),
            ))
            .to_bool()
        }
    }

    /// Concatenate elements from the slice `s` to `self`.
    ///
    /// Returns `Err` if `self` is frozen.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Integer, QNIL, RArray, Symbol};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = RArray::new();
    /// ary.cat(&[Symbol::new("a").as_value(), Integer::from_i64(1).as_value(), QNIL.as_value()]).unwrap();
    /// let res: bool = eval!("ary == [:a, 1, nil]", ary).unwrap();
    /// assert!(res);
    /// ```
    ///
    /// ```
    /// use magnus::{eval, RArray, Symbol};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = RArray::new();
    /// ary.cat(&[Symbol::new("a"), Symbol::new("b"), Symbol::new("c")]).unwrap();
    /// let res: bool = eval!("ary == [:a, :b, :c]", ary).unwrap();
    /// assert!(res);
    /// ```
    pub fn cat<T>(self, s: &[T]) -> Result<(), Error>
    where
        T: ReprValue,
    {
        let ptr = s.as_ptr() as *const VALUE;
        protect(|| unsafe { Value::new(rb_ary_cat(self.as_rb_value(), ptr, s.len() as c_long)) })?;
        Ok(())
    }

    /// Concatenate elements from Ruby array `other` to `self`.
    ///
    /// Returns `Err` if `self` is frozen.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Integer, QNIL, RArray, Symbol};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let a = RArray::from_vec(vec![1, 2, 3]);
    /// let b = RArray::from_vec(vec!["a", "b", "c"]);
    /// a.concat(b).unwrap();
    /// let res: bool = eval!(r#"a == [1, 2, 3, "a", "b", "c"]"#, a).unwrap();
    /// assert!(res);
    /// let res: bool = eval!(r#"b == ["a", "b", "c"]"#, b).unwrap();
    /// assert!(res);
    /// ```
    pub fn concat(self, other: Self) -> Result<(), Error> {
        protect(|| unsafe { Value::new(rb_ary_concat(self.as_rb_value(), other.as_rb_value())) })?;
        Ok(())
    }

    /// Create a new `RArray` containing the both the elements in `self` and
    /// `other`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Integer, QNIL, RArray, Symbol};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let a = RArray::from_vec(vec![1, 2, 3]);
    /// let b = RArray::from_vec(vec!["a", "b", "c"]);
    /// let c = a.plus(b);
    /// let res: bool = eval!(r#"c == [1, 2, 3, "a", "b", "c"]"#, c).unwrap();
    /// assert!(res);
    /// let res: bool = eval!(r#"a == [1, 2, 3]"#, a).unwrap();
    /// assert!(res);
    /// let res: bool = eval!(r#"b == ["a", "b", "c"]"#, b).unwrap();
    /// assert!(res);
    /// ```
    pub fn plus(self, other: Self) -> Self {
        unsafe {
            Self::from_rb_value_unchecked(rb_ary_plus(self.as_rb_value(), other.as_rb_value()))
        }
    }

    /// Create a new `RArray` containing the elements in `slice`.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Integer, QNIL, RArray, Symbol};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = RArray::from_slice(&[Symbol::new("a").as_value(), Integer::from_i64(1).as_value(), QNIL.as_value()]);
    /// let res: bool = eval!("ary == [:a, 1, nil]", ary).unwrap();
    /// assert!(res);
    /// ```
    ///
    /// ```
    /// use magnus::{eval, RArray, Symbol};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = RArray::from_slice(&[Symbol::new("a"), Symbol::new("b"), Symbol::new("c")]);
    /// let res: bool = eval!("ary == [:a, :b, :c]", ary).unwrap();
    /// assert!(res);
    /// ```
    #[inline]
    pub fn from_slice<T>(slice: &[T]) -> Self
    where
        T: ReprValue,
    {
        get_ruby!().ary_new_from_values(slice)
    }

    /// Add `item` to the end of `self`.
    ///
    /// Returns `Err` if `self` is frozen.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RArray, Symbol};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = RArray::new();
    /// ary.push(Symbol::new("a")).unwrap();
    /// ary.push(1).unwrap();
    /// ary.push(()).unwrap();
    /// let res: bool = eval!("ary == [:a, 1, nil]", ary).unwrap();
    /// assert!(res);
    /// ```
    pub fn push<T>(self, item: T) -> Result<(), Error>
    where
        T: IntoValue,
    {
        protect(|| unsafe {
            Value::new(rb_ary_push(
                self.as_rb_value(),
                item.into_value_unchecked().as_rb_value(),
            ))
        })?;
        Ok(())
    }

    /// Remove and return the last element of `self`, converting it to a `T`.
    ///
    /// Errors if `self` is frozen or if the conversion fails.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RArray};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = eval::<RArray>("[1, 2, 3]").unwrap();
    /// assert_eq!(ary.pop::<i64>().unwrap(), 3);
    /// assert_eq!(ary.pop::<i64>().unwrap(), 2);
    /// assert_eq!(ary.pop::<i64>().unwrap(), 1);
    /// assert!(ary.pop::<i64>().is_err());
    /// ```
    ///
    /// ```
    /// use magnus::{eval, RArray};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = eval::<RArray>("[1, 2, 3]").unwrap();
    /// assert_eq!(ary.pop::<Option<i64>>().unwrap(), Some(3));
    /// assert_eq!(ary.pop::<Option<i64>>().unwrap(), Some(2));
    /// assert_eq!(ary.pop::<Option<i64>>().unwrap(), Some(1));
    /// assert_eq!(ary.pop::<Option<i64>>().unwrap(), None);
    /// ```
    pub fn pop<T>(self) -> Result<T, Error>
    where
        T: TryConvert,
    {
        protect(|| unsafe { Value::new(rb_ary_pop(self.as_rb_value())) })
            .and_then(|val| val.try_convert())
    }

    /// Add `item` to the beginning of `self`.
    ///
    /// Returns `Err` if `self` is frozen.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RArray, Symbol};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = RArray::new();
    /// ary.unshift(Symbol::new("a"));
    /// ary.unshift(1);
    /// ary.unshift(());
    /// let res: bool = eval!("ary == [nil, 1, :a]", ary).unwrap();
    /// assert!(res);
    /// ```
    pub fn unshift<T>(self, item: T) -> Result<(), Error>
    where
        T: IntoValue,
    {
        protect(|| unsafe {
            Value::new(rb_ary_unshift(
                self.as_rb_value(),
                item.into_value_unchecked().as_rb_value(),
            ))
        })?;
        Ok(())
    }

    /// Remove and return the first element of `self`, converting it to a `T`.
    ///
    /// Errors if `self` is frozen or if the conversion fails.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RArray};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = eval::<RArray>("[1, 2, 3]").unwrap();
    /// assert_eq!(ary.shift::<i64>().unwrap(), 1);
    /// assert_eq!(ary.shift::<i64>().unwrap(), 2);
    /// assert_eq!(ary.shift::<i64>().unwrap(), 3);
    /// assert!(ary.shift::<i64>().is_err());
    /// ```
    ///
    /// ```
    /// use magnus::{eval, RArray};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = eval::<RArray>("[1, 2, 3]").unwrap();
    /// assert_eq!(ary.shift::<Option<i64>>().unwrap(), Some(1));
    /// assert_eq!(ary.shift::<Option<i64>>().unwrap(), Some(2));
    /// assert_eq!(ary.shift::<Option<i64>>().unwrap(), Some(3));
    /// assert_eq!(ary.shift::<Option<i64>>().unwrap(), None);
    /// ```
    pub fn shift<T>(self) -> Result<T, Error>
    where
        T: TryConvert,
    {
        protect(|| unsafe { Value::new(rb_ary_shift(self.as_rb_value())) })
            .and_then(|val| val.try_convert())
    }

    /// Remove all elements from `self` that match `item`'s `==` method.
    ///
    /// Returns `Err` if `self` is frozen.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RArray};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = RArray::from_vec(vec![1, 1, 2, 3]);
    /// ary.delete(1).unwrap();
    /// let res: bool = eval!("ary == [2, 3]", ary).unwrap();
    /// assert!(res);
    /// ```
    pub fn delete<T>(self, item: T) -> Result<(), Error>
    where
        T: IntoValue,
    {
        protect(|| unsafe {
            Value::new(rb_ary_delete(
                self.as_rb_value(),
                item.into_value_unchecked().as_rb_value(),
            ))
        })?;
        Ok(())
    }

    /// Remove and return the element of `self` at `index`, converting it to a
    /// `T`.
    ///
    /// `index` may be negative, in which case it counts backward from the end
    /// of the array.
    ///
    /// Returns `Err` if `self` is frozen or if the conversion fails.
    ///
    /// The returned element will be Ruby's `nil` when `index` is out of bounds
    /// this makes it impossible to distingush between out of bounds and
    /// removing `nil` without an additional length check.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RArray};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = RArray::from_vec(vec!["a", "b", "c"]);
    /// let removed: Option::<String> = ary.delete_at(1).unwrap();
    /// assert_eq!(removed, Some(String::from("b")));
    /// let res: bool = eval!(r#"ary == ["a", "c"]"#, ary).unwrap();
    /// assert!(res);
    /// ```
    pub fn delete_at<T>(self, index: isize) -> Result<T, Error>
    where
        T: TryConvert,
    {
        protect(|| unsafe { Value::new(rb_ary_delete_at(self.as_rb_value(), index as c_long)) })
            .and_then(|val| val.try_convert())
    }

    /// Remove all elements from `self`
    ///
    /// Returns `Err` if `self` is frozen.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RArray};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = RArray::from_vec::<i64>(vec![1, 2, 3]);
    /// ary.clear().unwrap();
    /// let res: bool = eval!("ary == []", ary).unwrap();
    /// assert!(res);
    /// ```
    pub fn clear(self) -> Result<(), Error> {
        protect(|| unsafe { Value::new(rb_ary_clear(self.as_rb_value())) })?;
        Ok(())
    }

    /// Expand or shrink the length of `self`.
    ///
    /// When increasing the length of the array empty positions will be filled
    /// with `nil`.
    ///
    /// Returns `Err` if `self` is frozen.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RArray};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = RArray::from_vec::<i64>(vec![1, 2, 3]);
    /// ary.resize(5).unwrap();
    /// let res: bool = eval!("ary == [1, 2, 3, nil, nil]", ary).unwrap();
    /// assert!(res);
    /// ary.resize(2).unwrap();
    /// let res: bool = eval!("ary == [1, 2]", ary).unwrap();
    /// assert!(res);
    /// ```
    pub fn resize(self, len: usize) -> Result<(), Error> {
        protect(|| unsafe { Value::new(rb_ary_resize(self.as_rb_value(), len as c_long)) })?;
        Ok(())
    }

    /// Reverses the order of `self` in place.
    ///
    /// Returns `Err` if `self` is frozen.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RArray};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = RArray::from_vec::<i64>(vec![1, 2, 3]);
    /// ary.reverse().unwrap();
    /// let res: bool = eval!("ary == [3, 2, 1]", ary).unwrap();
    /// assert!(res);
    /// ```
    pub fn reverse(self) -> Result<(), Error> {
        protect(|| unsafe { Value::new(rb_ary_reverse(self.as_rb_value())) })?;
        Ok(())
    }

    /// Rotates the elements of `self` in place by `rot` positions.
    ///
    /// If `rot` is positive elements are rotated to the left, if negative,
    /// to the right.
    ///
    /// Returns `Err` if `self` is frozen.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RArray};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = RArray::from_vec::<i64>(vec![1, 2, 3, 4, 5, 6, 7]);
    /// ary.rotate(3).unwrap();
    /// let res: bool = eval!("ary == [4, 5, 6, 7, 1, 2, 3]", ary).unwrap();
    /// assert!(res);
    /// ```
    ///
    /// ```
    /// use magnus::{eval, RArray};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = RArray::from_vec::<i64>(vec![1, 2, 3, 4, 5, 6, 7]);
    /// ary.rotate(-3).unwrap();
    /// let res: bool = eval!("ary == [5, 6, 7, 1, 2, 3, 4]", ary).unwrap();
    /// assert!(res);
    /// ```
    pub fn rotate(self, rot: isize) -> Result<(), Error> {
        protect(|| unsafe { Value::new(rb_ary_rotate(self.as_rb_value(), rot as c_long)) })?;
        Ok(())
    }

    /// Storts the elements of `self` in place using Ruby's `<=>` operator.
    ///
    /// Returns `Err` if `self` is frozen.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RArray};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = RArray::from_vec::<i64>(vec![2, 1, 3]);
    /// ary.sort().unwrap();
    /// let res: bool = eval!("ary == [1, 2, 3]", ary).unwrap();
    /// assert!(res);
    /// ```
    pub fn sort(self) -> Result<(), Error> {
        protect(|| unsafe { Value::new(rb_ary_sort_bang(self.as_rb_value())) })?;
        Ok(())
    }

    /// Create a new `RArray` from a Rust vector.
    ///
    /// # Safety
    ///
    /// Note that this function is intended to convert from a vector of Rust
    /// values to a `RArray`.
    /// [Ruby values should never be put into a `Vec`](crate#safety).
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RArray};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = RArray::from_vec(vec![1, 2, 3]);
    /// let res: bool = eval!("ary == [1, 2, 3]", ary).unwrap();
    /// assert!(res);
    /// ```
    #[inline]
    pub fn from_vec<T>(vec: Vec<T>) -> Self
    where
        T: IntoValueFromNative,
    {
        get_ruby!().ary_from_vec(vec)
    }

    /// Return `self` as a slice of [`Value`]s.
    ///
    /// # Safety
    ///
    /// This is directly viewing memory owned and managed by Ruby. Ruby may
    /// modify or free the memory backing the returned slice, the caller must
    /// ensure this does not happen.
    ///
    /// Ruby must not be allowed to garbage collect or modify `self` while a
    /// refrence to the slice is held.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RArray};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = eval::<RArray>("[1, 2, 3, 4, 5]").unwrap();
    /// // must not call any Ruby api that may modify ary while we have a
    /// // refrence to the return value of ::from_slice()
    /// let middle = unsafe { RArray::from_slice(&ary.as_slice()[1..4]) };
    /// let res: bool = eval!("middle == [2, 3, 4]", middle).unwrap();
    /// assert!(res);
    /// ```
    pub unsafe fn as_slice(&self) -> &[Value] {
        self.as_slice_unconstrained()
    }

    pub(crate) unsafe fn as_slice_unconstrained<'a>(self) -> &'a [Value] {
        debug_assert_value!(self);
        slice::from_raw_parts(
            RARRAY_CONST_PTR(self.as_rb_value()) as *const Value,
            RARRAY_LEN(self.as_rb_value()) as usize,
        )
    }

    /// Convert `self` to a Rust vector of `T`s. Errors if converting any
    /// element in the array fails.
    ///
    /// This will only convert to a map of 'owned' Rust native types. The types
    /// representing Ruby objects can not be stored in a heap-allocated
    /// datastructure like a [`Vec`] as they are hidden from the mark phase
    /// of Ruby's garbage collector, and thus may be prematurely garbage
    /// collected in the following sweep phase.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RArray};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = eval::<RArray>("[1, 2, 3]").unwrap();
    /// assert_eq!(ary.to_vec::<i64>().unwrap(), vec![1, 2, 3]);
    /// ```
    pub fn to_vec<T>(self) -> Result<Vec<T>, Error>
    where
        T: TryConvertOwned,
    {
        unsafe { self.as_slice().iter().map(|v| T::try_convert(*v)).collect() }
    }

    /// Convert `self` to a Rust array of [`Value`]s, of length `N`.
    ///
    /// Errors if the Ruby array is not of length `N`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RArray};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = eval::<RArray>("[1, 2, 3]").unwrap();
    /// assert!(ary.to_value_array::<3>().is_ok());
    /// assert!(ary.to_value_array::<2>().is_err());
    /// assert!(ary.to_value_array::<4>().is_err());
    /// ```
    pub fn to_value_array<const N: usize>(self) -> Result<[Value; N], Error> {
        unsafe {
            self.as_slice().try_into().map_err(|_| {
                Error::new(
                    exception::type_error(),
                    format!("expected Array of length {}", N),
                )
            })
        }
    }

    /// Convert `self` to a Rust array of `T`s, of length `N`.
    ///
    /// Errors if converting any element in the array fails, or if the Ruby
    /// array is not of length `N`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RArray};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = eval::<RArray>("[1, 2, 3]").unwrap();
    /// assert_eq!(ary.to_array::<i64, 3>().unwrap(), [1, 2, 3]);
    /// assert!(ary.to_array::<i64, 2>().is_err());
    /// assert!(ary.to_array::<i64, 4>().is_err());
    /// ```
    pub fn to_array<T, const N: usize>(self) -> Result<[T; N], Error>
    where
        T: TryConvert,
    {
        unsafe {
            let slice = self.as_slice();
            if slice.len() != N {
                return Err(Error::new(
                    exception::type_error(),
                    format!("expected Array of length {}", N),
                ));
            }
            // one day might be able to collect direct into an array, but for
            // now need to go via Vec
            slice
                .iter()
                .map(|v| v.try_convert())
                .collect::<Result<Vec<T>, Error>>()
                .map(|v| v.try_into().ok().unwrap())
        }
    }

    /// Stringify the contents of `self` and join the sequence with `sep`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Integer, RArray, Symbol, QNIL};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = RArray::from_slice(&[Symbol::new("a").as_value(), Integer::from_i64(1).as_value(), QNIL.as_value()]);
    /// assert_eq!(ary.join(", ").unwrap().to_string().unwrap(), "a, 1, ")
    /// ```
    pub fn join<T>(self, sep: T) -> Result<RString, Error>
    where
        T: IntoRString,
    {
        protect(|| unsafe {
            RString::from_rb_value_unchecked(rb_ary_join(
                self.as_rb_value(),
                sep.into_r_string_unchecked().as_rb_value(),
            ))
        })
    }

    /// Return the element at `offset`, converting it to a `T`.
    ///
    /// Errors if the conversion fails.
    ///
    /// An offset out of range will return `nil`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RArray};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary: RArray = eval(r#"["a", "b", "c"]"#).unwrap();
    ///
    /// assert_eq!(ary.entry::<String>(0).unwrap(), String::from("a"));
    /// assert_eq!(ary.entry::<char>(0).unwrap(), 'a');
    /// assert_eq!(ary.entry::<Option<String>>(0).unwrap(), Some(String::from("a")));
    /// assert_eq!(ary.entry::<String>(1).unwrap(), String::from("b"));
    /// assert_eq!(ary.entry::<String>(-1).unwrap(), String::from("c"));
    /// assert_eq!(ary.entry::<Option<String>>(3).unwrap(), None);
    ///
    /// assert!(ary.entry::<i64>(0).is_err());
    /// assert!(ary.entry::<String>(3).is_err());
    /// ```
    pub fn entry<T>(self, offset: isize) -> Result<T, Error>
    where
        T: TryConvert,
    {
        unsafe { Value::new(rb_ary_entry(self.as_rb_value(), offset as c_long)).try_convert() }
    }

    /// Set the element at `offset`.
    ///
    /// If `offset` is beyond the current size of the array the array will be
    /// expanded and padded with `nil`.
    ///
    /// Returns `Err` if `self` is frozen.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RArray, Symbol};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = RArray::from_slice(&[Symbol::new("a"), Symbol::new("b"), Symbol::new("c")]);
    /// ary.store(0, Symbol::new("d"));
    /// ary.store(5, Symbol::new("e"));
    /// ary.store(6, Symbol::new("f"));
    /// ary.store(-1, Symbol::new("g"));
    /// let res: bool = eval!("ary == [:d, :b, :c, nil, nil, :e, :g]", ary).unwrap();
    /// assert!(res);
    /// ```
    pub fn store<T>(self, offset: isize, val: T) -> Result<(), Error>
    where
        T: IntoValue,
    {
        protect(|| unsafe {
            rb_ary_store(
                self.as_rb_value(),
                offset as c_long,
                val.into_value_unchecked().as_rb_value(),
            );
            QNIL
        })?;
        Ok(())
    }

    /// Returns an [`Enumerator`] over `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RArray};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let mut res = Vec::new();
    /// for i in eval::<RArray>("[1, 2, 3]").unwrap().each() {
    ///     res.push(i.unwrap().try_convert::<i64>().unwrap());
    /// }
    /// assert_eq!(res, vec![1, 2, 3]);
    /// ```
    pub fn each(self) -> Enumerator {
        // TODO why doesn't rb_ary_each work?
        self.enumeratorize("each", ())
    }

    /// Returns true if both `self` and `other` share the same backing storage.
    ///
    /// It is possible for two Ruby Arrays to share the same backing storage,
    /// and only when one of them is modified will the copy-on-write cost be
    /// paid.
    ///
    /// Currently, this method will only return `true` if `self` and `other`
    /// are of the same length, even though Ruby may continue to use the same
    /// backing storage after popping a value from either of the arrays.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RArray, Value};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = RArray::from_vec((0..256).collect());
    /// let copy = RArray::new();
    /// copy.replace(ary);
    /// assert!(ary.is_shared(copy));
    /// assert!(copy.is_shared(ary));
    /// copy.push(11);
    /// assert!(!ary.is_shared(copy));
    /// assert!(!copy.is_shared(ary));
    /// ```
    pub fn is_shared(self, other: Self) -> bool {
        unsafe {
            Value::new(rb_ary_shared_with_p(
                self.as_rb_value(),
                other.as_rb_value(),
            ))
            .to_bool()
        }
    }

    /// Replace the contents of `self` with `from`.
    ///
    /// `from` is unmodified, and `self` becomes a copy of `from`. `self`'s
    /// former contents are abandoned.
    ///
    /// This is a very cheep operation, `self` will point at `from`'s backing
    /// storage until one is modified, and only then will the copy-on-write
    /// cost be paid.
    ///
    /// Returns `Err` if `self` is frozen.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RArray};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = RArray::from_vec((0..256).collect());
    /// let copy = RArray::new();
    /// copy.replace(ary);
    /// assert!(copy.is_shared(ary));
    /// copy.push(11);
    /// assert!(!copy.is_shared(ary));
    /// ```
    pub fn replace(self, from: Self) -> Result<(), Error> {
        protect(|| unsafe { Value::new(rb_ary_replace(self.as_rb_value(), from.as_rb_value())) })?;
        Ok(())
    }

    /// Create a new array from a subsequence of `self`.
    ///
    /// This is a very cheep operation, as `self` and the new array will share
    /// thier backing storage until one is modified.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RArray, Value};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = RArray::from_vec(vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
    /// let a = ary.subseq(0, 5).unwrap();
    /// let b = ary.subseq(5, 5).unwrap();
    /// assert_eq!(a.to_vec::<i64>().unwrap(), vec![1, 2, 3, 4, 5]);
    /// assert_eq!(b.to_vec::<i64>().unwrap(), vec![6, 7, 8, 9, 10]);
    /// ```
    // TODO maybe take a range instead of offset and length
    pub fn subseq(self, offset: usize, length: usize) -> Option<Self> {
        unsafe {
            let val = Value::new(rb_ary_subseq(
                self.as_rb_value(),
                offset as c_long,
                length as c_long,
            ));
            (!val.is_nil()).then(|| Self::from_rb_value_unchecked(val.as_rb_value()))
        }
    }

    /// Search `self` as an 'associative array' for `key`.
    ///
    /// Assumes `self` is an array of arrays, searching from the start of the
    /// outer array, returns the first inner array where the first element
    /// matches `key`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RArray};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = RArray::from_vec(vec![("foo", 1), ("bar", 2), ("baz", 3), ("baz", 4)]);
    /// assert_eq!(ary.assoc::<_, (String, i64)>("baz").unwrap(), (String::from("baz"), 3));
    /// assert_eq!(ary.assoc::<_, Option<(String, i64)>>("quz").unwrap(), None);
    /// ```
    pub fn assoc<K, T>(self, key: K) -> Result<T, Error>
    where
        K: IntoValue,
        T: TryConvert,
    {
        protect(|| unsafe {
            Value::new(rb_ary_assoc(
                self.as_rb_value(),
                key.into_value_unchecked().as_rb_value(),
            ))
        })
        .and_then(|val| val.try_convert())
    }

    /// Search `self` as an 'associative array' for `value`.
    ///
    /// Assumes `self` is an array of arrays, searching from the start of the
    /// outer array, returns the first inner array where the second element
    /// matches `value`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RArray};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = RArray::from_vec(vec![("foo", 1), ("bar", 2), ("baz", 3), ("qux", 3)]);
    /// assert_eq!(ary.rassoc::<_, (String, i64)>(3).unwrap(), (String::from("baz"), 3));
    /// assert_eq!(ary.rassoc::<_, Option<(String, i64)>>(4).unwrap(), None);
    /// ```
    pub fn rassoc<K, T>(self, value: K) -> Result<T, Error>
    where
        K: IntoValue,
        T: TryConvert,
    {
        protect(|| unsafe {
            Value::new(rb_ary_rassoc(
                self.as_rb_value(),
                value.into_value_unchecked().as_rb_value(),
            ))
        })
        .and_then(|val| val.try_convert())
    }

    /// Recursively compares elements of the two arrays using Ruby's `<=>`.
    ///
    /// Returns `Some(Ordering::Equal)` if `self` and `other` are equal.
    /// Returns `Some(Ordering::Less)` if `self` if less than `other`.
    /// Returns `Some(Ordering::Greater)` if `self` if greater than `other`.
    /// Returns `None` if `self` and `other` are not comparable.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::cmp::Ordering;
    /// use magnus::{eval, RArray, QNIL};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let a = RArray::from_vec(vec![1, 2, 3]);
    /// let b = RArray::from_vec(vec![1, 2, 3]);
    /// assert_eq!(a.cmp(b).unwrap(), Some(Ordering::Equal));
    ///
    /// let c = RArray::from_vec(vec![1, 2, 0]);
    /// assert_eq!(a.cmp(c).unwrap(), Some(Ordering::Greater));
    ///
    /// let d = RArray::from_vec(vec![1, 2, 4]);
    /// assert_eq!(a.cmp(d).unwrap(), Some(Ordering::Less));
    ///
    /// let e = RArray::from_vec(vec![1, 2]);
    /// e.push(QNIL);
    /// assert_eq!(a.cmp(e).unwrap(), None);
    /// ```
    ///
    /// Note that `std::cmp::Ordering` can be cast to `i{8,16,32,64,size}` to
    /// get the Ruby standard `-1`/`0`/`+1` for comparison results.
    ///
    /// ```
    /// assert_eq!(std::cmp::Ordering::Less as i64, -1);
    /// assert_eq!(std::cmp::Ordering::Equal as i64, 0);
    /// assert_eq!(std::cmp::Ordering::Greater as i64, 1);
    /// ```
    #[allow(clippy::should_implement_trait)]
    pub fn cmp(self, other: Self) -> Result<Option<Ordering>, Error> {
        protect(|| unsafe { Value::new(rb_ary_cmp(self.as_rb_value(), other.as_rb_value())) })
            .and_then(|val| val.try_convert::<Option<i64>>())
            .map(|opt| opt.map(|i| i.cmp(&0)))
    }
}

impl Deref for RArray {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
    }
}

impl fmt::Display for RArray {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for RArray {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl IntoValue for RArray {
    fn into_value_with(self, _: &RubyHandle) -> Value {
        *self
    }
}

impl From<RArray> for Value {
    fn from(val: RArray) -> Self {
        *val
    }
}

impl<T0> IntoValue for (T0,)
where
    T0: IntoValue,
{
    fn into_value_with(self, handle: &RubyHandle) -> Value {
        let ary = [handle.into_value(self.0)];
        handle.ary_new_from_values(&ary).into()
    }
}

unsafe impl<T0> IntoValueFromNative for (T0,) where T0: IntoValueFromNative {}

impl<T0> From<(T0,)> for Value
where
    T0: IntoValue,
{
    fn from(val: (T0,)) -> Self {
        val.into_value()
    }
}

impl<T0, T1> IntoValue for (T0, T1)
where
    T0: IntoValue,
    T1: IntoValue,
{
    fn into_value_with(self, handle: &RubyHandle) -> Value {
        let ary = [handle.into_value(self.0), handle.into_value(self.1)];
        handle.ary_new_from_values(&ary).into()
    }
}

unsafe impl<T0, T1> IntoValueFromNative for (T0, T1)
where
    T0: IntoValueFromNative,
    T1: IntoValueFromNative,
{
}

impl<T0, T1> From<(T0, T1)> for Value
where
    T0: IntoValue,
    T1: IntoValue,
{
    fn from(val: (T0, T1)) -> Self {
        val.into_value()
    }
}

impl<T0, T1, T2> IntoValue for (T0, T1, T2)
where
    T0: IntoValue,
    T1: IntoValue,
    T2: IntoValue,
{
    fn into_value_with(self, handle: &RubyHandle) -> Value {
        let ary = [
            handle.into_value(self.0),
            handle.into_value(self.1),
            handle.into_value(self.2),
        ];
        handle.ary_new_from_values(&ary).into()
    }
}

unsafe impl<T0, T1, T2> IntoValueFromNative for (T0, T1, T2)
where
    T0: IntoValueFromNative,
    T1: IntoValueFromNative,
    T2: IntoValueFromNative,
{
}

impl<T0, T1, T2> From<(T0, T1, T2)> for Value
where
    T0: IntoValue,
    T1: IntoValue,
    T2: IntoValue,
{
    fn from(val: (T0, T1, T2)) -> Self {
        val.into_value()
    }
}

impl<T0, T1, T2, T3> IntoValue for (T0, T1, T2, T3)
where
    T0: IntoValue,
    T1: IntoValue,
    T2: IntoValue,
    T3: IntoValue,
{
    fn into_value_with(self, handle: &RubyHandle) -> Value {
        let ary = [
            handle.into_value(self.0),
            handle.into_value(self.1),
            handle.into_value(self.2),
            handle.into_value(self.3),
        ];
        handle.ary_new_from_values(&ary).into()
    }
}

unsafe impl<T0, T1, T2, T3> IntoValueFromNative for (T0, T1, T2, T3)
where
    T0: IntoValueFromNative,
    T1: IntoValueFromNative,
    T2: IntoValueFromNative,
    T3: IntoValueFromNative,
{
}

impl<T0, T1, T2, T3> From<(T0, T1, T2, T3)> for Value
where
    T0: IntoValue,
    T1: IntoValue,
    T2: IntoValue,
    T3: IntoValue,
{
    fn from(val: (T0, T1, T2, T3)) -> Self {
        val.into_value()
    }
}

impl<T0, T1, T2, T3, T4> IntoValue for (T0, T1, T2, T3, T4)
where
    T0: IntoValue,
    T1: IntoValue,
    T2: IntoValue,
    T3: IntoValue,
    T4: IntoValue,
{
    fn into_value_with(self, handle: &RubyHandle) -> Value {
        let ary = [
            handle.into_value(self.0),
            handle.into_value(self.1),
            handle.into_value(self.2),
            handle.into_value(self.3),
            handle.into_value(self.4),
        ];
        handle.ary_new_from_values(&ary).into()
    }
}

unsafe impl<T0, T1, T2, T3, T4> IntoValueFromNative for (T0, T1, T2, T3, T4)
where
    T0: IntoValueFromNative,
    T1: IntoValueFromNative,
    T2: IntoValueFromNative,
    T3: IntoValueFromNative,
    T4: IntoValueFromNative,
{
}

impl<T0, T1, T2, T3, T4> From<(T0, T1, T2, T3, T4)> for Value
where
    T0: IntoValue,
    T1: IntoValue,
    T2: IntoValue,
    T3: IntoValue,
    T4: IntoValue,
{
    fn from(val: (T0, T1, T2, T3, T4)) -> Self {
        val.into_value()
    }
}

impl<T0, T1, T2, T3, T4, T5> IntoValue for (T0, T1, T2, T3, T4, T5)
where
    T0: IntoValue,
    T1: IntoValue,
    T2: IntoValue,
    T3: IntoValue,
    T4: IntoValue,
    T5: IntoValue,
{
    fn into_value_with(self, handle: &RubyHandle) -> Value {
        let ary = [
            handle.into_value(self.0),
            handle.into_value(self.1),
            handle.into_value(self.2),
            handle.into_value(self.3),
            handle.into_value(self.4),
            handle.into_value(self.5),
        ];
        handle.ary_new_from_values(&ary).into()
    }
}

unsafe impl<T0, T1, T2, T3, T4, T5> IntoValueFromNative for (T0, T1, T2, T3, T4, T5)
where
    T0: IntoValueFromNative,
    T1: IntoValueFromNative,
    T2: IntoValueFromNative,
    T3: IntoValueFromNative,
    T4: IntoValueFromNative,
    T5: IntoValueFromNative,
{
}

impl<T0, T1, T2, T3, T4, T5> From<(T0, T1, T2, T3, T4, T5)> for Value
where
    T0: IntoValue,
    T1: IntoValue,
    T2: IntoValue,
    T3: IntoValue,
    T4: IntoValue,
    T5: IntoValue,
{
    fn from(val: (T0, T1, T2, T3, T4, T5)) -> Self {
        val.into_value()
    }
}

impl<T0, T1, T2, T3, T4, T5, T6> IntoValue for (T0, T1, T2, T3, T4, T5, T6)
where
    T0: IntoValue,
    T1: IntoValue,
    T2: IntoValue,
    T3: IntoValue,
    T4: IntoValue,
    T5: IntoValue,
    T6: IntoValue,
{
    fn into_value_with(self, handle: &RubyHandle) -> Value {
        let ary = [
            handle.into_value(self.0),
            handle.into_value(self.1),
            handle.into_value(self.2),
            handle.into_value(self.3),
            handle.into_value(self.4),
            handle.into_value(self.5),
            handle.into_value(self.6),
        ];
        handle.ary_new_from_values(&ary).into()
    }
}

unsafe impl<T0, T1, T2, T3, T4, T5, T6> IntoValueFromNative for (T0, T1, T2, T3, T4, T5, T6)
where
    T0: IntoValueFromNative,
    T1: IntoValueFromNative,
    T2: IntoValueFromNative,
    T3: IntoValueFromNative,
    T4: IntoValueFromNative,
    T5: IntoValueFromNative,
    T6: IntoValueFromNative,
{
}

impl<T0, T1, T2, T3, T4, T5, T6> From<(T0, T1, T2, T3, T4, T5, T6)> for Value
where
    T0: IntoValue,
    T1: IntoValue,
    T2: IntoValue,
    T3: IntoValue,
    T4: IntoValue,
    T5: IntoValue,
    T6: IntoValue,
{
    fn from(val: (T0, T1, T2, T3, T4, T5, T6)) -> Self {
        val.into_value()
    }
}

impl<T0, T1, T2, T3, T4, T5, T6, T7> IntoValue for (T0, T1, T2, T3, T4, T5, T6, T7)
where
    T0: IntoValue,
    T1: IntoValue,
    T2: IntoValue,
    T3: IntoValue,
    T4: IntoValue,
    T5: IntoValue,
    T6: IntoValue,
    T7: IntoValue,
{
    fn into_value_with(self, handle: &RubyHandle) -> Value {
        let ary = [
            handle.into_value(self.0),
            handle.into_value(self.1),
            handle.into_value(self.2),
            handle.into_value(self.3),
            handle.into_value(self.4),
            handle.into_value(self.5),
            handle.into_value(self.6),
            handle.into_value(self.7),
        ];
        handle.ary_new_from_values(&ary).into()
    }
}

unsafe impl<T0, T1, T2, T3, T4, T5, T6, T7> IntoValueFromNative for (T0, T1, T2, T3, T4, T5, T6, T7)
where
    T0: IntoValueFromNative,
    T1: IntoValueFromNative,
    T2: IntoValueFromNative,
    T3: IntoValueFromNative,
    T4: IntoValueFromNative,
    T5: IntoValueFromNative,
    T6: IntoValueFromNative,
    T7: IntoValueFromNative,
{
}

impl<T0, T1, T2, T3, T4, T5, T6, T7> From<(T0, T1, T2, T3, T4, T5, T6, T7)> for Value
where
    T0: IntoValue,
    T1: IntoValue,
    T2: IntoValue,
    T3: IntoValue,
    T4: IntoValue,
    T5: IntoValue,
    T6: IntoValue,
    T7: IntoValue,
{
    fn from(val: (T0, T1, T2, T3, T4, T5, T6, T7)) -> Self {
        val.into_value()
    }
}

impl<T0, T1, T2, T3, T4, T5, T6, T7, T8> IntoValue for (T0, T1, T2, T3, T4, T5, T6, T7, T8)
where
    T0: IntoValue,
    T1: IntoValue,
    T2: IntoValue,
    T3: IntoValue,
    T4: IntoValue,
    T5: IntoValue,
    T6: IntoValue,
    T7: IntoValue,
    T8: IntoValue,
{
    fn into_value_with(self, handle: &RubyHandle) -> Value {
        let ary = [
            handle.into_value(self.0),
            handle.into_value(self.1),
            handle.into_value(self.2),
            handle.into_value(self.3),
            handle.into_value(self.4),
            handle.into_value(self.5),
            handle.into_value(self.6),
            handle.into_value(self.7),
            handle.into_value(self.8),
        ];
        handle.ary_new_from_values(&ary).into()
    }
}

unsafe impl<T0, T1, T2, T3, T4, T5, T6, T7, T8> IntoValueFromNative
    for (T0, T1, T2, T3, T4, T5, T6, T7, T8)
where
    T0: IntoValueFromNative,
    T1: IntoValueFromNative,
    T2: IntoValueFromNative,
    T3: IntoValueFromNative,
    T4: IntoValueFromNative,
    T5: IntoValueFromNative,
    T6: IntoValueFromNative,
    T7: IntoValueFromNative,
    T8: IntoValueFromNative,
{
}

impl<T0, T1, T2, T3, T4, T5, T6, T7, T8> From<(T0, T1, T2, T3, T4, T5, T6, T7, T8)> for Value
where
    T0: IntoValue,
    T1: IntoValue,
    T2: IntoValue,
    T3: IntoValue,
    T4: IntoValue,
    T5: IntoValue,
    T6: IntoValue,
    T7: IntoValue,
    T8: IntoValue,
{
    fn from(val: (T0, T1, T2, T3, T4, T5, T6, T7, T8)) -> Self {
        val.into_value()
    }
}

impl<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> IntoValue for (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9)
where
    T0: IntoValue,
    T1: IntoValue,
    T2: IntoValue,
    T3: IntoValue,
    T4: IntoValue,
    T5: IntoValue,
    T6: IntoValue,
    T7: IntoValue,
    T8: IntoValue,
    T9: IntoValue,
{
    fn into_value_with(self, handle: &RubyHandle) -> Value {
        let ary = [
            handle.into_value(self.0),
            handle.into_value(self.1),
            handle.into_value(self.2),
            handle.into_value(self.3),
            handle.into_value(self.4),
            handle.into_value(self.5),
            handle.into_value(self.6),
            handle.into_value(self.7),
            handle.into_value(self.8),
            handle.into_value(self.9),
        ];
        handle.ary_new_from_values(&ary).into()
    }
}

unsafe impl<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> IntoValueFromNative
    for (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9)
where
    T0: IntoValueFromNative,
    T1: IntoValueFromNative,
    T2: IntoValueFromNative,
    T3: IntoValueFromNative,
    T4: IntoValueFromNative,
    T5: IntoValueFromNative,
    T6: IntoValueFromNative,
    T7: IntoValueFromNative,
    T8: IntoValueFromNative,
    T9: IntoValueFromNative,
{
}

impl<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> From<(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9)>
    for Value
where
    T0: IntoValue,
    T1: IntoValue,
    T2: IntoValue,
    T3: IntoValue,
    T4: IntoValue,
    T5: IntoValue,
    T6: IntoValue,
    T7: IntoValue,
    T8: IntoValue,
    T9: IntoValue,
{
    fn from(val: (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9)) -> Self {
        val.into_value()
    }
}

impl<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> IntoValue
    for (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10)
where
    T0: IntoValue,
    T1: IntoValue,
    T2: IntoValue,
    T3: IntoValue,
    T4: IntoValue,
    T5: IntoValue,
    T6: IntoValue,
    T7: IntoValue,
    T8: IntoValue,
    T9: IntoValue,
    T10: IntoValue,
{
    fn into_value_with(self, handle: &RubyHandle) -> Value {
        let ary = [
            handle.into_value(self.0),
            handle.into_value(self.1),
            handle.into_value(self.2),
            handle.into_value(self.3),
            handle.into_value(self.4),
            handle.into_value(self.5),
            handle.into_value(self.6),
            handle.into_value(self.7),
            handle.into_value(self.8),
            handle.into_value(self.9),
            handle.into_value(self.10),
        ];
        handle.ary_new_from_values(&ary).into()
    }
}

unsafe impl<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> IntoValueFromNative
    for (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10)
where
    T0: IntoValueFromNative,
    T1: IntoValueFromNative,
    T2: IntoValueFromNative,
    T3: IntoValueFromNative,
    T4: IntoValueFromNative,
    T5: IntoValueFromNative,
    T6: IntoValueFromNative,
    T7: IntoValueFromNative,
    T8: IntoValueFromNative,
    T9: IntoValueFromNative,
    T10: IntoValueFromNative,
{
}

impl<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>
    From<(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10)> for Value
where
    T0: IntoValue,
    T1: IntoValue,
    T2: IntoValue,
    T3: IntoValue,
    T4: IntoValue,
    T5: IntoValue,
    T6: IntoValue,
    T7: IntoValue,
    T8: IntoValue,
    T9: IntoValue,
    T10: IntoValue,
{
    fn from(val: (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10)) -> Self {
        val.into_value()
    }
}

impl<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> IntoValue
    for (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11)
where
    T0: IntoValue,
    T1: IntoValue,
    T2: IntoValue,
    T3: IntoValue,
    T4: IntoValue,
    T5: IntoValue,
    T6: IntoValue,
    T7: IntoValue,
    T8: IntoValue,
    T9: IntoValue,
    T10: IntoValue,
    T11: IntoValue,
{
    fn into_value_with(self, handle: &RubyHandle) -> Value {
        let ary = [
            handle.into_value(self.0),
            handle.into_value(self.1),
            handle.into_value(self.2),
            handle.into_value(self.3),
            handle.into_value(self.4),
            handle.into_value(self.5),
            handle.into_value(self.6),
            handle.into_value(self.7),
            handle.into_value(self.8),
            handle.into_value(self.9),
            handle.into_value(self.10),
            handle.into_value(self.11),
        ];
        handle.ary_new_from_values(&ary).into()
    }
}

unsafe impl<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> IntoValueFromNative
    for (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11)
where
    T0: IntoValueFromNative,
    T1: IntoValueFromNative,
    T2: IntoValueFromNative,
    T3: IntoValueFromNative,
    T4: IntoValueFromNative,
    T5: IntoValueFromNative,
    T6: IntoValueFromNative,
    T7: IntoValueFromNative,
    T8: IntoValueFromNative,
    T9: IntoValueFromNative,
    T10: IntoValueFromNative,
    T11: IntoValueFromNative,
{
}

impl<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>
    From<(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11)> for Value
where
    T0: IntoValue,
    T1: IntoValue,
    T2: IntoValue,
    T3: IntoValue,
    T4: IntoValue,
    T5: IntoValue,
    T6: IntoValue,
    T7: IntoValue,
    T8: IntoValue,
    T9: IntoValue,
    T10: IntoValue,
    T11: IntoValue,
{
    fn from(val: (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11)) -> Self {
        val.into_value()
    }
}

impl<T> IntoValue for Vec<T>
where
    T: IntoValueFromNative,
{
    fn into_value_with(self, handle: &RubyHandle) -> Value {
        handle.ary_from_vec(self).into()
    }
}

impl<T> From<Vec<T>> for Value
where
    T: IntoValueFromNative,
{
    fn from(val: Vec<T>) -> Self {
        val.into_value()
    }
}

impl<T> FromIterator<T> for RArray
where
    T: IntoValue,
{
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        let iter = iter.into_iter();
        let (lower, _) = iter.size_hint();
        let array = if lower > 0 {
            RArray::with_capacity(lower)
        } else {
            RArray::new()
        };
        for i in iter {
            array.push(i).unwrap();
        }
        array
    }
}

impl Object for RArray {}

unsafe impl private::ReprValue for RArray {
    fn to_value(self) -> Value {
        *self
    }

    unsafe fn from_value_unchecked(val: Value) -> Self {
        Self(NonZeroValue::new_unchecked(val))
    }
}

impl ReprValue for RArray {}

impl TryConvert for RArray {
    fn try_convert(val: Value) -> Result<Self, Error> {
        if let Some(v) = Self::from_value(val) {
            return Ok(v);
        }
        unsafe {
            protect(|| Value::new(rb_check_array_type(val.as_rb_value()))).and_then(|res| {
                Self::from_value(res).ok_or_else(|| {
                    Error::new(
                        exception::type_error(),
                        format!("no implicit conversion of {} into Array", val.class()),
                    )
                })
            })
        }
    }
}
