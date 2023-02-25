//! Types and functions for working with Ruby’s Hash class.

use std::{
    collections::HashMap,
    fmt,
    hash::Hash,
    iter::FromIterator,
    marker::PhantomData,
    os::raw::{c_int, c_long},
    panic::AssertUnwindSafe,
};

#[cfg(ruby_gte_2_7)]
use rb_sys::rb_hash_bulk_insert;
#[cfg(ruby_gte_3_2)]
use rb_sys::rb_hash_new_capa;
use rb_sys::{
    rb_check_hash_type, rb_hash_aref, rb_hash_aset, rb_hash_clear, rb_hash_delete, rb_hash_fetch,
    rb_hash_foreach, rb_hash_lookup, rb_hash_lookup2, rb_hash_new, rb_hash_size, rb_hash_size_num,
    rb_hash_update_by, ruby_value_type, VALUE,
};

use crate::{
    error::{protect, raise, Error},
    exception,
    into_value::{IntoValue, IntoValueFromNative},
    object::Object,
    try_convert::{TryConvert, TryConvertOwned},
    value::{
        private::{self, ReprValue as _},
        Fixnum, NonZeroValue, ReprValue, Value, QUNDEF,
    },
    Ruby,
};

/// Iteration state for [`RHash::foreach`].
#[repr(u32)]
pub enum ForEach {
    /// Continue iterating.
    Continue,
    /// Stop iterating.
    Stop,
    /// Delete the last entry and continue iterating.
    Delete,
}

// Helper type for wrapping a function with type conversions and error
// handling for `RHash::foreach`.
struct ForEachCallback<Func, K, V> {
    func: Func,
    key: PhantomData<K>,
    value: PhantomData<V>,
}

impl<Func, K, V> ForEachCallback<Func, K, V>
where
    Func: FnMut(K, V) -> Result<ForEach, Error>,
    K: TryConvert,
    V: TryConvert,
{
    #[inline]
    fn new(func: Func) -> Self {
        Self {
            func,
            key: Default::default(),
            value: Default::default(),
        }
    }

    #[inline]
    unsafe fn call_convert_value(mut self, key: Value, value: Value) -> Result<ForEach, Error> {
        (self.func)(
            TryConvert::try_convert(key)?,
            TryConvert::try_convert(value)?,
        )
    }

    #[inline]
    unsafe fn call_handle_error(self, key: Value, value: Value) -> ForEach {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
            self.call_convert_value(key, value)
        })) {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(e)),
        };
        match res {
            Ok(v) => v,
            Err(e) => raise(e),
        }
    }
}

impl Ruby {
    pub fn hash_new(&self) -> RHash {
        unsafe { RHash::from_rb_value_unchecked(rb_hash_new()) }
    }

    #[cfg(any(ruby_gte_3_2, docsrs))]
    #[cfg_attr(docsrs, doc(cfg(ruby_gte_3_2)))]
    pub fn with_capacity(&self, n: usize) -> RHash {
        unsafe { RHash::from_rb_value_unchecked(rb_hash_new_capa(n as c_long)) }
    }
}

/// A Value pointer to a RHash struct, Ruby's internal representation of Hash
/// objects.
///
/// See the [`ReprValue`] and [`Object`] traits for additional methods
/// available on this type.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RHash(NonZeroValue);

impl RHash {
    /// Return `Some(RHash)` if `val` is a `RHash`, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RHash};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// assert!(RHash::from_value(eval(r#"{"answer" => 42}"#).unwrap()).is_some());
    /// assert!(RHash::from_value(eval("[]").unwrap()).is_none());
    /// assert!(RHash::from_value(eval("nil").unwrap()).is_none());
    /// ```
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            (val.rb_type() == ruby_value_type::RUBY_T_HASH)
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        Self(NonZeroValue::new_unchecked(Value::new(val)))
    }

    /// Create a new empty `RHash`.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::RHash;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let hash = RHash::new();
    /// assert!(hash.is_empty());
    /// ```
    #[inline]
    pub fn new() -> RHash {
        get_ruby!().hash_new()
    }

    /// Create a new empty `RHash` with capacity for `n` elements
    /// pre-allocated.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RHash};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let ary = RHash::with_capacity(16);
    /// assert!(ary.is_empty());
    /// ```
    #[cfg(any(ruby_gte_3_2, docsrs))]
    #[cfg_attr(docsrs, doc(cfg(ruby_gte_3_2)))]
    #[inline]
    pub fn with_capacity(n: usize) -> Self {
        get_ruby!().with_capacity(n)
    }

    /// Set the value `val` for the key `key`.
    ///
    /// Errors if `self` is frozen or `key` does not respond to `hash`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RHash};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let hash = RHash::new();
    /// hash.aset("answer", 42);
    /// let res: bool = eval!(r#"hash == {"answer" => 42}"#, hash).unwrap();
    /// assert!(res);
    /// ```
    pub fn aset<K, V>(self, key: K, val: V) -> Result<(), Error>
    where
        K: IntoValue,
        V: IntoValue,
    {
        let key = unsafe { key.into_value_unchecked() };
        let val = unsafe { val.into_value_unchecked() };
        unsafe {
            protect(|| {
                Value::new(rb_hash_aset(
                    self.as_rb_value(),
                    key.as_rb_value(),
                    val.as_rb_value(),
                ))
            })?;
        }
        Ok(())
    }

    /// Insert a list of key-value pairs into a hash at once.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, IntoValue, RHash, RString, Symbol};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let hash = RHash::new();
    /// hash.bulk_insert(&[Symbol::new("given_name").into_value(), RString::new("Arthur").into_value(), Symbol::new("family_name").into_value(), RString::new("Dent").into_value()]);
    /// let res: bool = eval!(r#"hash == {given_name: "Arthur", family_name: "Dent"}"#, hash).unwrap();
    /// assert!(res);
    /// ```
    #[cfg(any(ruby_gte_2_7, docsrs))]
    #[cfg_attr(docsrs, doc(cfg(ruby_gte_2_7)))]
    pub fn bulk_insert<T>(self, slice: &[T]) -> Result<(), Error>
    where
        T: ReprValue,
    {
        let ptr = slice.as_ptr() as *const VALUE;
        protect(|| unsafe {
            rb_hash_bulk_insert(slice.len() as c_long, ptr, self.as_rb_value());
            Ruby::get_unchecked().qnil()
        })?;
        Ok(())
    }

    /// Merges two hashes into one.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RHash, RString, Symbol};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let a: RHash = eval("{a: 1, b: 2}").unwrap();
    /// let b: RHash = eval("{b: 3, c: 4}").unwrap();
    /// a.update(b);
    ///
    /// // a is mutated, in case of conflicts b wins
    /// let res: bool = eval!("a == {a: 1, b: 3, c: 4}", a).unwrap();
    /// assert!(res);
    ///
    /// // b is unmodified
    /// let res: bool = eval!("b == {b: 3, c: 4}", b).unwrap();
    /// assert!(res);
    /// ```
    //
    // Implementation note: `rb_hash_update_by` takes a third optional argument,
    // a function pointer, the function being called to resolve conflicts.
    // Unfortunately there's no way to wrap this in a easy to use and safe Rust
    // api, so it has been omitted.
    pub fn update(self, other: RHash) -> Result<(), Error> {
        protect(|| unsafe {
            rb_hash_update_by(self.as_rb_value(), other.as_rb_value(), None);
            Ruby::get_unchecked().qnil()
        })?;
        Ok(())
    }

    /// Return the value for `key`, converting it to `U`.
    ///
    /// Returns hash's default if `key` is missing. See also
    /// [`lookup`](RHash::lookup), [`get`](RHash::get), and
    /// [`fetch`](RHash::fetch).
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{value::Qnil, RHash};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let hash = RHash::new();
    /// hash.aset("answer", 42);
    /// assert_eq!(hash.aref::<_, i64>("answer").unwrap(), 42);
    /// assert!(hash.aref::<_, Qnil>("missing").is_ok());
    /// assert_eq!(hash.aref::<_, Option<i64>>("answer").unwrap(), Some(42));
    /// assert_eq!(hash.aref::<_, Option<i64>>("missing").unwrap(), None);
    /// ```
    ///
    /// ```
    /// use magnus::{eval, RHash};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let hash = eval::<RHash>(r#"
    ///   hash = {"answer" => 42}
    ///   hash.default = 0
    ///   hash
    /// "#).unwrap();
    /// assert_eq!(hash.aref::<_, i64>("answer").unwrap(), 42);
    /// assert_eq!(hash.aref::<_, i64>("missing").unwrap(), 0);
    /// assert_eq!(hash.aref::<_, i64>(()).unwrap(), 0);
    /// ```
    pub fn aref<T, U>(self, key: T) -> Result<U, Error>
    where
        T: IntoValue,
        U: TryConvert,
    {
        let key = unsafe { key.into_value_unchecked() };
        protect(|| unsafe { Value::new(rb_hash_aref(self.as_rb_value(), key.as_rb_value())) })
            .and_then(TryConvert::try_convert)
    }

    /// Return the value for `key`, converting it to `U`.
    ///
    /// Returns `nil` if `key` is missing. See also [`aref`](RHash::aref),
    /// [`get`](RHash::get), and [`fetch`](RHash::fetch).
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, value::Qnil, RHash};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let hash = eval::<RHash>(r#"
    ///   hash = {"answer" => 42}
    ///   hash.default = 0
    ///   hash
    /// "#).unwrap();
    /// assert_eq!(hash.lookup::<_, i64>("answer").unwrap(), 42);
    /// assert!(hash.lookup::<_, Qnil>("missing").is_ok());
    /// assert_eq!(hash.lookup::<_, Option<i64>>("answer").unwrap(), Some(42));
    /// assert_eq!(hash.lookup::<_, Option<i64>>("missing").unwrap(), None);
    /// ```
    pub fn lookup<T, U>(self, key: T) -> Result<U, Error>
    where
        T: IntoValue,
        U: TryConvert,
    {
        let key = unsafe { key.into_value_unchecked() };
        protect(|| unsafe { Value::new(rb_hash_lookup(self.as_rb_value(), key.as_rb_value())) })
            .and_then(TryConvert::try_convert)
    }

    /// Return the value for `key` as a [`Value`].
    ///
    /// Returns `None` if `key` is missing. See also [`aref`](RHash::aref),
    /// [`lookup`](RHash::lookup), and [`fetch`](RHash::fetch).
    ///
    /// Note: It is possible for very badly behaved key objects to raise an
    /// error during hash lookup. This is unlikely, and for the simplicity of
    /// this api any errors will result in `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::RHash;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let hash = RHash::new();
    /// hash.aset("answer", 42);
    /// assert!(hash.get("answer").is_some());
    /// assert!(hash.get("missing").is_none());
    /// ```
    pub fn get<T>(self, key: T) -> Option<Value>
    where
        T: IntoValue,
    {
        let key = unsafe { key.into_value_unchecked() };
        protect(|| unsafe {
            Value::new(rb_hash_lookup2(
                self.as_rb_value(),
                key.as_rb_value(),
                QUNDEF.as_value().as_rb_value(),
            ))
        })
        .ok()
        .and_then(|v| (!v.is_undef()).then(|| v))
    }

    /// Return the value for `key`, converting it to `U`.
    ///
    /// Returns `Err` if `key` is missing. See also [`aref`](RHash::aref),
    /// [`lookup`](RHash::lookup), and [`get`](RHash::get).
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, value::Qnil, RHash};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let hash = eval::<RHash>(r#"
    ///   hash = {"answer" => 42}
    ///   hash.default = 0
    ///   hash
    /// "#).unwrap();
    /// assert_eq!(hash.fetch::<_, i64>("answer").unwrap(), 42);
    /// assert!(hash.fetch::<_, i64>("missing").is_err());
    /// assert_eq!(hash.fetch::<_, Option<i64>>("answer").unwrap(), Some(42));
    /// assert!(hash.fetch::<_, Option<i64>>("missing").is_err());
    /// ```
    pub fn fetch<T, U>(self, key: T) -> Result<U, Error>
    where
        T: IntoValue,
        U: TryConvert,
    {
        let key = unsafe { key.into_value_unchecked() };
        protect(|| unsafe { Value::new(rb_hash_fetch(self.as_rb_value(), key.as_rb_value())) })
            .and_then(TryConvert::try_convert)
    }

    /// Removes the key `key` from self and returns the associated value,
    /// converting it to `U`.
    ///
    /// Returns `nil` if `key` is missing.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, value::Qnil, RHash};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let hash = eval::<RHash>(r#"hash = {"answer" => 42}"#).unwrap();
    /// assert_eq!(hash.delete::<_, i64>("answer").unwrap(), 42);
    /// assert!(hash.delete::<_, Qnil>("answer").is_ok());
    /// ```
    pub fn delete<T, U>(self, key: T) -> Result<U, Error>
    where
        T: IntoValue,
        U: TryConvert,
    {
        let key = unsafe { key.into_value_unchecked() };
        protect(|| unsafe { Value::new(rb_hash_delete(self.as_rb_value(), key.as_rb_value())) })
            .and_then(TryConvert::try_convert)
    }

    /// Removes all entries from `self`.
    ///
    /// Errors if `self` is frozen.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RHash};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let hash: RHash = eval(r#"{"answer" => 42}"#).unwrap();
    /// assert!(!hash.is_empty());
    /// hash.clear().unwrap();
    /// assert!(hash.is_empty());
    /// ```
    pub fn clear(self) -> Result<(), Error> {
        protect(|| unsafe { Value::new(rb_hash_clear(self.as_rb_value())) })?;
        Ok(())
    }

    /// Run `func` for each key/value pair in `self`.
    ///
    /// The result of `func` is checked on each call, when it is
    /// [`ForEach::Continue`] the iteration will continue, [`ForEach::Stop`]
    /// will cause the iteration to stop, and [`ForEach::Delete`] will remove
    /// the key/value pair from `self` and then continue iteration.
    ///
    /// Returing an error from `func` behaves like [`ForEach::Stop`].
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, r_hash::ForEach, RHash};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let hash = eval::<RHash>(r#"{"foo" => 1, "bar" => 2, "baz" => 4, "qux" => 8}"#).unwrap();
    /// let mut found = None;
    /// hash.foreach(|key: String, value: i64| {
    ///     if value > 3 {
    ///         found = Some(key);
    ///         Ok(ForEach::Stop)
    ///     } else {
    ///         Ok(ForEach::Continue)
    ///     }
    /// }).unwrap();
    /// assert_eq!(found, Some(String::from("baz")));
    /// ```
    pub fn foreach<F, K, V>(self, mut func: F) -> Result<(), Error>
    where
        F: FnMut(K, V) -> Result<ForEach, Error>,
        K: TryConvert,
        V: TryConvert,
    {
        unsafe extern "C" fn iter<F, K, V>(key: VALUE, value: VALUE, arg: VALUE) -> c_int
        where
            F: FnMut(K, V) -> Result<ForEach, Error>,
            K: TryConvert,
            V: TryConvert,
        {
            let closure = &mut *(arg as *mut F);
            ForEachCallback::new(closure).call_handle_error(Value::new(key), Value::new(value))
                as c_int
        }

        unsafe {
            let arg = &mut func as *mut F as VALUE;
            protect(|| {
                let fptr = iter::<F, K, V> as unsafe extern "C" fn(VALUE, VALUE, VALUE) -> c_int;
                #[cfg(ruby_lt_2_7)]
                let fptr: unsafe extern "C" fn() -> c_int = std::mem::transmute(fptr);
                rb_hash_foreach(self.as_rb_value(), Some(fptr), arg);
                Ruby::get_unchecked().qnil()
            })?;
        }
        Ok(())
    }

    /// Return `self` converted to a Rust [`HashMap`].
    ///
    /// This will only convert to a map of 'owned' Rust native types. The types
    /// representing Ruby objects can not be stored in a heap-allocated
    /// datastructure like a [`HashMap`] as they are hidden from the mark phase
    /// of Ruby's garbage collector, and thus may be prematurely garbage
    /// collected in the following sweep phase.
    ///
    /// Errors if the conversion of any key or value fails.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    /// use magnus::{eval, RHash};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let r_hash = eval::<RHash>(r#"{"answer" => 42}"#).unwrap();
    /// let mut hash_map = HashMap::new();
    /// hash_map.insert(String::from("answer"), 42);
    /// assert_eq!(r_hash.to_hash_map().unwrap(), hash_map);
    /// ```
    pub fn to_hash_map<K, V>(self) -> Result<HashMap<K, V>, Error>
    where
        K: TryConvertOwned + Eq + Hash,
        V: TryConvertOwned,
    {
        let mut map = HashMap::new();
        self.foreach(|key, value| {
            map.insert(key, value);
            Ok(ForEach::Continue)
        })?;
        Ok(map)
    }

    /// Convert `self` to a Rust vector of key/value pairs.
    ///
    /// This will only convert to a map of 'owned' Rust native types. The types
    /// representing Ruby objects can not be stored in a heap-allocated
    /// datastructure like a [`Vec`] as they are hidden from the mark phase
    /// of Ruby's garbage collector, and thus may be prematurely garbage
    /// collected in the following sweep phase.
    ///
    /// Errors if the conversion of any key or value fails.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    /// use magnus::{eval, RHash};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let r_hash = eval::<RHash>(r#"{"answer" => 42}"#).unwrap();
    /// assert_eq!(r_hash.to_vec().unwrap(), vec![(String::from("answer"), 42)]);
    /// ```
    pub fn to_vec<K, V>(self) -> Result<Vec<(K, V)>, Error>
    where
        K: TryConvertOwned,
        V: TryConvertOwned,
    {
        let mut vec = Vec::with_capacity(self.len());
        self.foreach(|key, value| {
            vec.push((key, value));
            Ok(ForEach::Continue)
        })?;
        Ok(vec)
    }

    /// Return the number of entries in `self` as a Ruby [`Fixnum`].
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RHash};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let hash = eval::<RHash>(r#"{"foo" => 1, "bar" => 2, "baz" => 4}"#).unwrap();
    /// assert_eq!(hash.size().to_i64(), 3);
    /// ```
    pub fn size(self) -> Fixnum {
        unsafe { Fixnum::from_rb_value_unchecked(rb_hash_size(self.as_rb_value())) }
    }

    /// Return the number of entries in `self` as a Rust [`usize`].
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, RHash};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let hash = eval::<RHash>(r#"{"foo" => 1, "bar" => 2, "baz" => 4}"#).unwrap();
    /// assert_eq!(hash.len(), 3);
    /// ```
    pub fn len(self) -> usize {
        unsafe { rb_hash_size_num(self.as_rb_value()) as usize }
    }

    /// Return whether self contains any entries or not.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::RHash;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let hash = RHash::new();
    /// assert!(hash.is_empty());
    /// hash.aset("answer", 42);
    /// assert!(!hash.is_empty());
    /// ```
    pub fn is_empty(self) -> bool {
        self.len() == 0
    }
}

impl fmt::Display for RHash {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for RHash {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl IntoValue for RHash {
    fn into_value_with(self, _: &Ruby) -> Value {
        self.0.get()
    }
}

impl<K, V> IntoValue for HashMap<K, V>
where
    K: IntoValueFromNative,
    V: IntoValueFromNative,
{
    fn into_value_with(self, handle: &Ruby) -> Value {
        let hash = handle.hash_new();
        for (k, v) in self {
            let _ = hash.aset(k, v);
        }
        hash.into_value_with(handle)
    }
}

impl<K, V> FromIterator<(K, V)> for RHash
where
    K: IntoValue,
    V: IntoValue,
{
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = (K, V)>,
    {
        let hash = RHash::new();
        for (k, v) in iter {
            let _ = hash.aset(k, v);
        }
        hash
    }
}

impl Object for RHash {}

unsafe impl private::ReprValue for RHash {}

impl ReprValue for RHash {}

impl TryConvert for RHash {
    fn try_convert(val: Value) -> Result<Self, Error> {
        debug_assert_value!(val);
        if let Some(v) = Self::from_value(val) {
            return Ok(v);
        }
        unsafe {
            protect(|| Value::new(rb_check_hash_type(val.as_rb_value()))).and_then(|res| {
                Self::from_value(res).ok_or_else(|| {
                    Error::new(
                        exception::type_error(),
                        format!("no implicit conversion of {} into Hash", val.class()),
                    )
                })
            })
        }
    }
}
