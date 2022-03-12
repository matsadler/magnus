//! Types and functions for working with Ruby’s Hash class.

use std::{collections::HashMap, fmt, hash::Hash, iter::FromIterator, ops::Deref, os::raw::c_int};

use crate::{
    debug_assert_value,
    error::{protect, Error},
    object::Object,
    ruby_sys::{
        rb_check_hash_type, rb_hash_aref, rb_hash_aset, rb_hash_fetch, rb_hash_foreach,
        rb_hash_lookup, rb_hash_lookup2, rb_hash_new, rb_hash_size, ruby_value_type, VALUE,
    },
    try_convert::{TryConvert, TryConvertOwned},
    value::{Fixnum, NonZeroValue, Value, QNIL, QUNDEF},
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

/// A Value pointer to a RHash struct, Ruby's internal representation of Hash
/// objects.
///
/// All [`Value`] methods should be available on this type through [`Deref`],
/// but some may be missed by this documentation.
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
    /// # Examples
    ///
    /// ```
    /// use magnus::RHash;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let hash = RHash::new();
    /// assert!(hash.is_empty());
    /// ```
    pub fn new() -> RHash {
        unsafe { Self::from_rb_value_unchecked(rb_hash_new()) }
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
        K: Into<Value>,
        V: Into<Value>,
    {
        let key = key.into();
        let val = val.into();
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
        T: Into<Value>,
        U: TryConvert,
    {
        let key = key.into();
        unsafe {
            protect(|| Value::new(rb_hash_aref(self.as_rb_value(), key.as_rb_value())))
                .and_then(|v| v.try_convert())
        }
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
        T: Into<Value>,
        U: TryConvert,
    {
        let key = key.into();
        unsafe {
            protect(|| Value::new(rb_hash_lookup(self.as_rb_value(), key.as_rb_value())))
                .and_then(|v| v.try_convert())
        }
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
        T: Into<Value>,
    {
        let key = key.into();
        unsafe {
            protect(|| {
                Value::new(rb_hash_lookup2(
                    self.as_rb_value(),
                    key.as_rb_value(),
                    QUNDEF.to_value().as_rb_value(),
                ))
            })
            .ok()
            .and_then(|v| (!v.is_undef()).then(|| v))
        }
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
        T: Into<Value>,
        U: TryConvert,
    {
        let key = key.into();
        unsafe {
            protect(|| Value::new(rb_hash_fetch(self.as_rb_value(), key.as_rb_value())))
                .and_then(|v| v.try_convert())
        }
    }

    fn base_foreach<F>(self, mut func: F) -> Result<(), Error>
    where
        F: FnMut(Value, Value) -> ForEach,
    {
        unsafe extern "C" fn iter<F>(key: VALUE, value: VALUE, arg: VALUE) -> c_int
        where
            F: FnMut(Value, Value) -> ForEach,
        {
            let closure = &mut *(arg as *mut F);
            (closure)(Value::new(key), Value::new(value)) as c_int
        }

        unsafe {
            let arg = &mut func as *mut F as VALUE;
            protect(|| {
                let fptr = iter::<F> as unsafe extern "C" fn(VALUE, VALUE, VALUE) -> c_int;
                #[cfg(ruby_lt_2_7)]
                let fptr: unsafe extern "C" fn() -> c_int = std::mem::transmute(fptr);
                rb_hash_foreach(self.as_rb_value(), Some(fptr), arg);
                QNIL.into()
            })?;
        }
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
    /// hash.foreach(|key, value| {
    ///     if value.try_convert::<i64>()? > 3 {
    ///         found = Some(key.try_convert()?);
    ///         Ok(ForEach::Stop)
    ///     } else {
    ///         Ok(ForEach::Continue)
    ///     }
    /// }).unwrap();
    /// assert_eq!(found, Some(String::from("baz")));
    /// ```
    pub fn foreach<F>(self, mut func: F) -> Result<(), Error>
    where
        F: FnMut(Value, Value) -> Result<ForEach, Error>,
    {
        let mut res = Ok(());
        self.base_foreach(|key, value| match func(key, value) {
            Ok(v) => v,
            Err(e) => {
                res = Err(e);
                ForEach::Stop
            }
        })?;
        res
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
            map.insert(key.try_convert()?, value.try_convert()?);
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
            vec.push((key.try_convert()?, value.try_convert()?));
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
        self.size().to_usize().unwrap()
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

impl Deref for RHash {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
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

impl From<RHash> for Value {
    fn from(val: RHash) -> Self {
        *val
    }
}

impl<K, V> From<HashMap<K, V>> for Value
where
    K: Into<Value>,
    V: Into<Value>,
{
    fn from(map: HashMap<K, V>) -> Self {
        map.into_iter().collect::<RHash>().into()
    }
}

impl<K, V> FromIterator<(K, V)> for RHash
where
    K: Into<Value>,
    V: Into<Value>,
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

impl TryConvert for RHash {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        debug_assert_value!(val);
        if let Some(v) = Self::from_value(*val) {
            return Ok(v);
        }
        unsafe {
            protect(|| Value::new(rb_check_hash_type(val.as_rb_value()))).and_then(|res| {
                Self::from_value(res).ok_or_else(|| {
                    Error::type_error(format!(
                        "no implicit conversion of {} into Hash",
                        val.class()
                    ))
                })
            })
        }
    }
}
