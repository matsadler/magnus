use std::{collections::HashMap, fmt, hash::Hash, iter::FromIterator, ops::Deref};

use crate::{
    debug_assert_value,
    error::{protect, Error},
    object::Object,
    ruby_sys::{
        rb_check_hash_type, rb_hash_aref, rb_hash_aset, rb_hash_fetch, rb_hash_lookup,
        rb_hash_lookup2, rb_hash_new, ruby_value_type, VALUE,
    },
    try_convert::{TryConvert, TryConvertOwned},
    value::{NonZeroValue, Qundef, Value},
};

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RHash(NonZeroValue);

impl RHash {
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

    pub fn new() -> RHash {
        unsafe { Self::from_rb_value_unchecked(rb_hash_new()) }
    }

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

    /// returns hash's default if `key` is missing. See also `lookup`, `get`,
    /// and `fetch`.
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

    /// returns `nil` if `key` is missing. See also `aref`, `get`, and `fetch`.
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

    /// returns `None` if `key` is missing. See also `aref`, `lookup`, and
    /// `fetch`.
    ///
    /// Note: It is possible for very badly behaved key objects to raise an
    /// error during hash lookup. This is unlikely, and for the simplicity of
    /// this api any errors will result in `None`.
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
                    Qundef::new().to_value().as_rb_value(),
                ))
            })
            .ok()
            .and_then(|v| (!v.is_undef()).then(|| v))
        }
    }

    /// returns `Err` if `key` is missing. See also `aref`, `lookup`, and `get`.
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

    pub fn to_hash_map<K, V>(self) -> Result<HashMap<K, V>, Error>
    where
        K: TryConvertOwned + Eq + Hash,
        V: TryConvertOwned,
    {
        let mut map = HashMap::new();
        for res in self.enumeratorize("each", ()) {
            let (k, v) = res?.try_convert()?;
            map.insert(k, v);
        }
        Ok(map)
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
