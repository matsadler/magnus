use crate::{Error, Fixnum, RArray, RBignum, RFloat, RHash, RString, Symbol, Value};
use rb_sys::ruby_value_type;
use serde::{
    de::{
        Deserialize, DeserializeSeed, EnumAccess, IntoDeserializer, MapAccess, SeqAccess,
        Unexpected, VariantAccess, Visitor,
    },
    forward_to_deserialize_any,
};

/// Deserialize a Ruby [`Value`] to Rust.
///
/// See [`crate::value::serialize`] for the expected Ruby formats of various Rust types.
///
/// ```
/// use magnus::{eval, Value, value::deserialize};
/// use serde::{Deserialize};
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// #[derive(Deserialize, Debug)]
/// struct A {
///     b: B,
///     c: [i32; 3],
///     d: Option<D>,
/// }
///
/// #[derive(Deserialize, PartialEq, Debug)]
/// struct B(u32);
///
/// #[derive(Deserialize, PartialEq, Debug)]
/// enum D {
///     A { a: String },
/// }
///
/// let a: Value = eval(
///     r#"
///     {
///       b: 1234,
///       c: [123, -456, 789],
///       d: {
///         "A" => { a: "test" }
///       }
///     }
///     "#,
/// )
/// .unwrap();
///
/// let a: A = deserialize(a).unwrap();
///
/// assert_eq!(B(1234), a.b);
/// assert_eq!([123, -456, 789], a.c);
/// assert_eq!(
///     Some(D::A {
///         a: String::from("test")
///     }),
///     a.d
/// );
/// ```
pub fn deserialize<'i, T, U>(value: T) -> Result<U, Error>
where
    T: Into<Value>,
    U: Deserialize<'i>,
{
    U::deserialize(Deserializer {
        value: value.into(),
    })
}

struct Deserializer {
    value: Value,
}

impl<'i> serde::Deserializer<'i> for Deserializer {
    type Error = Error;

    fn deserialize_any<T: Visitor<'i>>(self, visitor: T) -> Result<T::Value, Self::Error> {
        match self.value.rb_type() {
            ruby_value_type::RUBY_T_NIL => visitor.visit_unit(),

            ruby_value_type::RUBY_T_TRUE | ruby_value_type::RUBY_T_FALSE => {
                visitor.visit_bool(self.value.to_bool())
            }

            ruby_value_type::RUBY_T_FIXNUM => {
                let fixnum = unsafe { Fixnum::from_rb_value_unchecked(self.value.as_rb_value()) };

                visitor.visit_i64(fixnum.to_i64())
            }

            ruby_value_type::RUBY_T_BIGNUM => {
                let bignum = unsafe { RBignum::from_rb_value_unchecked(self.value.as_rb_value()) };

                if bignum.is_negative() {
                    visitor.visit_i64(bignum.to_i64()?)
                } else {
                    visitor.visit_u64(bignum.to_u64()?)
                }
            }

            ruby_value_type::RUBY_T_FLOAT => {
                let float = unsafe { RFloat::from_rb_value_unchecked(self.value.as_rb_value()) };

                visitor.visit_f64(float.to_f64())
            }

            ruby_value_type::RUBY_T_STRING => {
                let string = unsafe { RString::from_rb_value_unchecked(self.value.as_rb_value()) };

                visitor.visit_string(string.to_string()?)
            }

            ruby_value_type::RUBY_T_SYMBOL => {
                let symbol = unsafe { Symbol::from_rb_value_unchecked(self.value.as_rb_value()) };

                visitor.visit_string(symbol.name()?.to_string())
            }

            ruby_value_type::RUBY_T_ARRAY => {
                let array = unsafe { RArray::from_rb_value_unchecked(self.value.as_rb_value()) };

                visitor.visit_seq(ArrayDeserializer::new(&array))
            }

            ruby_value_type::RUBY_T_HASH => {
                let hash = unsafe { RHash::from_rb_value_unchecked(self.value.as_rb_value()) };

                visitor.visit_map(HashDeserializer::new(&hash)?)
            }

            _ => Err(Error::new(
                crate::exception::type_error(),
                format!(
                    "can't deserialize {}",
                    unsafe { self.value.classname() }.into_owned()
                ),
            )),
        }
    }

    fn deserialize_bytes<T>(self, visitor: T) -> Result<T::Value, Error>
    where
        T: Visitor<'i>,
    {
        visitor.visit_bytes(self.value.try_convert::<String>()?.as_bytes())
    }

    fn deserialize_byte_buf<T>(self, visitor: T) -> Result<T::Value, Error>
    where
        T: Visitor<'i>,
    {
        visitor.visit_bytes(self.value.try_convert::<String>()?.as_bytes())
    }

    fn deserialize_option<T>(self, visitor: T) -> Result<T::Value, Error>
    where
        T: Visitor<'i>,
    {
        if self.value.is_nil() {
            visitor.visit_none()
        } else {
            visitor.visit_some(self)
        }
    }

    fn deserialize_enum<T>(
        self,
        _name: &'static str,
        _variants: &'static [&'static str],
        visitor: T,
    ) -> Result<T::Value, Error>
    where
        T: Visitor<'i>,
    {
        match self.value.rb_type() {
            ruby_value_type::RUBY_T_STRING => {
                let variant = unsafe { RString::from_rb_value_unchecked(self.value.as_rb_value()) };

                visitor.visit_enum(EnumDeserializer {
                    variant: variant.to_string()?,
                    value: None,
                })
            }

            ruby_value_type::RUBY_T_HASH => {
                let hash = unsafe { RHash::from_rb_value_unchecked(self.value.as_rb_value()) };

                if hash.len() == 1 {
                    let key: String = hash.keys()?.entry(0)?;
                    let value = hash.get(key.as_str());

                    visitor.visit_enum(EnumDeserializer {
                        variant: key,
                        value,
                    })
                } else {
                    Err(Error::new(
                        crate::exception::type_error(),
                        format!("can't deserialize Hash of length {} to Enum", hash.len()),
                    ))
                }
            }

            _ => Err(Error::new(
                crate::exception::type_error(),
                format!(
                    "can't deserialize {} to Enum",
                    unsafe { self.value.classname() }.into_owned()
                ),
            )),
        }
    }

    fn deserialize_newtype_struct<T>(
        self,
        _name: &'static str,
        visitor: T,
    ) -> Result<T::Value, Error>
    where
        T: Visitor<'i>,
    {
        visitor.visit_newtype_struct(self)
    }

    fn deserialize_ignored_any<T>(self, visitor: T) -> Result<T::Value, Error>
    where
        T: Visitor<'i>,
    {
        visitor.visit_unit()
    }

    forward_to_deserialize_any! {
        <T: Visitor<'i>>
        bool i8 i16 i32 i64 i128 u8 u16 u32 u64 u128 f32 f64 char str string
        unit unit_struct seq tuple tuple_struct map struct identifier
    }
}

struct ArrayDeserializer<'i> {
    array: &'i RArray,
    index: isize,
}

impl<'i> ArrayDeserializer<'i> {
    fn new(array: &'i RArray) -> Self {
        Self { array, index: 0 }
    }
}

impl<'i, 'de> SeqAccess<'de> for ArrayDeserializer<'i> {
    type Error = Error;

    fn next_element_seed<T>(&mut self, seed: T) -> Result<Option<T::Value>, Error>
    where
        T: DeserializeSeed<'de>,
    {
        if self.index as usize >= self.array.len() {
            return Ok(None);
        }

        let value: Value = self.array.entry(self.index)?;
        self.index += 1;

        seed.deserialize(Deserializer { value }).map(Some)
    }
}

struct HashDeserializer<'i> {
    hash: &'i RHash,
    keys: RArray,
    index: isize,
}

impl<'i> HashDeserializer<'i> {
    fn new(hash: &'i RHash) -> Result<Self, Error> {
        Ok(Self {
            hash,
            keys: hash.keys()?,
            index: 0,
        })
    }
}

impl<'i, 'de> MapAccess<'de> for HashDeserializer<'i> {
    type Error = Error;

    fn next_key_seed<K>(&mut self, seed: K) -> Result<Option<K::Value>, Self::Error>
    where
        K: DeserializeSeed<'de>,
    {
        if self.index as usize >= self.keys.len() {
            return Ok(None);
        }

        let key = self.keys.entry(self.index)?;

        seed.deserialize(Deserializer { value: key }).map(Some)
    }

    fn next_value_seed<T>(&mut self, seed: T) -> Result<T::Value, Self::Error>
    where
        T: DeserializeSeed<'de>,
    {
        if self.index as usize >= self.hash.len() {
            return Err(Error::new(
                crate::exception::index_error(),
                format!(
                    "index out of range (expected 0...{}, got {})",
                    self.hash.len(),
                    self.index,
                ),
            ));
        }

        let key: Value = self.keys.entry(self.index)?;
        let value: Value = self.hash.aref(key)?;
        self.index += 1;

        seed.deserialize(Deserializer { value })
    }
}

struct EnumDeserializer {
    variant: String,
    value: Option<Value>,
}

impl<'i> EnumAccess<'i> for EnumDeserializer {
    type Variant = VariantDeserializer;
    type Error = Error;

    fn variant_seed<T>(self, seed: T) -> Result<(T::Value, Self::Variant), Error>
    where
        T: DeserializeSeed<'i>,
    {
        let deserializer = VariantDeserializer { value: self.value };
        seed.deserialize(self.variant.into_deserializer())
            .map(|value| (value, deserializer))
    }
}

struct VariantDeserializer {
    value: Option<Value>,
}

impl<'i> VariantAccess<'i> for VariantDeserializer {
    type Error = Error;

    fn unit_variant(self) -> Result<(), Self::Error> {
        if let Some(value) = self.value {
            deserialize(value)
        } else {
            Ok(())
        }
    }

    fn newtype_variant_seed<T>(self, seed: T) -> Result<T::Value, Self::Error>
    where
        T: DeserializeSeed<'i>,
    {
        if let Some(value) = self.value {
            seed.deserialize(Deserializer { value })
        } else {
            Err(serde::de::Error::invalid_type(
                Unexpected::UnitVariant,
                &"newtype variant",
            ))
        }
    }

    fn tuple_variant<T>(self, _len: usize, visitor: T) -> Result<T::Value, Self::Error>
    where
        T: Visitor<'i>,
    {
        if let Some(value) = self.value {
            if let Ok(array) = value.try_convert::<RArray>() {
                visitor.visit_seq(&mut ArrayDeserializer::new(&array))
            } else {
                Err(serde::de::Error::invalid_type(
                    Unexpected::Other(&(unsafe { value.classname() }.to_owned())),
                    &"tuple variant",
                ))
            }
        } else {
            Err(serde::de::Error::invalid_type(
                Unexpected::UnitVariant,
                &"tuple variant",
            ))
        }
    }

    fn struct_variant<T>(
        self,
        _fields: &'static [&'static str],
        visitor: T,
    ) -> Result<T::Value, Self::Error>
    where
        T: Visitor<'i>,
    {
        if let Some(value) = self.value {
            if let Ok(hash) = value.try_convert::<RHash>() {
                visitor.visit_map(&mut HashDeserializer::new(&hash)?)
            } else {
                Err(serde::de::Error::invalid_type(
                    Unexpected::Other(&(unsafe { value.classname() }.to_owned())),
                    &"struct variant",
                ))
            }
        } else {
            Err(serde::de::Error::invalid_type(
                Unexpected::UnitVariant,
                &"struct variant",
            ))
        }
    }
}
