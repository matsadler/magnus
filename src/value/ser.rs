use crate::{Error, RArray, RHash, RString, Symbol, TryConvert, Value};
use serde::ser::{
    Serialize, SerializeMap, SerializeSeq, SerializeStruct, SerializeStructVariant, SerializeTuple,
    SerializeTupleStruct, SerializeTupleVariant,
};

/// Serialize Rust data to a Ruby [`Value`].
///
/// The most basic Rust types are converted as follows:
///
/// | Rust type                 | Ruby value                          |
/// |---------------------------|-------------------------------------|
/// | `()`                      | `nil`                               |
/// | `bool`                    | `true` or `false`                   |
/// | `i8`, `i16`, `i32`, `i64` | An `Integer`                        |
/// | `u8`, `u16`, `u32`, `u64` | An `Integer`                        |
/// | `f32` or `f64`            | A `Float`                           |
/// | `char`                    | A `String` with UTF-8 encoding      |
/// | `&str`                    | A `String` with UTF-8 encoding      |
/// | `String`                  | A `String` with UTF-8 encoding      |
/// | `&[u8]`                   | A `String` with ASCII-8BIT encoding |
///
/// ```
/// use magnus::{Integer, RString, value::serialize};
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// let magic: Integer = serialize(&1234).unwrap();
/// assert_eq!(1234, magic.to_u64().unwrap());
///
/// let greeting: RString = serialize("Hello, world!").unwrap();
/// assert_eq!("Hello, world!", greeting.to_string().unwrap());
/// ```
///
/// ### `Option`
///
/// `None` is converted to `nil`. For an `Option<T>`, `Some` is unwrapped and its `T` value is
/// recursively serialized.
///
/// ```
/// use magnus::{Integer, Value, value::serialize};
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// let magic: Option<u64> = None;
/// let magic: Value = serialize(&magic).unwrap();
/// assert!(magic.is_nil());
///
/// let magic: Option<u64> = Some(1234);
/// let magic: Integer = serialize(&magic).unwrap();
/// assert_eq!(1234, magic.to_u64().unwrap());
/// ```
///
/// ### Structs
///
/// A unit struct (`A` in the example code below) is converted to `nil`.
///
/// A newtype struct (`B`) is unwrapped. Its value is recursively serialized.
///
/// A tuple struct (`C`) is converted to an `Array`. The `Array` contains the struct's fields,
/// recursively serialized.
///
/// A struct with named fields (`D`) is converted to a `Hash` with the field names as `Symbol`
/// keys. The field values are recursively serialized.
///
/// ```
/// use magnus::{Integer, RArray, RHash, Symbol, Value, value::serialize};
/// use serde::Serialize;
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// #[derive(Serialize)]
/// struct A;
///
/// #[derive(Serialize)]
/// struct B(u16);
///
/// #[derive(Serialize)]
/// struct C(u16, bool, B);
///
/// #[derive(Serialize)]
/// struct D {
///     foo: u16,
///     bar: bool,
///     baz: B
/// }
///
/// let a: Value = serialize(&A).unwrap();
/// assert!(a.is_nil());
///
/// let b: Integer = serialize(&B(1234)).unwrap();
/// assert_eq!(1234, b.to_u64().unwrap());
///
/// let c: RArray = serialize(&C(1234, false, B(5678))).unwrap();
/// assert_eq!(3, c.len());
/// assert_eq!(1234, c.entry(0).unwrap());
/// assert_eq!(false, c.entry(1).unwrap());
/// assert_eq!(5678, c.entry(2).unwrap());
///
/// let d: RHash = serialize(&D { foo: 1234, bar: false, baz: B(5678) }).unwrap();
/// assert_eq!(1234, d.lookup(Symbol::new("foo")).unwrap());
/// assert_eq!(false, d.lookup(Symbol::new("bar")).unwrap());
/// assert_eq!(5678, d.lookup(Symbol::new("baz")).unwrap());
/// ```
///
/// ### Enums
///
/// A unit enum variant (`A::Z` in the example code below) is converted to the name of the
/// variant as a `String` (`"Z"`).
///
/// All other types of enum variants (`A::Y`, `A::X`, `A::W`) are converted to a `Hash` with one
/// key: the name of the variant as a `String` (`"Y"`', `"X"`, `"W"`).
///
/// For a newtype enum variant (`A::Y`), the value keyed by the variant name is the variant's value
/// recursively serialized.
///
/// For a tuple enum variant (`A::X`), the value keyed by the variant name is an `Array` containing
/// the variant's fields recursively serialized.
///
/// For a struct enum variant (`A::W`), the value keyed by the variant name is a `Hash` with the
/// variant's field names as `Symbol` keys. The field values are recursively serialized.
///
/// ```
/// use magnus::{Integer, RArray, RHash, RString, Symbol, Value, value::serialize};
/// use serde::Serialize;
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// #[derive(Serialize)]
/// enum A {
///     Z,
///     Y(u16),
///     X(u16, bool, Box<A>),
///     W {
///         foo: u16,
///         bar: bool,
///         baz: Box<A>
///     }
/// }
///
/// let a: RString = serialize(&A::Z).unwrap();
/// assert_eq!("Z", a.to_string().unwrap());
///
/// let a: RHash = serialize(&A::Y(1234)).unwrap();
/// assert_eq!(1, a.len());
/// assert_eq!(1234, a.lookup("Y").unwrap());
///
/// let a: RHash = serialize(&A::X(1234, false, Box::new(A::Y(5678)))).unwrap();
/// let ax: RArray = a.lookup("X").unwrap();
/// assert_eq!(3, ax.len());
/// assert_eq!(1234, ax.entry(0).unwrap());
/// assert_eq!(false, ax.entry(1).unwrap());
/// assert_eq!(5678, ax.entry::<RHash>(2).unwrap().lookup("Y").unwrap());
///
/// let a: RHash = serialize(&A::W { foo: 1234, bar: false, baz: Box::new(A::Y(5678)) }).unwrap();
/// let aw: RHash = a.lookup("W").unwrap();
/// assert_eq!(1234, aw.lookup(Symbol::new("foo")).unwrap());
/// assert_eq!(false, aw.lookup(Symbol::new("bar")).unwrap());
/// let awbaz: RHash = aw.lookup(Symbol::new("baz")).unwrap();
/// assert_eq!(5678, awbaz.lookup("Y").unwrap());
/// ```
pub fn serialize<T: Serialize + ?Sized, U: TryConvert>(value: &T) -> Result<U, Error> {
    value.serialize(Serializer)?.try_convert()
}

struct Serializer;

impl serde::Serializer for Serializer {
    type Ok = Value;
    type Error = Error;

    type SerializeSeq = SeqSerializer;
    type SerializeTuple = SeqSerializer;
    type SerializeTupleStruct = SeqSerializer;
    type SerializeTupleVariant = TupleVariantSerializer;
    type SerializeMap = MapSerializer;
    type SerializeStruct = StructSerializer;
    type SerializeStructVariant = StructVariantSerializer;

    fn serialize_bool(self, value: bool) -> Result<Self::Ok, Self::Error> {
        Ok(value.into())
    }

    fn serialize_i8(self, value: i8) -> Result<Self::Ok, Self::Error> {
        Ok(value.into())
    }

    fn serialize_i16(self, value: i16) -> Result<Self::Ok, Self::Error> {
        Ok(value.into())
    }

    fn serialize_i32(self, value: i32) -> Result<Self::Ok, Self::Error> {
        Ok(value.into())
    }

    fn serialize_i64(self, value: i64) -> Result<Self::Ok, Self::Error> {
        Ok(value.into())
    }

    fn serialize_u8(self, value: u8) -> Result<Self::Ok, Self::Error> {
        Ok(value.into())
    }

    fn serialize_u16(self, value: u16) -> Result<Self::Ok, Self::Error> {
        Ok(value.into())
    }

    fn serialize_u32(self, value: u32) -> Result<Self::Ok, Self::Error> {
        Ok(value.into())
    }

    fn serialize_u64(self, value: u64) -> Result<Self::Ok, Self::Error> {
        Ok(value.into())
    }

    fn serialize_f32(self, value: f32) -> Result<Self::Ok, Self::Error> {
        Ok(value.into())
    }

    fn serialize_f64(self, value: f64) -> Result<Self::Ok, Self::Error> {
        Ok(value.into())
    }

    fn serialize_char(self, value: char) -> Result<Self::Ok, Self::Error> {
        Ok(value.into())
    }

    fn serialize_str(self, value: &str) -> Result<Self::Ok, Self::Error> {
        Ok(value.into())
    }

    fn serialize_bytes(self, value: &[u8]) -> Result<Self::Ok, Self::Error> {
        Ok(RString::from_slice(value).into())
    }

    fn serialize_none(self) -> Result<Self::Ok, Self::Error> {
        Ok(().into())
    }

    fn serialize_some<T: Serialize + ?Sized>(self, value: &T) -> Result<Self::Ok, Self::Error> {
        value.serialize(self)
    }

    fn serialize_unit(self) -> Result<Self::Ok, Self::Error> {
        Ok(().into())
    }

    fn serialize_unit_struct(self, _name: &'static str) -> Result<Self::Ok, Self::Error> {
        Ok(().into())
    }

    fn serialize_unit_variant(
        self,
        _name: &'static str,
        _index: u32,
        variant: &'static str,
    ) -> Result<Self::Ok, Self::Error> {
        Ok(variant.into())
    }

    fn serialize_newtype_struct<T: Serialize + ?Sized>(
        self,
        _name: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error> {
        value.serialize(self)
    }

    fn serialize_newtype_variant<T: Serialize + ?Sized>(
        self,
        _name: &'static str,
        _index: u32,
        variant: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error> {
        let hash = RHash::new();
        hash.aset(variant, value.serialize(self)?)?;
        Ok(hash.into())
    }

    fn serialize_seq(self, len: Option<usize>) -> Result<Self::SerializeSeq, Self::Error> {
        Ok(SeqSerializer {
            array: RArray::with_capacity(len.unwrap_or(0)),
        })
    }

    fn serialize_tuple(self, len: usize) -> Result<Self::SerializeTuple, Self::Error> {
        self.serialize_seq(Some(len))
    }

    fn serialize_tuple_struct(
        self,
        _name: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleStruct, Self::Error> {
        self.serialize_seq(Some(len))
    }

    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        _index: u32,
        variant: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleVariant, Self::Error> {
        Ok(TupleVariantSerializer {
            variant,
            array: RArray::with_capacity(len),
        })
    }

    fn serialize_map(self, len: Option<usize>) -> Result<Self::SerializeMap, Self::Error> {
        Ok(MapSerializer {
            hash: RHash::with_capacity(len.unwrap_or(0)),
            key: None,
        })
    }

    fn serialize_struct(
        self,
        _name: &'static str,
        len: usize,
    ) -> Result<Self::SerializeStruct, Self::Error> {
        Ok(StructSerializer {
            hash: RHash::with_capacity(len),
        })
    }

    fn serialize_struct_variant(
        self,
        _name: &'static str,
        _index: u32,
        variant: &'static str,
        len: usize,
    ) -> Result<Self::SerializeStructVariant, Self::Error> {
        Ok(StructVariantSerializer {
            variant,
            hash: RHash::with_capacity(len),
        })
    }
}

struct SeqSerializer {
    array: RArray,
}

impl SerializeSeq for SeqSerializer {
    type Ok = Value;
    type Error = Error;

    fn serialize_element<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<(), Self::Error> {
        self.array.push(value.serialize(Serializer)?)
    }

    fn end(self) -> Result<Self::Ok, self::Error> {
        Ok(self.array.into())
    }
}

impl SerializeTuple for SeqSerializer {
    type Ok = Value;
    type Error = Error;

    fn serialize_element<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<(), Self::Error> {
        <Self as SerializeSeq>::serialize_element(self, value)
    }

    fn end(self) -> Result<Self::Ok, self::Error> {
        <Self as SerializeSeq>::end(self)
    }
}

impl SerializeTupleStruct for SeqSerializer {
    type Ok = Value;
    type Error = Error;

    fn serialize_field<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<(), Self::Error> {
        <Self as SerializeSeq>::serialize_element(self, value)
    }

    fn end(self) -> Result<Self::Ok, self::Error> {
        <Self as SerializeSeq>::end(self)
    }
}

struct TupleVariantSerializer {
    variant: &'static str,
    array: RArray,
}

impl SerializeTupleVariant for TupleVariantSerializer {
    type Ok = Value;
    type Error = Error;

    fn serialize_field<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<(), Self::Error> {
        self.array.push(value.serialize(Serializer)?)
    }

    fn end(self) -> Result<Self::Ok, self::Error> {
        let hash = RHash::with_capacity(1);
        hash.aset(self.variant, self.array)?;
        Ok(hash.into())
    }
}

struct MapSerializer {
    hash: RHash,
    key: Option<Value>,
}

impl SerializeMap for MapSerializer {
    type Ok = Value;
    type Error = Error;

    fn serialize_key<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<(), Self::Error> {
        self.key = Some(value.serialize(Serializer)?);
        Ok(())
    }

    fn serialize_value<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<(), Self::Error> {
        self.hash
            .aset(self.key.unwrap(), value.serialize(Serializer)?)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(self.hash.into())
    }
}

struct StructSerializer {
    hash: RHash,
}

impl SerializeStruct for StructSerializer {
    type Ok = Value;
    type Error = Error;

    fn serialize_field<T: Serialize + ?Sized>(
        &mut self,
        name: &'static str,
        value: &T,
    ) -> Result<(), Self::Error> {
        self.hash
            .aset(Symbol::new(name), value.serialize(Serializer)?)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(self.hash.into())
    }
}

struct StructVariantSerializer {
    variant: &'static str,
    hash: RHash,
}

impl SerializeStructVariant for StructVariantSerializer {
    type Ok = Value;
    type Error = Error;

    fn serialize_field<T: Serialize + ?Sized>(
        &mut self,
        name: &'static str,
        value: &T,
    ) -> Result<(), Self::Error> {
        self.hash
            .aset(Symbol::new(name), value.serialize(Serializer)?)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        let hash = RHash::with_capacity(1);
        hash.aset(self.variant, self.hash)?;
        Ok(hash.into())
    }
}
