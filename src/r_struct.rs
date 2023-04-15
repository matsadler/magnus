//! Types and functions for working with Ruby's Struct class.
//!
//! See also [`Ruby`](Ruby#struct) for more Struct related methods.

use std::{
    borrow::Cow,
    ffi::CString,
    fmt,
    os::raw::c_char,
    ptr::{null, NonNull},
    slice,
};

use rb_sys::{
    rb_struct_aref, rb_struct_aset, rb_struct_define, rb_struct_getmember, rb_struct_members,
    rb_struct_size, ruby_value_type, VALUE,
};
use seq_macro::seq;

use crate::{
    class::RClass,
    error::{protect, Error},
    into_value::IntoValue,
    object::Object,
    r_array::RArray,
    symbol::Symbol,
    try_convert::TryConvert,
    value::{self, private::ReprValue as _, IntoId, NonZeroValue, ReprValue, Value},
    Ruby,
};

// Ruby provides some inline functions to get a pointer to the struct's
// contents, but we have to reimplement those for Rust. The for that we need
// the definition of RStruct, but that isn't public, so we have to duplicate it
// here.
mod sys {
    #[cfg(ruby_lt_3_0)]
    use rb_sys::ruby_fl_type::RUBY_FL_USHIFT;
    #[cfg(ruby_gte_3_0)]
    use rb_sys::ruby_fl_ushift::RUBY_FL_USHIFT;
    use rb_sys::{ruby_fl_type, RBasic, VALUE};

    #[cfg(ruby_gte_2_7)]
    pub const EMBED_LEN_MAX: u32 = rb_sys::ruby_rvalue_flags::RVALUE_EMBED_LEN_MAX as u32;

    #[cfg(ruby_lt_2_7)]
    pub const EMBED_LEN_MAX: u32 = 3;

    pub const EMBED_LEN_MASK: u32 =
        ruby_fl_type::RUBY_FL_USER2 as u32 | ruby_fl_type::RUBY_FL_USER1 as u32;
    pub const EMBED_LEN_SHIFT: u32 = RUBY_FL_USHIFT as u32 + 1;

    #[repr(C)]
    #[derive(Copy, Clone)]
    pub struct RStruct {
        pub basic: RBasic,
        pub as_: As,
    }
    #[repr(C)]
    #[derive(Copy, Clone)]
    pub union As {
        pub heap: Heap,
        pub ary: [VALUE; EMBED_LEN_MAX as usize],
    }
    #[repr(C)]
    #[derive(Debug, Copy, Clone)]
    pub struct Heap {
        pub len: std::os::raw::c_long,
        pub ptr: *const VALUE,
    }
}

/// A Value pointer to a RStruct struct, Ruby’s internal representation of
/// 'Structs'.
///
/// See the [`ReprValue`] and [`Object`] traits for additional methods
/// available on this type.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct RStruct(NonZeroValue);

impl RStruct {
    /// Return `Some(RStruct)` if `val` is a `RStruct`, `None` otherwise.
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            (val.rb_type() == ruby_value_type::RUBY_T_STRUCT)
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        Self(NonZeroValue::new_unchecked(Value::new(val)))
    }

    fn as_internal(self) -> NonNull<sys::RStruct> {
        // safe as inner value is NonZero
        unsafe { NonNull::new_unchecked(self.0.get().as_rb_value() as *mut _) }
    }

    /// Return the members of the struct as a slice of [`Value`]s. The order
    /// will be the order the of the member names when the struct class was
    /// defined.
    ///
    /// # Safety
    ///
    /// Ruby may modify or free the memory backing the returned slice, the
    /// caller must ensure this does not happen.
    pub unsafe fn as_slice(&self) -> &[Value] {
        self.as_slice_unconstrained()
    }

    pub(crate) unsafe fn as_slice_unconstrained<'a>(self) -> &'a [Value] {
        debug_assert_value!(self);
        let r_basic = self.r_basic_unchecked();
        let flags = r_basic.as_ref().flags;
        if (flags & sys::EMBED_LEN_MASK as VALUE) != 0 {
            let len = (flags & sys::EMBED_LEN_MASK as VALUE) >> sys::EMBED_LEN_SHIFT as VALUE;
            slice::from_raw_parts(
                &self.as_internal().as_ref().as_.ary as *const VALUE as *const Value,
                len as usize,
            )
        } else {
            let h = self.as_internal().as_ref().as_.heap;
            slice::from_raw_parts(h.ptr as *const Value, h.len as usize)
        }
    }

    /// Return the value for the member at `index`, where members are ordered
    /// as per the member names when the struct class was defined.
    pub fn get<T>(self, index: usize) -> Result<T, Error>
    where
        T: TryConvert,
    {
        unsafe {
            let slice = self.as_slice();
            slice
                .get(index)
                .copied()
                .ok_or_else(|| {
                    Error::new(
                        Ruby::get_with(self).exception_index_error(),
                        format!(
                            "offset {} too large for struct(size:{})",
                            index,
                            slice.len()
                        ),
                    )
                })
                .and_then(TryConvert::try_convert)
        }
    }

    /// Return the value for the member at `index`.
    ///
    /// `index` may be an integer, string, or [`Symbol`].
    pub fn aref<T, U>(self, index: T) -> Result<U, Error>
    where
        T: IntoValue,
        U: TryConvert,
    {
        let index = Ruby::get_with(self).into_value(index);
        protect(|| unsafe { Value::new(rb_struct_aref(self.as_rb_value(), index.as_rb_value())) })
            .and_then(TryConvert::try_convert)
    }

    /// Return the value for the member at `index`.
    ///
    /// `index` may be an integer, string, or [`Symbol`].
    pub fn aset<T, U>(self, index: T, val: U) -> Result<(), Error>
    where
        T: IntoValue,
        U: IntoValue,
    {
        let handle = Ruby::get_with(self);
        let index = handle.into_value(index);
        let val = handle.into_value(val);
        unsafe {
            protect(|| {
                Value::new(rb_struct_aset(
                    self.as_rb_value(),
                    index.as_rb_value(),
                    val.as_rb_value(),
                ))
            })?;
        }
        Ok(())
    }

    /// Returns the count of members this struct has.
    pub fn size(self) -> usize {
        unsafe { usize::try_convert(Value::new(rb_struct_size(self.as_rb_value()))).unwrap() }
    }

    /// Returns the member names for this struct as [`Symbol`]s.
    pub fn members(self) -> Result<Vec<Cow<'static, str>>, Error> {
        unsafe {
            let array = RArray::from_rb_value_unchecked(rb_struct_members(self.as_rb_value()));
            array
                .as_slice()
                .iter()
                .map(|v| Symbol::from_value(*v).unwrap().name())
                .collect()
        }
    }

    /// Return the value for the member named `id`.
    pub fn getmember<T, U>(self, id: T) -> Result<U, Error>
    where
        T: IntoId,
        U: TryConvert,
    {
        let id = id.into_id_with(&Ruby::get_with(self));
        protect(|| unsafe { Value::new(rb_struct_getmember(self.as_rb_value(), id.as_rb_id())) })
            .and_then(TryConvert::try_convert)
    }
}

impl fmt::Display for RStruct {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for RStruct {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl IntoValue for RStruct {
    fn into_value_with(self, _: &Ruby) -> Value {
        self.0.get()
    }
}

impl Object for RStruct {}

unsafe impl value::private::ReprValue for RStruct {}

impl ReprValue for RStruct {}

impl TryConvert for RStruct {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Self::from_value(val).ok_or_else(|| {
            Error::new(
                Ruby::get_with(val).exception_type_error(),
                format!("no implicit conversion of {} into Struct", unsafe {
                    val.classname()
                },),
            )
        })
    }
}

/// # `Struct`
///
/// Functions that can be used to create Ruby `Struct` classes.
///
/// See also the [`struct`](self) module.
#[allow(missing_docs)]
impl Ruby {
    pub fn define_struct<T>(&self, name: Option<&str>, members: T) -> Result<RClass, Error>
    where
        T: StructMembers,
    {
        members.define(name)
    }
}

/// Define a Ruby Struct class.
///
/// `members` is a tuple of `&str`, of between lengths 1 to 12 inclusive.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread. See [`Ruby::define_struct`] for
/// the non-panicking version.
///
/// # Examples
///
/// When providing `None` for the `name` the struct class's name will be taken
/// from the first constant it is assigned to:
///
/// ```
/// use magnus::{define_global_const, prelude::*, r_struct::define_struct};
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// let struct_class = define_struct(None, ("foo", "bar")).unwrap();
/// define_global_const("Example", struct_class).unwrap();
///
/// assert_eq!(unsafe { struct_class.name().to_owned() }, "Example");
///
/// let instance = struct_class.new_instance((1, 2)).unwrap();
/// assert_eq!(instance.inspect(), "#<struct Example foo=1, bar=2>")
/// ```
///
/// When providing `Some("Name")` for the `name` the struct will be defined
/// under `Struct`:
///
/// ```
/// use magnus::{prelude::*, r_struct::define_struct};
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// let struct_class = define_struct(Some("Example"), ("foo", "bar")).unwrap();
///
/// assert_eq!(unsafe { struct_class.name().to_owned() }, "Struct::Example");
///
/// let instance = struct_class.new_instance((1, 2)).unwrap();
/// assert_eq!(instance.inspect(), "#<struct Struct::Example foo=1, bar=2>")
/// ```
#[cfg(feature = "friendly-api")]
#[inline]
pub fn define_struct<T>(name: Option<&str>, members: T) -> Result<RClass, Error>
where
    T: StructMembers,
{
    get_ruby!().define_struct(name, members)
}

mod private {
    use super::*;

    pub trait StructMembers {
        fn define(self, name: Option<&str>) -> Result<RClass, Error>;
    }
}
use private::StructMembers;

macro_rules! impl_struct_members {
    ($n:literal) => {
        seq!(N in 0..$n {
            impl StructMembers for (#(&str,)*) {
                fn define(self, name: Option<&str>) -> Result<RClass, Error> {
                    let name = name.map(|n| CString::new(n).unwrap());
                    #(let arg~N = CString::new(self.N).unwrap();)*
                    protect(|| unsafe {
                        RClass::from_rb_value_unchecked(rb_struct_define(
                            name.as_ref().map(|n| n.as_ptr()).unwrap_or_else(null),
                            #(arg~N.as_ptr(),)*
                            null::<c_char>(),
                        ))
                    })
                }
            }
        });
    }
}

seq!(N in 1..=12 {
    impl_struct_members!(N);
});
