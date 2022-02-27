use std::{fmt, ops::Deref};

use crate::{
    class::RClass,
    error::{protect, Error},
    object::Object,
    ruby_sys::{rb_binding_new, rb_cBinding},
    symbol::Symbol,
    try_convert::TryConvert,
    value::{NonZeroValue, Value},
};

/// A Value known to be an instance of Binding.
///
/// All [`Value`] methods should be available on this type through [`Deref`],
/// but some may be missed by this documentation.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Binding(NonZeroValue);

impl Binding {
    /// Create a new `Binding` from the current Ruby execution context.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::Binding;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let binding = Binding::new();
    /// ```
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        unsafe {
            protect(|| Value::new(rb_binding_new()))
                .map(|v| Self(NonZeroValue::new_unchecked(v)))
                .unwrap()
        }
    }

    /// Return `Some(Binding)` if `val` is a `Binding`, `None` otherwise.
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            val.is_kind_of(RClass::from_rb_value_unchecked(rb_cBinding))
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    /// Evaluate a string of Ruby code within the binding's context.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::Binding;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let binding = Binding::new();
    /// assert_eq!(binding.eval::<i64>("1 + 2").unwrap(), 3);
    /// ```
    pub fn eval<T>(&self, s: &str) -> Result<T, Error>
    where
        T: TryConvert,
    {
        self.funcall("eval", (s,))
    }

    /// Get the named local variable from the binding.
    ///
    /// Returns `Ok(T)` if the method returns without error and the return
    /// value converts to a `T`, or returns `Err` if the local variable does
    /// not exist or the conversion fails.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{Binding, Value};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let binding = Binding::new();
    /// binding.local_variable_set("a", 1);
    /// assert_eq!(binding.local_variable_get::<_, i64>("a").unwrap(), 1);
    /// assert!(binding.local_variable_get::<_, Value>("b").is_err());
    /// ```
    pub fn local_variable_get<N, T>(&self, name: N) -> Result<T, Error>
    where
        N: Into<Symbol>,
        T: TryConvert,
    {
        self.funcall("local_variable_get", (name.into(),))
    }

    /// Set the named local variable in the binding.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::Binding;
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let binding = Binding::new();
    /// binding.local_variable_set("a", 1);
    /// assert_eq!(binding.local_variable_get::<_, i64>("a").unwrap(), 1);
    /// ```
    pub fn local_variable_set<N, T>(&self, name: N, val: T)
    where
        N: Into<Symbol>,
        T: Into<Value>,
    {
        self.funcall::<_, _, Value>("local_variable_set", (name.into(), val))
            .unwrap();
    }
}

impl Deref for Binding {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        self.0.get_ref()
    }
}

impl fmt::Display for Binding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for Binding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.deref().inspect())
    }
}

impl From<Binding> for Value {
    fn from(val: Binding) -> Self {
        *val
    }
}

impl Object for Binding {}

impl TryConvert for Binding {
    #[inline]
    fn try_convert(val: &Value) -> Result<Self, Error> {
        Self::from_value(*val).ok_or_else(|| {
            Error::type_error(format!(
                "no implicit conversion of {} into Binding",
                unsafe { val.classname() },
            ))
        })
    }
}

/// Evaluate a string of Ruby code with the given local variables.
///
/// Any type that implements `Into<Value>` can be passed to Ruby.
///
/// See also the [`eval`](fn@crate::eval) function and [`Binding`].
///
/// # Examples
///
/// ```
/// # let _cleanup = unsafe { magnus::embed::init() };
/// let result: i64 = magnus::eval!("a + b", a = 1, b = 2).unwrap();
/// assert_eq!(result, 3)
/// ```
/// ```
/// # let _cleanup = unsafe { magnus::embed::init() };
/// let a = 1;
/// let b = 2;
/// let result: i64 = magnus::eval!("a + b", a, b).unwrap();
/// assert_eq!(result, 3);
/// ```
#[macro_export]
macro_rules! eval {
    ($s:literal) => {{
        $crate::eval($s)
    }};
    ($s:literal, $($rest:tt)*) => {{
        let binding = $crate::Binding::new();
        $crate::bind!(binding, $($rest)*);
        binding.eval($s)
    }}
}

#[doc(hidden)]
#[macro_export]
macro_rules! bind {
    ($binding:ident,) => {};
    ($binding:ident, $k:ident = $v:expr) => {{
        $binding.local_variable_set(stringify!($k), $v);
    }};
    ($binding:ident, $k:ident) => {{
        $binding.local_variable_set(stringify!($k), $k);
    }};
    ($binding:ident, $k:ident = $v:expr, $($rest:tt)*) => {{
        $binding.local_variable_set(stringify!($k), $v);
        $crate::bind!($binding, $($rest)*);
    }};
    ($binding:ident, $k:ident, $($rest:tt)*) => {{
        $binding.local_variable_set(stringify!($k), $k);
        $crate::bind!($binding, $($rest)*);
    }}
}
