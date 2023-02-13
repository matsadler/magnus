use std::fmt;

#[cfg(any(ruby_lte_3_1, docsrs))]
use rb_sys::{rb_binding_new, VALUE};

use crate::{
    class,
    error::Error,
    exception,
    into_value::IntoValue,
    object::Object,
    r_string::IntoRString,
    ruby_handle::RubyHandle,
    symbol::IntoSymbol,
    try_convert::TryConvert,
    value::{
        private::{self, ReprValue as _},
        NonZeroValue, ReprValue, Value,
    },
};

impl RubyHandle {
    #[cfg(any(ruby_lte_3_1, docsrs))]
    #[cfg_attr(docsrs, doc(cfg(ruby_lte_3_1)))]
    #[deprecated(since = "0.2.0", note = "this will no longer function as of Ruby 3.2")]
    pub fn binding_new(&self) -> Binding {
        crate::error::protect(|| unsafe { Binding::from_rb_value_unchecked(rb_binding_new()) })
            .unwrap()
    }
}

/// A Value known to be an instance of Binding.
///
/// See the [`ReprValue`] and [`Object`] traits for additional methods
/// available on this type.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Binding(NonZeroValue);

impl Binding {
    /// Create a new `Binding` from the current Ruby execution context.
    ///
    /// # Panics
    ///
    /// Panics if called from a non-Ruby thread.
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
    #[cfg(any(ruby_lte_3_1, docsrs))]
    #[cfg_attr(docsrs, doc(cfg(ruby_lte_3_1)))]
    #[deprecated(since = "0.2.0", note = "this will no longer function as of Ruby 3.2")]
    #[inline]
    pub fn new() -> Self {
        #[allow(deprecated)]
        get_ruby!().binding_new()
    }

    #[cfg(any(ruby_lte_3_1, docsrs))]
    #[inline]
    pub(crate) unsafe fn from_rb_value_unchecked(val: VALUE) -> Self {
        Self(NonZeroValue::new_unchecked(Value::new(val)))
    }

    /// Return `Some(Binding)` if `val` is a `Binding`, `None` otherwise.
    #[inline]
    pub fn from_value(val: Value) -> Option<Self> {
        unsafe {
            val.is_kind_of(class::binding())
                .then(|| Self(NonZeroValue::new_unchecked(val)))
        }
    }

    /// Evaluate a string of Ruby code within the binding's context.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Binding};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let binding = eval::<Binding>("binding").unwrap();
    /// assert_eq!(binding.eval::<_, i64>("1 + 2").unwrap(), 3);
    /// ```
    pub fn eval<T, U>(&self, s: T) -> Result<U, Error>
    where
        T: IntoRString,
        U: TryConvert,
    {
        self.funcall("eval", (unsafe { s.into_r_string_unchecked() },))
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
    /// use magnus::{eval, Binding, Value};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let binding = eval::<Binding>("binding").unwrap();
    /// binding.local_variable_set("a", 1);
    /// assert_eq!(binding.local_variable_get::<_, i64>("a").unwrap(), 1);
    /// assert!(binding.local_variable_get::<_, Value>("b").is_err());
    /// ```
    pub fn local_variable_get<N, T>(&self, name: N) -> Result<T, Error>
    where
        N: IntoSymbol,
        T: TryConvert,
    {
        self.funcall(
            "local_variable_get",
            (unsafe { name.into_symbol_unchecked() },),
        )
    }

    /// Set the named local variable in the binding.
    ///
    /// # Examples
    ///
    /// ```
    /// use magnus::{eval, Binding};
    /// # let _cleanup = unsafe { magnus::embed::init() };
    ///
    /// let binding = eval::<Binding>("binding").unwrap();
    /// binding.local_variable_set("a", 1);
    /// assert_eq!(binding.local_variable_get::<_, i64>("a").unwrap(), 1);
    /// ```
    pub fn local_variable_set<N, T>(&self, name: N, val: T)
    where
        N: IntoSymbol,
        T: IntoValue,
    {
        self.funcall::<_, _, Value>(
            "local_variable_set",
            (unsafe { name.into_symbol_unchecked() }, val),
        )
        .unwrap();
    }
}

impl fmt::Display for Binding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.to_s_infallible() })
    }
}

impl fmt::Debug for Binding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inspect())
    }
}

impl IntoValue for Binding {
    fn into_value_with(self, _: &RubyHandle) -> Value {
        self.0.get()
    }
}

impl Object for Binding {}

unsafe impl private::ReprValue for Binding {
    fn as_value(self) -> Value {
        self.0.get()
    }

    unsafe fn from_value_unchecked(val: Value) -> Self {
        Self(NonZeroValue::new_unchecked(val))
    }
}

impl ReprValue for Binding {}

impl TryConvert for Binding {
    fn try_convert(val: Value) -> Result<Self, Error> {
        Self::from_value(val).ok_or_else(|| {
            Error::new(
                exception::type_error(),
                format!("no implicit conversion of {} into Binding", unsafe {
                    val.classname()
                },),
            )
        })
    }
}

/// Evaluate a literal string of Ruby code with the given local variables.
///
/// Any type that implements [`IntoValue`] can be passed to Ruby.
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
        $crate::eval::<$crate::Binding>("binding").unwrap().eval($crate::r_string!($s))
    }};
    ($s:literal, $($rest:tt)*) => {{
        let binding = $crate::eval::<$crate::Binding>("binding").unwrap();
        $crate::bind!(binding, $($rest)*);
        binding.eval($crate::r_string!($s))
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
