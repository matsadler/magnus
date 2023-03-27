//! Derive and proc macros for magnus.
//!
//! ```
//! #[magnus::wrap(class = "RbPoint", free_immediately, size)]
//! struct Point {
//!     x: isize,
//!     y: isize,
//! }
//!
//! #[magnus::init]
//! fn init() -> Result<(), magnus::Error> {
//!     magnus::define_class("RbPoint", magnus::class::object())?;
//!     Ok(())
//! }
//! ```

#![warn(missing_docs)]

use proc_macro::TokenStream;
use syn::parse_macro_input;

mod init;
mod typed_data;
mod util;

/// Mark a function as the 'init' function to be run for a library when it is
/// `require`d by Ruby code.
///
/// The init function is used to define your Ruby modules & classes, bind
/// functions as Ruby methods, etc.
///
/// # Attributes
///
/// * `name = "..."` - sets the name of the init function exported for Ruby.
///   This default's to the current crate's name. The name will be prepended
///   with `Init_` and `-` will be replaced with `_`. This (minus the `Init_`
///   prefix) must match the name of the final `.so`/`.bundle` file.
///
/// # Examples
///
/// ```
/// fn distance(a: (f64, f64), b: (f64, f64)) -> f64 {
///     ((b.0 - a.0).powi(2) + (b.1 - a.1).powi(2)).sqrt()
/// }
///
/// #[magnus::init]
/// fn init() {
///     magnus::define_global_function("distance", magnus::function!(distance, 2));
/// }
/// ```
/// The init function can also return `Result<(), magnus::Error>`.
/// ```
/// use magnus::{class, define_module, function, method, prelude::*, Error};
///
/// #[magnus::wrap(class = "Euclid::Point", free_immediately, size)]
/// struct Point {
///     x: isize,
///     y: isize,
/// }
///
/// impl Point {
///     fn new(x: isize, y: isize) -> Self {
///         Self { x, y }
///     }
///
///     fn x(&self) -> isize {
///         self.x
///     }
///
///     fn y(&self) -> isize {
///         self.y
///     }
/// }
///
/// #[magnus::init]
/// fn init() -> Result<(), Error> {
///     let module = define_module("Euclid")?;
///     let class = module.define_class("Point", class::object())?;
///     class.define_singleton_method("new", function!(Point::new, 2))?;
///     class.define_method("x", method!(Point::x, 0))?;
///     class.define_method("y", method!(Point::y, 0))?;
///     Ok(())
/// }
/// ```
/// Setting the name.
/// ```
/// #[magnus::init(name = "example")]
/// fn init() {
///     ()
/// }
/// ```
#[proc_macro_attribute]
pub fn init(attrs: TokenStream, item: TokenStream) -> TokenStream {
    let mut name = None;
    if !attrs.is_empty() {
        let attr_parser = syn::meta::parser(|meta| {
            if meta.path.is_ident("name") {
                name = Some(meta.value()?.parse::<syn::LitStr>()?.value());
                Ok(())
            } else {
                Err(meta.error("unsupported attribute"))
            }
        });
        parse_macro_input!(attrs with attr_parser);
    }
    match init::expand(name, parse_macro_input!(item)) {
        Ok(tokens) => tokens,
        Err(e) => e.into_compile_error(),
    }
    .into()
}

/// Allow a Rust type to be passed to Ruby, automatically wrapped as a Ruby
/// object.
///
/// For more control over the wrapped object, see [`TypedData`].
///
/// # Attributes
///
/// * `class = "..."` - required, sets the Ruby class to wrap the Rust type.
///   Supports module paths, e.g. `Foo::Bar::Baz`.
/// * `name = "..."` - debug name for the type, must be unique. Defaults to the
///   class name.
/// * `free_immediately` - Drop the Rust type as soon as the Ruby object has
///   been garbage collected. This is only safe to set if the type's [`Drop`]
///   implmentation does not call Ruby.
/// * `size` - Report the [`std::mem::size_of_val`] of the type to Ruby, used
///   to aid in deciding when to run the garbage collector.
/// * `unsafe_generics` - The derived implementation of [`TypedData`] is not
///   guaranteed to be correct for types with generics. If you are sure it is
///   for your type this attribute can be used to override the compile time
///   error usually generated for types with generics.
///
/// # Variant Attributes
///
/// The `#[magnus(...)]` attribute can be set on enum variants with the
/// following values:
///
/// * `class = "..."` - sets the Ruby class to wrap the variant. Supports
///   module paths, e.g. `Foo::Bar::Baz`.
///
/// # Examples
///
/// ```
/// #[magnus::wrap(class = "RbPoint", free_immediately, size)]
/// struct Point {
///     x: isize,
///     y: isize,
/// }
///
/// // the `Point` struct is automatically wrapped in a Ruby `RbPoint` object
/// // when returned to Ruby.
/// fn point(x: isize, y: isize) -> Point {
///     Point { x, y }
/// }
///
/// // Ruby `RbPoint` objects are automatically unwrapped to references to the
/// // `Point` structs they are wrapping when this function is called from Ruby.
/// fn distance(a: &Point, b: &Point) -> f64 {
///     (((b.x - a.x).pow(2) + (b.y - a.y).pow(2)) as f64).sqrt()
/// }
///
/// #[magnus::init]
/// fn init() {
///     magnus::define_global_function("point", magnus::function!(point, 2));
///     magnus::define_global_function("distance", magnus::function!(distance, 2));
/// }
/// ```
///
/// With subclasses for enum variants:
///
/// ```
/// use std::f64::consts::PI;
///
/// use magnus::{class, define_class, function, method, prelude::*};
///
/// #[magnus::wrap(class = "Shape")]
/// enum Shape {
///     #[magnus(class = "Circle")]
///     Circle { r: f64 },
///     #[magnus(class = "Rectangle")]
///     Rectangle { x: f64, y: f64 },
/// }
///
/// impl Shape {
///     fn area(&self) -> f64 {
///         match self {
///             Shape::Circle { r } => PI * r * r,
///             Shape::Rectangle { x, y } => x * y,
///         }
///     }
/// }
///
/// #[magnus::init]
/// fn init() -> Result<(), magnus::Error> {
///     let shape = define_class("Shape", class::object())?;
///     shape.define_method("area", method!(Shape::area, 0))?;
///
///     let circle = define_class("Circle", shape)?;
///     circle.define_singleton_method("new", function!(|r| Shape::Circle { r }, 1))?;
///
///     let rectangle = define_class("Rectangle", shape)?;
///     rectangle.define_singleton_method("new", function!(|x, y| Shape::Rectangle { x, y }, 2))?;
///
///     Ok(())
/// }
/// ```
#[proc_macro_attribute]
pub fn wrap(attrs: TokenStream, item: TokenStream) -> TokenStream {
    typed_data::expand(parse_macro_input!(attrs), parse_macro_input!(item)).into()
}

/// Derives `DataTypeFunctions` with default implementations, for simple uses
/// of [`TypedData`].
///
/// For cases where no custom `DataTypeFunctions` are required a default
/// implementation can be derived. The [`macro@wrap`] macro may be a simpler
/// alternative in this use case.
#[proc_macro_derive(DataTypeFunctions)]
pub fn derive_data_type_functions(input: TokenStream) -> TokenStream {
    typed_data::expand_derive_data_type_functions(parse_macro_input!(input)).into()
}

/// Derives `TypedData`, allowing the type to be passed to Ruby automatically
/// wrapped as a Ruby object.
///
/// For simple cases, see [`macro@wrap`].
///
/// # Attributes
///
/// The `#[magnus(...)]` attribute can be set with the following values:
///
/// * `class = "..."` - required, sets the Ruby class to wrap the Rust type.
///   Supports module paths, e.g. `Foo::Bar::Baz`.
/// * `name = "..."` - debug name for the type, must be unique. Defaults to the
///   class name.
/// * `free_immediately` - Drop the Rust type as soon as the Ruby object has
///   been garbage collected. This is only safe to set if the type's [`Drop`]
///   and `DataTypeFunctions::free` implementations do not call Ruby.
/// * `mark` - Enable Ruby calling the `DataTypeFunctions::mark` function.
/// * `size` - Enable Ruby calling the `DataTypeFunctions::size` function.
/// * `compact` - Enable Ruby calling the `DataTypeFunctions::compact` function.
/// * `wb_protected` - Enable the `wb_protected` flag.
/// * `frozen_shareable` - Enable the `frozen_shareable` flag.
/// * `unsafe_generics` - The derived implementation of [`TypedData`] is not
///   guaranteed to be correct for types with generics. If you are sure it is
///   for your type this attribute can be used to override the compile time
///   error usually generated for types with generics.
///
/// # Field Attributes
///
/// The `#[magnus(...)]` attribute can be set on struct fields with the
/// following values:
///
/// * `opaque_attr_reader` - For a Ruby value wrapped in `Opaque`, creates a
///   accessor method that returns the unwrapped Ruby value.
///
/// # Variant Attributes
///
/// The `#[magnus(...)]` attribute can be set on enum variants with the
/// following values:
///
/// * `class = "..."` - sets the Ruby class to wrap the variant. Supports
///   module paths, e.g. `Foo::Bar::Baz`.
///
/// # Examples
///
/// ```
/// use magnus::{DataTypeFunctions, TypedData};
///
/// #[derive(DataTypeFunctions, TypedData)]
/// #[magnus(class = "RbPoint", size, free_immediately)]
/// struct Point {
///     x: isize,
///     y: isize,
/// }
///
/// // the `Point` struct is automatically wrapped in a Ruby `RbPoint` object
/// // when returned to Ruby.
/// fn point(x: isize, y: isize) -> Point {
///     Point { x, y }
/// }
///
/// // Ruby `RbPoint` objects are automatically unwrapped to references to the
/// // `Point` structs they are wrapping when this function is called from Ruby.
/// fn distance(a: &Point, b: &Point) -> f64 {
///     (((b.x - a.x).pow(2) + (b.y - a.y).pow(2)) as f64).sqrt()
/// }
///
/// #[magnus::init]
/// fn init() {
///     magnus::define_global_function("point", magnus::function!(point, 2));
///     magnus::define_global_function("distance", magnus::function!(distance, 2));
/// }
/// ```
///
/// With subclasses for enum variants:
///
/// ```
/// use magnus::{class, define_class};
///
/// #[magnus::wrap(class = "Shape")]
/// enum Shape {
///     #[magnus(class = "Circle")]
///     Circle { r: f64 },
///     #[magnus(class = "Rectangle")]
///     Rectangle { x: f64, y: f64 },
/// }
///
/// #[magnus::init]
/// fn init() -> Result<(), magnus::Error> {
///     let shape = define_class("Shape", class::object())?;
///     define_class("Circle", shape)?;
///     define_class("Rectangle", shape)?;
///     Ok(())
/// }
/// ```
///
/// Defining a custom `DataType` function:
///
/// ```
/// use std::mem::size_of_val;
///
/// use magnus::{DataTypeFunctions, TypedData};
///
/// #[derive(TypedData)]
/// #[magnus(class = "Name", size, free_immediately)]
/// struct Name {
///     first: String,
///     last: String,
/// }
///
/// impl DataTypeFunctions for Name {
///     fn size(&self) -> usize {
///         size_of_val(&self.first) + size_of_val(&self.last)
///     }
/// }
/// ```
///
/// A struct containing Ruby values.
///
/// ```
/// use magnus::{
///     class, define_class, function, gc, method, prelude::*, typed_data::Obj, value::Opaque,
///     DataTypeFunctions, TypedData,
/// };
///
/// # #[magnus::wrap(class = "Point", free_immediately, size)]
/// # struct Point {
/// #     x: isize,
/// #     y: isize,
/// # }
/// #
/// #[derive(TypedData)]
/// #[magnus(class = "Line", free_immediately, mark)]
/// struct Line {
///     #[magnus(opaque_attr_reader)]
///     start: Opaque<Obj<Point>>,
///     #[magnus(opaque_attr_reader)]
///     end: Opaque<Obj<Point>>,
/// }
///
/// impl Line {
///     fn new(start: Obj<Point>, end: Obj<Point>) -> Self {
///         Self {
///             start: start.into(),
///             end: end.into(),
///         }
///     }
///
///     fn length(&self) -> f64 {
///         let start = self.start();
///         let end = self.end();
///
///         (((end.x - start.x).pow(2) + (end.y - start.y).pow(2)) as f64).sqrt()
///     }
/// }
///
/// impl DataTypeFunctions for Line {
///     fn mark(&self) {
///         gc::mark(self.start());
///         gc::mark(self.end());
///     }
/// }
///
/// #[magnus::init]
/// fn init() -> Result<(), magnus::Error> {
///     let line = define_class("Line", class::object())?;
///     line.define_singleton_method("new", function!(Line::new, 2))?;
///     line.define_method("length", method!(Line::length, 0))?;
///     Ok(())
/// }
/// ```
#[proc_macro_derive(TypedData, attributes(magnus))]
pub fn derive_typed_data(input: TokenStream) -> TokenStream {
    match typed_data::expand_derive_typed_data(parse_macro_input!(input)) {
        Ok(tokens) => tokens,
        Err(e) => e.into_compile_error(),
    }
    .into()
}
