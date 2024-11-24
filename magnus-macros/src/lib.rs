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
//! fn init(ruby: &Ruby) -> Result<(), magnus::Error> {
//!     ruby.define_class("RbPoint", magnus::class::object())?;
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

/// Allows a Rust type to be passed to Ruby, where it is automatically wrapped
/// as a Ruby object.
///
/// For more control over the wrapping behavior, see [`TypedData`].
///
/// # Attributes
///
/// The `#[wrap]` macro supports several attributes to configure its behavior:
///
/// * `class = "..."` (required):  
///   Specifies the Ruby class associated with the Rust type. The class name can include
///   module paths, such as `Foo::Bar::Baz`, which are used to define the hierarchy
///   of the Ruby class.
///   
/// * `name = "..."`:  
///   Specifies a debug name for the type. This name must be unique and defaults to the
///   class name if not explicitly provided.
///
/// * `free_immediately`:  
///   Indicates that the Rust type should be dropped as soon as the Ruby object is garbage
///   collected. This is only safe if the type's [`Drop`] implementation does not call Ruby,
///   as calling Ruby during the garbage collection process is unsafe and can lead to
///   undefined behavior.
///
/// * `size`:  
///   Reports the [`std::mem::size_of_val`] of the type to Ruby, helping Ruby's garbage
///   collector determine when to run.
///
/// * `unsafe_generics`:  
///   Disables compile-time checks for types with generics, allowing their use with
///   `#[wrap]`. This should only be used if you are confident that the derived
///   implementation of [`TypedData`] is correct for your generic type.
///
/// # Variant Attributes
///
/// When wrapping enums, the `#[magnus(...)]` attribute can also be applied to individual
/// variants to define specific behavior for them:
///
/// * `class = "..."`:  
///   Specifies the Ruby class associated with a particular variant. This is useful
///   for defining subclasses for the variants.
///
/// ## Wrapping a Struct
///
/// ```
/// use magnus::{function, prelude::*, wrap};
///
/// #[wrap(class = "Point", free_immediately, size)]
/// struct Point {
///     x: isize,
///     y: isize,
/// }
///
/// fn point(x: isize, y: isize) -> Point {
///     Point { x, y }
/// }
///
/// fn distance(a: &Point, b: &Point) -> f64 {
///     (((b.x - a.x).pow(2) + (b.y - a.y).pow(2)) as f64).sqrt()
/// }
///
/// #[magnus::init]
/// fn init() {
///     magnus::define_global_function("point", function!(point, 2));
///     magnus::define_global_function("distance", function!(distance, 2));
/// }
/// ```
///
/// Read the complete example [here](https://github.com/matsadler/magnus/blob/main/examples/point.rs).
///
/// ## Handling Mutability
///
/// ```
/// use magnus::{wrap, prelude::*};
/// use std::cell::RefCell;
///
/// struct Point {
///     x: isize,
///     y: isize,
/// }
///
/// #[wrap(class = "Point")]
/// struct MutPoint(RefCell<Point>);
///
/// impl MutPoint {
///     fn set_x(&self, i: isize) {
///         self.0.borrow_mut().x = i;
///     }
/// }
/// ```
///
/// Read the complete example [here](https://github.com/matsadler/magnus/blob/main/examples/mut_point.rs).
///
/// ## Supporting Subclassing
///
/// ```
/// use magnus::{function, method, prelude::*, wrap, Ruby, Error};
/// use std::cell::RefCell;
///
/// #[derive(Default)]
/// struct Point {
///     x: isize,
///     y: isize,
/// }
///
/// #[derive(Default)]
/// #[wrap(class = "Point")]
/// struct MutPoint(RefCell<Point>);
///
/// impl MutPoint {
///     fn initialize(&self, x: isize, y: isize) {
///         let mut this = self.0.borrow_mut();
///         this.x = x;
///         this.y = y;
///     }
/// }
///
/// #[magnus::init]
/// fn init(ruby: &Ruby) -> Result<(), Error> {
///     let class = ruby.define_class("Point", ruby.class_object()).unwrap();
///     class.define_alloc_func::<MutPoint>();
///     class.define_method("initialize", method!(MutPoint::initialize, 2))?;
///     Ok(())
/// }
/// ```
///
/// ## Error Handling
///
/// ```
/// use magnus::{wrap, prelude::*, Ruby, Error};
/// use std::cell::RefCell;
///
/// struct Point {
///     x: isize,
///     y: isize,
/// }
///
/// #[wrap(class = "Point")]
/// struct MutPoint(RefCell<Point>);
///
/// impl MutPoint {
///     fn set_x(ruby: &Ruby, rb_self: &Self, i: i32) -> Result<(), Error> {
///         if i <= 0 {
///             return Err(Error::new(ruby.exception_arg_error(), "x must be positive"));
///         }
///         rb_self.0.borrow_mut().x = i as isize;
///         Ok(())
///     }
/// }
/// ```
///
/// ## Wrapping an Enum with Subclasses
///
/// ```
/// use magnus::{class, define_class, function, method, prelude::*, wrap};
/// use std::f64::consts::PI;
///
/// #[wrap(class = "Shape")]
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

/// Derives `TypedData`, allowing a Rust type to be passed to Ruby and automatically
/// wrapped as a Ruby object.
///
/// For simpler use cases, consider using [`macro@wrap`].
///
/// # Attributes
///
/// The `#[magnus(...)]` attribute supports the following values to configure its behavior:
///
/// * `class = "..."` (required):  
///   Specifies the Ruby class associated with the Rust type. Supports module paths,
///   such as `Foo::Bar::Baz`.
///
/// * `name = "..."`:  
///   Specifies a debug name for the type. This name must be unique and defaults to the
///   class name if not explicitly provided.
///
/// * `free_immediately`:  
///   Indicates that the Rust type should be dropped as soon as the Ruby object is garbage
///   collected. This is only safe if the type's [`Drop`] and `DataTypeFunctions::free`
///   implementations do not call Ruby.
///
/// * `mark`:  
///   Enables Ruby to call the `DataTypeFunctions::mark` function.
///
/// * `size`:  
///   Enables Ruby to call the `DataTypeFunctions::size` function.
///
/// * `compact`:  
///   Enables Ruby to call the `DataTypeFunctions::compact` function.
///
/// * `wb_protected`:  
///   Sets the `wb_protected` flag for write-barrier-protected objects.
///
/// * `frozen_shareable`:  
///   Sets the `frozen_shareable` flag for objects shareable across frozen Ruby objects.
///
/// * `unsafe_generics`:  
///   Disables compile-time checks for types with generics, allowing their use with
///   `#[magnus(...)]`. Use this only if you are confident the derived implementation
///   is correct for your generic type.
///
/// # Field Attributes
///
/// The `#[magnus(...)]` attribute can be set on struct fields with the following values:
///
/// * `opaque_attr_reader`:  
///   For a Ruby value wrapped in `Opaque`, creates an accessor method that returns
///   the unwrapped Ruby value.
///
/// # Variant Attributes
///
/// The `#[magnus(...)]` attribute can be set on enum variants with the following values:
///
/// * `class = "..."`:  
///   Specifies the Ruby class associated with the variant. Supports module paths,
///   such as `Foo::Bar::Baz`.
///
/// ## Wrapping a Struct
///
/// ```
/// use magnus::{TypedData, DataTypeFunctions, function, prelude::*, Ruby};
///
/// #[derive(DataTypeFunctions, TypedData)]
/// #[magnus(class = "Point", size, free_immediately)]
/// struct Point {
///     x: isize,
///     y: isize,
/// }
///
/// // wraps `Point` struct in a Ruby `Point` object when returned to Ruby.
/// fn point(x: isize, y: isize) -> Point {
///     Point { x, y }
/// }
///
/// // automatically unwraps `Point` objects to references to `Point`` structs
/// // when invoking the function.
/// fn distance(a: &Point, b: &Point) -> f64 {
///     (((b.x - a.x).pow(2) + (b.y - a.y).pow(2)) as f64).sqrt()
/// }
///
/// #[magnus::init]
/// fn init(ruby: &Ruby) {
///     ruby.define_global_function("point", function!(point, 2));
///     ruby.define_global_function("distance", function!(distance, 2));
/// }
/// ```
///
/// ## Wrapping an Enum with Subclasses
///
/// ```
/// use magnus::{class, prelude::*, wrap, Ruby, Error};
///
/// #[wrap(class = "Shape")]
/// enum Shape {
///     #[magnus(class = "Circle")]
///     Circle { r: f64 },
///     #[magnus(class = "Rectangle")]
///     Rectangle { x: f64, y: f64 },
/// }
///
/// #[magnus::init]
/// fn init(ruby: &Ruby) -> Result<(), Error> {
///     let shape = ruby.define_class("Shape", ruby.class_object())?;
///     ruby.define_class("Circle", shape)?;
///     ruby.define_class("Rectangle", shape)?;
///     Ok(())
/// }
/// ```
///
/// ## Custom `DataTypeFunctions` Implementation
///
/// ```
/// use std::mem::size_of_val;
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
/// ## Struct Containing Ruby Values
///
/// ```
/// use magnus::{
///     class, function, gc, method, prelude::*, typed_data::Obj, value::Opaque,
///     DataTypeFunctions, TypedData, Ruby
/// };
///
/// #[derive(DataTypeFunctions, TypedData)]
/// #[magnus(class = "Point", size, free_immediately)]
/// struct Point {
///     x: isize,
///     y: isize,
/// }
///
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
///     fn mark(&self, marker: &gc::Marker) {
///         marker.mark(self.start);
///         marker.mark(self.end);
///     }
/// }
///
/// #[magnus::init]
/// fn init(ruby: &Ruby) -> Result<(), magnus::Error> {
///     let line = ruby.define_class("Line", ruby.class_object())?;
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
