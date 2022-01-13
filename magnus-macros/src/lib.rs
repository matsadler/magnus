//! Derive and proc macros for magnus.
//!
//! ``` ignore
//! #[magnus::wrap(class = "RbPoint", free_immediatly, size)]
//! struct Point {
//!     x: isize,
//!     y: isize,
//! }
//!
//! #[magnus::init]
//! fn init() -> Result<(), magnus::Error> {
//!     magnus::define_class("RbPoint")?;
//!     Ok(())
//! }
//! ```

#![warn(missing_docs)]

use darling::{util::Flag, FromMeta};
use proc_macro::TokenStream;
use proc_macro2::{Ident, Span};
use quote::{quote, ToTokens};
use syn::{parse_macro_input, spanned::Spanned, AttributeArgs, DeriveInput, Error, ItemFn};

#[derive(FromMeta)]
struct InitAttributes {
    #[darling(default)]
    name: Option<String>,
}

/// Mark a function as the 'init' function to be run for a library when it is
/// `require`d by Ruby code.
///
/// The init function is used to define your Ruby modules & classes, bind
/// functions as Ruby methods, etc.
///
/// # Examples
///
/// ``` ignore
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
/// ``` ignore
/// use magnus::{define_module, function, method, prelude::*, Error};
///
/// #[magnus::wrap(class = "Euclid::Point", free_immediatly, size)]
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
///     let class = module.define_class("Point", Default::default())?;
///     class.define_singleton_method("new", function!(Point::new, 2));
///     class.define_method("x", method!(Point::x, 0));
///     class.define_method("y", method!(Point::y, 0));
///     Ok(())
/// }
/// ```
#[proc_macro_attribute]
pub fn init(attrs: TokenStream, item: TokenStream) -> TokenStream {
    let init = parse_macro_input!(item as ItemFn);
    let init_name = init.sig.ident.clone();

    let attrs2 = attrs.clone();
    let attr_args = parse_macro_input!(attrs2 as AttributeArgs);
    let crate_name = match InitAttributes::from_list(&attr_args) {
        Ok(v) => v.name,
        Err(e) => return TokenStream::from(e.write_errors()),
    };
    let crate_name = match crate_name.or_else(|| std::env::var("CARGO_PKG_NAME").ok()) {
        Some(v) => v,
        None => {
            return Error::new(
                proc_macro2::TokenStream::from(attrs).span(),
                "missing #[magnus] attribute",
            )
            .into_compile_error()
            .into()
        }
    };
    let extern_init_name = Ident::new(&format!("Init_{}", crate_name), Span::call_site());

    let tokens = quote! {
        #init

        #[allow(non_snake_case)]
        #[no_mangle]
        pub extern "C" fn #extern_init_name() {
            unsafe { magnus::method::Init::new(#init_name).call_handle_error() }
        }
    };
    tokens.into()
}

/// Allow a Rust type to be passed to Ruby, automatically wrapped as a Ruby
/// object.
///
/// For more control over the wrapped object, see [`TypedData`].
///
/// # Attributes
///
/// * `class = "..."` - required, sets the Ruby class to wrap the Rust type.
///    Supports module paths, e.g. `Foo::Bar::Baz`.
/// * `name = "..."` - debug name for the type, must be unique. Defaults to the
///   class name.
/// * `free_immediatly` - Drop the Rust type as soon as the Ruby object has
///   been garbage collected. This is only safe to set if the type's [`Drop`]
///   implmentation does not call Ruby.
/// * `size` - Report the [`std::mem::size_of_val`] of the type to Ruby, used
///   to aid in deciding when to run the garbage collector.
///
/// # Examples
///
/// ``` ignore
/// #[magnus::wrap(class = "RbPoint", free_immediatly, size)]
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
#[proc_macro_attribute]
pub fn wrap(attrs: TokenStream, item: TokenStream) -> TokenStream {
    let attrs = proc_macro2::TokenStream::from(attrs);
    let item = proc_macro2::TokenStream::from(item);
    let tokens = quote! {
        #[derive(magnus::DataTypeFunctions, magnus::TypedData)]
        #[magnus(#attrs)]
        #item
    };
    tokens.into()
}

/// Derives `DataTypeFunctions` with default implementations, for simple uses
/// of [`TypedData`].
///
/// For cases where no custom `DataTypeFunctions` are required a default
/// implementation can be derived. The [`macro@wrap`] macro may be a simpler
/// alternative in this use case.
#[proc_macro_derive(DataTypeFunctions)]
pub fn derive_data_type_functions(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let ident = input.ident;
    let generics = input.generics;
    let tokens = quote! {
        impl #generics magnus::DataTypeFunctions for #ident #generics {}
    };
    tokens.into()
}

#[derive(FromMeta)]
struct TypedDataAttributes {
    class: String,
    #[darling(default)]
    name: Option<String>,
    #[darling(default)]
    mark: Flag,
    #[darling(default)]
    size: Flag,
    #[darling(default)]
    compact: Flag,
    #[darling(default)]
    free_immediatly: Flag,
    #[darling(default)]
    wb_protected: Flag,
    #[darling(default)]
    frozen_shareable: Flag,
}

/// Derives `TypedData`, allowing the type to be passed to Ruby automatically
/// wrapped as a Ruby object.
///
/// For simple cases, see [`macro@wrap`].
///
/// # Attributes
///
/// The `#[magnus(...)]` attribute can be set with the following values.
///
/// * `class = "..."` - required, sets the Ruby class to wrap the Rust type.
///    Supports module paths, e.g. `Foo::Bar::Baz`.
/// * `name = "..."` - debug name for the type, must be unique. Defaults to the
///   class name.
/// * `free_immediatly` - Drop the Rust type as soon as the Ruby object has
///   been garbage collected. This is only safe to set if the type's [`Drop`]
///   and `DataTypeFunctions::free` implementations do not call Ruby.
/// * `mark` - Enable Ruby calling the `DataTypeFunctions::mark` function.
/// * `size` - Enable Ruby calling the `DataTypeFunctions::size` function.
/// * `compact` - Enable Ruby calling the `DataTypeFunctions::compact` function.
/// * `wb_protected` - Enable the `wb_protected` flag.
/// * `frozen_shareable` - Enable the `frozen_shareable` flag.
///
/// # Examples
///
/// ``` ignore
/// use magnus::{DataTypeFunctions, TypedData};
///
/// #[derive(DataTypeFunctions, TypedData)]
/// #[magnus(class = "RbPoint", size, free_immediatly)]
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
/// Defining a custom `DataType` function.
/// ``` ignore
/// use std::mem::size_of_val;
/// use magnus::{DataTypeFunctions, TypedData};
///
/// #[derive(TypedData)]
/// #[magnus(class = "Name", size, free_immediatly)]
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
#[proc_macro_derive(TypedData, attributes(magnus))]
pub fn derive_typed_data(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    if !input.generics.to_token_stream().is_empty() {
        return Error::new(
            input.generics.span(),
            "TypedData can't be derived for generic types",
        )
        .into_compile_error()
        .into();
    }
    let mut attrs = input
        .attrs
        .clone()
        .into_iter()
        .filter(|attr| attr.path.is_ident("magnus"))
        .collect::<Vec<_>>();
    if attrs.len() > 1 {
        return attrs
            .into_iter()
            .map(|a| Error::new(a.span(), "duplicate attribute"))
            .reduce(|mut a, b| {
                a.combine(b);
                a
            })
            .unwrap()
            .into_compile_error()
            .into();
    }
    if attrs.is_empty() {
        return Error::new(input.span(), "missing #[magnus] attribute")
            .into_compile_error()
            .into();
    }
    let attrs = match attrs.remove(0).parse_meta() {
        Ok(v) => v,
        Err(e) => return e.into_compile_error().into(),
    };
    let attrs = match TypedDataAttributes::from_meta(&attrs) {
        Ok(v) => v,
        Err(e) => return TokenStream::from(e.write_errors()),
    };
    let ident = input.ident;
    let class = attrs.class;
    let name = attrs.name.unwrap_or_else(|| class.clone());
    let mut builder = Vec::new();
    builder.push(quote! { let mut builder = magnus::DataType::builder::<Self>(#name); });
    if attrs.mark.is_some() {
        builder.push(quote! { builder.mark(); });
    }
    if attrs.size.is_some() {
        builder.push(quote! { builder.size(); });
    }
    if attrs.compact.is_some() {
        builder.push(quote! { builder.compact(); });
    }
    if attrs.free_immediatly.is_some() {
        builder.push(quote! { builder.free_immediatly(); });
    }
    if attrs.wb_protected.is_some() {
        builder.push(quote! { builder.wb_protected(); });
    }
    if attrs.frozen_shareable.is_some() {
        builder.push(quote! { builder.frozen_shareable(); });
    }
    builder.push(quote! { builder.build() });
    let builder = builder.into_iter().collect::<proc_macro2::TokenStream>();
    let tokens = quote! {
        unsafe impl magnus::TypedData for #ident {
            fn class() -> magnus::RClass {
                use magnus::Module;
                *magnus::memoize!(magnus::RClass: magnus::RClass::default().funcall("const_get", (#class,)).unwrap())
            }

            fn data_type() -> &'static magnus::DataType {
                magnus::memoize!(magnus::DataType: {
                    #builder
                })
            }
        }
    };
    tokens.into()
}
