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

/// Derives `DataTypeFunctions`, allowing the type to implement `TypedData`.
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
