use darling::{util::Flag, FromMeta};
use proc_macro2::TokenStream;
use quote::{quote, ToTokens};
use syn::{spanned::Spanned, DeriveInput, Error};

pub fn expand(attrs: TokenStream, item: TokenStream) -> TokenStream {
    quote! {
        #[derive(magnus::DataTypeFunctions, magnus::TypedData)]
        #[magnus(#attrs)]
        #item
    }
}

pub fn expand_derive_data_type_functions(input: DeriveInput) -> TokenStream {
    let ident = input.ident;
    let generics = input.generics;
    quote! {
        impl #generics magnus::DataTypeFunctions for #ident #generics {}
    }
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

pub fn expand_derive_typed_data(input: DeriveInput) -> TokenStream {
    if !input.generics.to_token_stream().is_empty() {
        return Error::new(
            input.generics.span(),
            "TypedData can't be derived for generic types",
        )
        .into_compile_error();
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
            .into_compile_error();
    }
    if attrs.is_empty() {
        return Error::new(input.span(), "missing #[magnus] attribute").into_compile_error();
    }
    let attrs = match attrs.remove(0).parse_meta() {
        Ok(v) => v,
        Err(e) => return e.into_compile_error(),
    };
    let attrs = match TypedDataAttributes::from_meta(&attrs) {
        Ok(v) => v,
        Err(e) => return e.write_errors(),
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
    let builder = builder.into_iter().collect::<TokenStream>();
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
    tokens
}
