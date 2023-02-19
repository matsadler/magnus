use proc_macro2::TokenStream;
use quote::{quote, ToTokens};
use syn::{spanned::Spanned, Data, DataEnum, DataStruct, DeriveInput, Error, Fields, FieldsNamed};

use crate::util;

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

pub fn expand_derive_typed_data(input: DeriveInput) -> TokenStream {
    if !input.generics.to_token_stream().is_empty() {
        return Error::new(
            input.generics.span(),
            "TypedData can't be derived for generic types",
        )
        .into_compile_error();
    }
    let attrs = match util::to_attribute_args(&input.attrs) {
        Ok(Some(v)) => v,
        Ok(None) => {
            return Error::new(input.span(), "missing #[magnus] attribute").into_compile_error()
        }
        Err(e) => return e.into_compile_error(),
    };
    let mut args = match util::Args::new_with_aliases(
        attrs,
        &[
            "class",
            "name",
            "mark",
            "size",
            "compact",
            "free_immediately",
            "wb_protected",
            "frozen_shareable",
        ],
        &vec![("free_immediatly", "free_immediately")]
            .into_iter()
            .collect(),
    ) {
        Ok(v) => v,
        Err(e) => return e.into_compile_error(),
    };

    let class = match args.extract::<String>("class") {
        Ok(v) => v,
        Err(e) => return e.into_compile_error(),
    };
    let name = match args.extract::<Option<String>>("name") {
        Ok(v) => v.unwrap_or_else(|| class.clone()),
        Err(e) => return e.into_compile_error(),
    };
    let mark = match args.extract::<Option<()>>("mark") {
        Ok(v) => v.is_some(),
        Err(e) => return e.into_compile_error(),
    };
    let size = match args.extract::<Option<()>>("size") {
        Ok(v) => v.is_some(),
        Err(e) => return e.into_compile_error(),
    };
    let compact = match args.extract::<Option<()>>("compact") {
        Ok(v) => v.is_some(),
        Err(e) => return e.into_compile_error(),
    };
    let free_immediately = match args.extract::<Option<()>>("free_immediately") {
        Ok(v) => v.is_some(),
        Err(e) => return e.into_compile_error(),
    };
    let wb_protected = match args.extract::<Option<()>>("wb_protected") {
        Ok(v) => v.is_some(),
        Err(e) => return e.into_compile_error(),
    };
    let frozen_shareable = match args.extract::<Option<()>>("frozen_shareable") {
        Ok(v) => v.is_some(),
        Err(e) => return e.into_compile_error(),
    };

    let ident = &input.ident;

    let mut arms = Vec::new();
    if let Data::Enum(DataEnum { ref variants, .. }) = input.data {
        for variant in variants.into_iter() {
            let attrs = match util::to_attribute_args(&variant.attrs) {
                Ok(Some(v)) => v,
                Ok(None) => continue,
                Err(e) => return e.into_compile_error(),
            };
            let mut args = match util::Args::new(attrs, &["class"]) {
                Ok(v) => v,
                Err(e) => return e.into_compile_error(),
            };
            let class = match args.extract::<String>("class") {
                Ok(v) => v,
                Err(e) => return e.into_compile_error(),
            };
            let ident = &variant.ident;
            let fetch_class = quote! {
                *magnus::memoize!(RClass: {
                    let class: RClass = class::object().funcall("const_get", (#class,)).unwrap();
                    class.undef_alloc_func();
                    class
                })
            };
            arms.push(match variant.fields {
                Fields::Named(_) => quote! { Self::#ident { .. } => #fetch_class },
                Fields::Unnamed(_) => quote! { Self::#ident(_) => #fetch_class },
                Fields::Unit => quote! { Self::#ident => #fetch_class },
            });
        }
    }
    let class_for = if !arms.is_empty() {
        quote! {
            fn class_for(value: &Self) -> magnus::RClass {
                use magnus::{class, Module, Class, RClass};
                #[allow(unreachable_patterns)]
                match value {
                    #(#arms,)*
                    _ => Self::class(),
                }
            }
        }
    } else {
        quote! {}
    };

    let mut accessors = Vec::new();
    if let Data::Struct(DataStruct {
        fields: Fields::Named(FieldsNamed { ref named, .. }),
        ..
    }) = input.data
    {
        for field in named {
            let attrs = match util::to_attribute_args(&field.attrs) {
                Ok(Some(v)) => v,
                Ok(None) => continue,
                Err(e) => return e.into_compile_error(),
            };
            let mut args = match util::Args::new(attrs, &["opaque_attr_reader"]) {
                Ok(v) => v,
                Err(e) => return e.into_compile_error(),
            };
            let mut read = false;
            match args.extract::<Option<()>>("opaque_attr_reader") {
                Ok(Some(())) => read = true,
                Ok(None) => {}
                Err(e) => return e.into_compile_error(),
            };
            let ident = field.ident.as_ref().unwrap();
            let ty = &field.ty;
            if read {
                accessors.push(quote! {
                    fn #ident(&self) -> <#ty as magnus::value::OpaqueVal>::Val {
                        let handle = unsafe { RubyHandle::get_unchecked() };
                        handle.unwrap_opaque(self.#ident)
                    }
                });
            }
        }
    }

    let accessor_impl = if !accessors.is_empty() {
        quote! {
            impl #ident {
                #(#accessors)*
            }
        }
    } else {
        quote! {}
    };

    let mut builder = Vec::new();
    builder.push(quote! { let mut builder = magnus::DataType::builder::<Self>(#name); });
    if mark {
        builder.push(quote! { builder.mark(); });
    }
    if size {
        builder.push(quote! { builder.size(); });
    }
    if compact {
        builder.push(quote! { builder.compact(); });
    }
    if free_immediately {
        builder.push(quote! { builder.free_immediately(); });
    }
    if wb_protected {
        builder.push(quote! { builder.wb_protected(); });
    }
    if frozen_shareable {
        builder.push(quote! { builder.frozen_shareable(); });
    }
    builder.push(quote! { builder.build() });
    let builder = builder.into_iter().collect::<TokenStream>();
    let tokens = quote! {
        #accessor_impl

        unsafe impl magnus::TypedData for #ident {
            fn class() -> magnus::RClass {
                use magnus::{class, Module, Class, RClass, value::ReprValue};
                *magnus::memoize!(RClass: {
                    let class: RClass = class::object().funcall("const_get", (#class,)).unwrap();
                    class.undef_alloc_func();
                    class
                })
            }

            fn data_type() -> &'static magnus::DataType {
                magnus::memoize!(magnus::DataType: {
                    #builder
                })
            }

            #class_for
        }
    };
    tokens
}
