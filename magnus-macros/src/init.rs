use proc_macro2::{Ident, Span, TokenStream};
use quote::quote;
use syn::{AttributeArgs, Error, ItemFn, Lit, Meta, MetaNameValue, NestedMeta};

pub fn expand(args: AttributeArgs, input: ItemFn) -> TokenStream {
    let crate_name = {
        let mut crate_name = None;

        for attr in args {
            if let NestedMeta::Meta(Meta::NameValue(MetaNameValue {
                path,
                eq_token: _,
                lit,
            })) = attr
            {
                if path.is_ident("name") {
                    if crate_name.is_some() {
                        return Error::new_spanned(path, "duplicate field").into_compile_error();
                    } else if let Lit::Str(lit_str) = lit {
                        crate_name = Some(lit_str.value());
                    } else {
                        return Error::new_spanned(lit, "expected string").into_compile_error();
                    }
                } else {
                    return Error::new_spanned(path, "unknown field").into_compile_error();
                }
            } else {
                return Error::new_spanned(attr, "unknown field").into_compile_error();
            }
        }

        match crate_name.or_else(|| std::env::var("CARGO_PKG_NAME").ok()) {
            Some(v) => v,
            None => {
                return Error::new(Span::call_site(), r#"missing (name = "...") attribute"#)
                    .into_compile_error()
            }
        }
    };

    let extern_init_name = Ident::new(
        &format!("Init_{}", crate_name.replace('-', "_")),
        Span::call_site(),
    );
    let init_name = input.sig.ident.clone();

    quote! {
        #input

        #[allow(non_snake_case)]
        #[no_mangle]
        pub extern "C" fn #extern_init_name() {
            unsafe { magnus::method::Init::new(#init_name).call_handle_error() }
        }
    }
}
