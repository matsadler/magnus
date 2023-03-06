use proc_macro2::{Ident, Span, TokenStream};
use quote::quote;
use syn::{AttributeArgs, Error, ItemFn};

use crate::util;

pub fn expand(args: AttributeArgs, input: ItemFn) -> TokenStream {
    let mut args = match util::Args::new(args, &["name"]) {
        Ok(v) => v,
        Err(e) => return e.into_compile_error(),
    };
    let crate_name: String = match args.extract("name") {
        Ok(Some(v)) => v,
        Ok(None) => match std::env::var("CARGO_PKG_NAME") {
            Ok(v) => v,
            Err(_) => {
                return Error::new(Span::call_site(), r#"missing (name = "...") attribute"#)
                    .into_compile_error()
            }
        },
        Err(e) => return e.into_compile_error(),
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
        pub unsafe extern "C" fn #extern_init_name() {
            use magnus::method::{Init, RubyInit};
            #init_name.call_handle_error()
        }
    }
}
