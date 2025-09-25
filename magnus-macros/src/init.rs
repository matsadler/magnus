use proc_macro2::{Ident, Span, TokenStream};
use quote::quote;
use syn::{Error, ItemFn};

pub fn expand(name: Option<String>, input: ItemFn) -> Result<TokenStream, Error> {
    let crate_name = match name {
        Some(v) => v,
        None => match std::env::var("CARGO_PKG_NAME") {
            Ok(v) => v,
            Err(_) => {
                return Err(Error::new(
                    Span::call_site(),
                    r#"missing (name = "...") attribute"#,
                ))
            }
        },
    };

    let extern_init_name = Ident::new(
        &format!("Init_{}", crate_name.replace('-', "_")),
        Span::call_site(),
    );
    let init_name = input.sig.ident.clone();

    Ok(quote! {
        #input

        #[allow(non_snake_case)]
        #[no_mangle]
        pub unsafe extern "C" fn #extern_init_name() {
            use magnus::method::{Init, RubyInit};
            #init_name.call_handle_error(&unsafe { magnus::Ruby::get_unchecked() })
        }
    })
}
