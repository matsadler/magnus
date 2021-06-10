use proc_macro::TokenStream;
use proc_macro2::{Ident, Span};
use quote::quote;
use syn::{parse_macro_input, ItemFn};

#[proc_macro_attribute]
pub fn init(_: TokenStream, item: TokenStream) -> TokenStream {
    let init = parse_macro_input!(item as ItemFn);
    let init_name = init.sig.ident.clone();

    let crate_name = std::env::var("CARGO_PKG_NAME").unwrap();
    let extern_init_name = Ident::new(&format!("Init_{}", crate_name), Span::call_site());

    let tokens = quote! {
        #init

        #[allow(non_snake_case)]
        #[no_mangle]
        pub extern "C" fn #extern_init_name() {
            unsafe { magnus::method::Init::new(#init_name).call_handle_error() }
        }
    };
    TokenStream::from(tokens)
}
