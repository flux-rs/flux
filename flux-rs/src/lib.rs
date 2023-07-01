// When running without flux, all macros are pass-through
#![cfg_attr(not(feature = "enabled"), no_std)]
use proc_macro::TokenStream;

#[cfg(not(feature = "enabled"))]
#[proc_macro_attribute]
pub fn extern_spec(_attrs: TokenStream, _tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(feature = "enabled")]
#[proc_macro_attribute]
pub fn extern_spec(attrs: TokenStream, tokens: TokenStream) -> TokenStream {
    flux_attrs::extern_spec(attrs.into(), tokens.into()).into()
}

#[proc_macro]
pub fn flux(tokens: TokenStream) -> TokenStream {
    flux_attrs::flux(tokens.into()).into()
}
