// When running without flux, all macros are pass-through
#![cfg_attr(not(feature = "enabled"), no_std)]
use proc_macro::TokenStream;

#[cfg(not(feature = "enabled"))]
#[proc_macro_attribute]
pub fn extern_spec(_: TokenStream, tokens: TokenStream) -> TokenStream {
    tokens
}

#[cfg(feature = "enabled")]
#[proc_macro_attribute]
pub fn extern_spec(attrs: TokenStream, tokens: TokenStream) -> TokenStream {
    flux_attrs::extern_spec(attrs.into(), tokens.into()).into()
}
