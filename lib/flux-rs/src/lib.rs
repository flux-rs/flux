// When running without flux, all macros are pass-through
use proc_macro::TokenStream;

#[cfg(not(flux_sysroot))]
#[proc_macro_attribute]
pub fn extern_spec(_attrs: TokenStream, _tokens: TokenStream) -> TokenStream {
    TokenStream::new()
}

#[cfg(flux_sysroot)]
#[proc_macro_attribute]
pub fn extern_spec(attrs: TokenStream, tokens: TokenStream) -> TokenStream {
    flux_attrs::extern_spec(attrs.into(), tokens.into()).into()
}

#[proc_macro]
pub fn flux(tokens: TokenStream) -> TokenStream {
    flux_attrs::flux(tokens.into()).into()
}
