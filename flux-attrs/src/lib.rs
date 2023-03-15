#![feature(proc_macro_diagnostic)]

use proc_macro2::TokenStream;
use quote::{format_ident, quote_spanned};
use syn::{
    parse_quote_spanned, punctuated::Punctuated, spanned::Spanned, Expr, FnArg, GenericArgument,
    GenericParam, Token,
};

pub fn extern_spec(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    transform_extern_spec(attr, tokens).unwrap_or_else(|err| err.to_compile_error())
}

fn transform_extern_spec(attr: TokenStream, tokens: TokenStream) -> syn::Result<TokenStream> {
    let mod_path: Option<syn::Path> =
        if !attr.is_empty() { Some(syn::parse2(attr)?) } else { None };
    let (sig, attrs) = extract_sig_from_stub(tokens)?;
    create_dummy_fn(mod_path, sig, attrs)
}

/// Takes a function stub, i.e. something that looks like
/// ```ignore
///     pub fn swap(a: &mut i32, b: &mut i32) -> ();
/// ```
/// and extracts its signature and any attributes.
///
/// This function actually tries to parse the stub as a `syn::TraitItemMethod`
/// and requires that it not have a default implementation.
fn extract_sig_from_stub(
    tokens: TokenStream,
) -> syn::Result<(syn::Signature, Vec<syn::Attribute>)> {
    let span = tokens.span();
    match syn::parse2::<syn::TraitItemMethod>(tokens) {
        // Parse must succeed and it must not have a default implementation (i.e. it must end with a ';')
        Err(_) | Ok(syn::TraitItemMethod { default: Some(_), .. }) => Err(syn::Error::new(
            span,
            "Invalid function stub: extern specs expect a function stub like: fn swap(a: &mut i32, b: &mut i32);"
        )),
        Ok(trait_item_method) => {
            Ok((trait_item_method.sig, trait_item_method.attrs))
        }
    }
}

/// Creates a dummy function whose inner body is just a pass-through call to the
/// extern function. Takes the signature and attributes
/// ```ignore
/// swap(a: &mut i32, b: &mut i32) -> ()
/// ```
/// and produces a function that looks like.
/// ```ignore
///     pub fn flux_extern_spec_swap(a: &mut i32, b: &mut i32) -> () {
///         swap(a,b)
///     }
/// ```
///
/// The big idea:
/// 1. Mangle the name of the function into flux_extern_spec_{fn_ident} so that it doesn't
///    conflict with an existing function. TODO: add some random number to ensure it.
/// 2. Create a new function with the mangled name and same signature.
/// 3. Replace its body with a single expression that is a function call.
/// 4. The function call is of the form mod_path::fn_ident<generic_args>(params)
///    where the generic args and params have been modified so that they function as
///    arguments to the call instead of being a part of the function signature.
/// 5. Finally, we suppress dead_code/unused warnings and add the flux::extern_spec
///    so that flux knows this is the generated dummy function for the external function
///    that is being called.
fn create_dummy_fn(
    mod_path: Option<syn::Path>,
    sig: syn::Signature,
    attrs: Vec<syn::Attribute>,
) -> syn::Result<TokenStream> {
    let span = sig.span();
    let mut mangled_sig = sig.clone();
    let ident = sig.ident;
    mangled_sig.ident = format_ident!("flux_extern_spec_{}", ident);
    let generic_call_args = transform_generic_params_to_call_args(sig.generics.params);
    let call_args = transform_params_to_call_args(sig.inputs);
    let fn_path: syn::Path = if let Some(mod_path) = mod_path {
        parse_quote_spanned!( ident.span() => #mod_path :: #ident)
    } else {
        parse_quote_spanned!( ident.span() => #ident )
    };
    Ok(quote_spanned! { span =>
                        #[flux::extern_spec]
                        #(#attrs)*
                        #[allow(unused, dead_code)]
                        #mangled_sig {
                            #fn_path :: < #generic_call_args > ( #call_args )
                        }
    })
}

// Cribbed from Prusti's extern_spec_rewriter
fn transform_generic_params_to_call_args(
    generic_params: Punctuated<GenericParam, Token!(,)>,
) -> Punctuated<GenericArgument, Token!(,)> {
    Punctuated::from_iter(
        generic_params
            .iter()
            .flat_map(|param| -> Option<GenericArgument> {
                let span = param.span();
                match param {
                    GenericParam::Type(syn::TypeParam { ident, .. }) => {
                        Some(parse_quote_spanned! { span => #ident })
                    }
                    GenericParam::Lifetime(_) => None,
                    GenericParam::Const(syn::ConstParam { ident, .. }) => {
                        Some(parse_quote_spanned! {span => #ident })
                    }
                }
            }),
    )
}

// Cribbed from Prusti's extern_spec_rewriter
fn transform_params_to_call_args(
    params: Punctuated<FnArg, Token!(,)>,
) -> Punctuated<Expr, Token!(,)> {
    Punctuated::from_iter(params.iter().map(|param| -> Expr {
        let span = param.span();
        match param {
            FnArg::Typed(pat_type) => {
                match pat_type.pat.as_ref() {
                    syn::Pat::Ident(ident) => {
                        parse_quote_spanned! {span => #ident }
                    }
                    _ => {
                        unimplemented!(
                            "extern specs don't support patterns other than simple identifiers"
                        )
                    }
                }
            }
            FnArg::Receiver(_) => parse_quote_spanned! {span => self},
        }
    }))
}
