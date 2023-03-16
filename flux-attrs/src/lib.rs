#![feature(proc_macro_diagnostic)]

use proc_macro2::{Ident, TokenStream, TokenTree};
use quote::{format_ident, quote_spanned, ToTokens};
use syn::{
    parse::{Parse, ParseStream},
    parse_quote_spanned,
    punctuated::Punctuated,
    spanned::Spanned,
    Expr, FnArg, GenericArgument, GenericParam, Token,
};

/// Attributes on an extern spec.
///
/// Example:
///
/// ```ignore
/// #[extern_spec(mod_path = std::vec, generics = <T>)]
/// struct Vec<T>;
/// ```
#[derive(Default)]
struct ExternSpecAttrs {
    /// The path prefix of the extern spec.
    ///
    /// In the example, the mod_path is `std::vec` and the `Vec` gets expanded
    /// to `std::vec::Vec`.
    mod_path: Option<syn::Path>,
    /// Any generics that the extern spec takes. A module path has to be
    /// specified to take generics - an empty module path or `::` should suffice
    /// if one is not necessary.
    ///
    /// In the example, the sole generic is the variable `T`. The dummy struct that
    /// gets expanded has `T` as an argument on it. Without this generic,
    /// we would get a compile error because the dummy struct would look like
    ///
    /// ```ignore
    /// struct FluxExternStructVec(Vec<T>);
    /// ```
    ///
    /// and the `T` would not be in scope.
    generics: Option<syn::Generics>,
}

enum ExternSpecAttr {
    ModPath(syn::Path),
    Generics(syn::Generics),
}

impl Parse for ExternSpecAttr {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        // Extract an ident, erroring if there isn't one.
        let ident: Ident = input.step(|cursor| {
            if let Some((tt, next)) = cursor.token_tree() {
                match tt {
                    TokenTree::Ident(ident) => {
                        Ok((ident, next))
                    }
                    _ => {
                        Err(cursor.error(format!("Bad token {}: expecting an extern spec identifier (mod_path or generics)", tt)))
                    }
                }
            } else {
                Err(cursor.error("Empty stream: expecting an extern spec attribute, ex: mod_path = mod::path::def or generics = < Generics, List >"))
            }
        })?;
        let _equals_token: Token![=] = input.parse()?;
        match &ident.to_string()[..] {
            "mod_path" => input.parse().map(Self::ModPath),
            "generics" => input.parse().map(Self::Generics),
            _ => {
                Err(input
                    .error(format!("Unexpected ident {}, expecting mod_path or generics", ident)))
            }
        }
    }
}

impl Parse for ExternSpecAttrs {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let punctuated_attrs: Punctuated<ExternSpecAttr, Token![,]> =
            input.parse_terminated(ExternSpecAttr::parse)?;
        let mut attrs = ExternSpecAttrs::default();
        for attr in punctuated_attrs {
            match attr {
                ExternSpecAttr::ModPath(mod_path) => {
                    if attrs.mod_path.is_some() {
                        return Err(
                            input.error("Invalid extern_spec: duplicate mod_path attribute")
                        );
                    }
                    attrs.mod_path = Some(mod_path);
                }
                ExternSpecAttr::Generics(generics) => {
                    if attrs.generics.is_some() {
                        return Err(
                            input.error("Invalid extern_spec: duplicate generics attribute")
                        );
                    }
                    attrs.generics = Some(generics);
                }
            }
        }
        Ok(attrs)
    }
}

pub fn extern_spec(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    transform_extern_spec(attr, tokens).unwrap_or_else(|err| err.to_compile_error())
}

fn transform_extern_spec(attr: TokenStream, tokens: TokenStream) -> syn::Result<TokenStream> {
    let extern_spec_attrs: ExternSpecAttrs = syn::parse2(attr)?;
    let span = tokens.span();
    match syn::parse2::<syn::Item>(tokens) {
        // TODO: impls
        Ok(syn::Item::Impl(_item_impl)) => {
            unimplemented!()
        }
        Ok(syn::Item::Struct(item_struct)) => create_dummy_struct(extern_spec_attrs, item_struct),
        // Function stubs end up as Verbatim
        Ok(syn::Item::Verbatim(tokens)) => {
            let (sig, attrs) = extract_sig_from_stub(tokens)?;
            create_dummy_fn(extern_spec_attrs, sig, attrs)
        }
        Ok(_) => Err(syn::Error::new(
            span,
            "Invalid extern_spec: the only items which are supported are impls and function stubs",
        )),
        Err(_) => {
            Err(syn::Error::new(span, "Invalid extern_spec: could not parse associated item"))
        }
    }
}

/// Create a dummy struct with a single unnamed field that is the external struct.
///
/// Example:
///
/// ```ignore
/// #[extern_spec(mod_path = alloc::vec)]
/// #[flux::refined_by(n: int)]
/// struct Vec<T>;
///
/// =>
///
/// #[flux::extern_spec]
/// #[allow(unused, dead_code)]
/// #[flux::refined_by(n: int)]
/// struct FluxExternStructVec(alloc::vec::Vec<T>);
/// ```
fn create_dummy_struct(
    attrs: ExternSpecAttrs,
    item_struct: syn::ItemStruct,
) -> syn::Result<TokenStream> {
    let item_struct_span = item_struct.span();
    let fields_span = item_struct.fields.span();
    if let syn::Fields::Unit = item_struct.fields {
        let mut dummy_struct = item_struct.clone();
        let ident = item_struct.ident;
        let generics = item_struct.generics;
        dummy_struct.ident = format_ident!("FluxExternStruct{}", ident);
        dummy_struct.semi_token = None;
        let dummy_field: syn::FieldsUnnamed = if let Some(mod_path) = attrs.mod_path {
            parse_quote_spanned! {item_struct_span =>
                ( #mod_path :: #ident #generics )
            }
        } else {
            parse_quote_spanned! {item_struct_span =>
                ( #ident #generics )
            }
        };
        dummy_struct.fields = syn::Fields::Unnamed(dummy_field);
        dummy_struct.generics =
            if let Some(generics) = attrs.generics { generics } else { syn::Generics::default() };
        let dummy_struct_with_attrs: syn::ItemStruct = parse_quote_spanned! { item_struct_span =>
            #[flux::extern_spec]
            #[allow(unused, dead_code)]
            #dummy_struct
        };
        Ok(dummy_struct_with_attrs.to_token_stream())
    } else {
        Err(syn::Error::new(
            fields_span,
            "Extern specs on structs cannot have fields, i.e. they must look like struct Vec<T>;",
        ))
    }
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
/// 3. Add any generic parameters in the extern spec to the generic params of the new function.
/// 4. Replace its body with a single expression that is a function call.
/// 5. The function call is of the form mod_path::fn_ident<generic_args>(params)
///    where the generic args and params have been modified so that they function as
///    arguments to the call instead of being a part of the function signature.
/// 6. Finally, we suppress dead_code/unused warnings and add the flux::extern_spec
///    so that flux knows this is the generated dummy function for the external function
///    that is being called.
fn create_dummy_fn(
    extern_spec_attrs: ExternSpecAttrs,
    sig: syn::Signature,
    attrs: Vec<syn::Attribute>,
) -> syn::Result<TokenStream> {
    let span = sig.span();
    let mut mangled_sig = sig.clone();
    let ident = sig.ident;
    mangled_sig.ident = format_ident!("flux_extern_spec_{}", ident);
    if let Some(generics) = extern_spec_attrs.generics {
        mangled_sig.generics.params.extend(generics.params);
    }
    let generic_call_args = transform_generic_params_to_call_args(sig.generics.params);
    let call_args = transform_params_to_call_args(sig.inputs);
    let fn_path: syn::Path = if let Some(mod_path) = extern_spec_attrs.mod_path {
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
