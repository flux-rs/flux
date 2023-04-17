#![feature(proc_macro_diagnostic)]

use proc_macro2::TokenStream;
use quote::{format_ident, quote_spanned, ToTokens};
use syn::{
    parse_quote, parse_quote_spanned, punctuated::Punctuated, spanned::Spanned, Expr, FnArg,
    GenericArgument, GenericParam, Token,
};

pub fn extern_spec(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    transform_extern_spec(attr, tokens).unwrap_or_else(|err| err.to_compile_error())
}

fn transform_extern_spec(attr: TokenStream, tokens: TokenStream) -> syn::Result<TokenStream> {
    // let extern_spec_attrs: ExternSpecAttrs = syn::parse2(attr)?;
    let mod_path: Option<syn::Path> =
        if !attr.is_empty() { Some(syn::parse2(attr)?) } else { None };
    let span = tokens.span();
    match syn::parse2::<syn::Item>(tokens) {
        Ok(syn::Item::Struct(item_struct)) => create_dummy_struct(mod_path, item_struct),
        // Function stubs end up as Verbatim
        Ok(syn::Item::Verbatim(tokens)) => {
            let (sig, attrs) = extract_sig_from_stub(tokens)?;
            create_dummy_fn(mod_path, None, sig, attrs)
        }
        Ok(syn::Item::Impl(item_impl)) => create_dummy_impl(mod_path, item_impl),
        Ok(_) => Err(syn::Error::new(
            span,
            "Invalid extern_spec: the only items which are supported are structs, impls, and function stubs",
        )),
        Err(_) => {
            Err(syn::Error::new(span, "Invalid extern_spec: could not parse associated item"))
        }
    }
}

/// Creates a dummy impl and supporting struct.
///
/// Here's how it works at a high level.
///
/// 1. Mangle the Self type's name and create a struct similar to the one
/// created from create_dummy_struct. We will make an impl on this struct that
/// mirrors the extern impl.
/// 2. Create an impl for the struct made in step 1. that follows the structure
/// of the original impl.
/// 3. Convert each method inside of the impl into a dummy function using
/// create_dummy_fn. We pass both the mod_path and the original Self type so
/// that create_dummy_fn can create the proper function call.
///
/// Example:
///
/// ```ignore
/// #[extern_spec]
/// impl<T> [T] {
///     #[flux::sig(fn(&[T][@n]) -> usize[n])]
///     fn len(v: &[T]) -> usize;
/// }
///
/// =>
///
/// #[allow(unused, dead_code)]
/// struct<T> FluxExternImplStructRefSliceT<T>(&[T]);
/// #[allow(unused, dead_code)]
/// impl<T> FluxExternImplStructRefSliceT<T> {
///     #[flux::extern_spec]
///     #[flux::sig(fn(&[T][@n]) -> usize[n])]
///     #[allow(unused, dead_code)]
///     fn len(v: &[T]) -> usize {
///         <&[T]>::len(v)
///     }
/// }
/// ```
fn create_dummy_impl(
    mod_path: Option<syn::Path>,
    item_impl: syn::ItemImpl,
) -> syn::Result<TokenStream> {
    let self_ty_span = item_impl.self_ty.as_ref().span();
    let mod_path_clone = mod_path.clone();
    // This field corresponds to the Self type. Reading the mod_path
    // from the extern_spec attr is probably not strictly necessary, but
    // we do it so our behavior is consistent.
    let self_ty = item_impl.self_ty.as_ref();
    let struct_field: syn::FieldsUnnamed = if let Some(mod_path) = mod_path {
        parse_quote_spanned! { self_ty_span => ( #mod_path :: #self_ty ) }
    } else {
        parse_quote_spanned! { self_ty_span => ( #self_ty ) }
    };
    // The name of this struct is mangled to ensure that it doesn't
    // conflict with an actual impl. Same with the name of the type.
    let dummy_ident =
        create_dummy_ident(&mut "FluxExternImplStruct".to_string(), item_impl.self_ty.as_ref())?;
    let mut dummy_self_ty_path = syn::TypePath {
        qself: None,
        path: syn::Path { leading_colon: None, segments: Punctuated::new() },
    };
    // Copy the generics onto the dummy self type
    if !item_impl.generics.params.is_empty() {
        let generics_span = item_impl.generics.span();
        let generics = item_impl.generics.clone();
        let generic_arguments: syn::AngleBracketedGenericArguments =
            parse_quote_spanned! { generics_span => #generics };
        dummy_self_ty_path.path.segments.push(syn::PathSegment {
            ident: dummy_ident.clone(),
            arguments: syn::PathArguments::AngleBracketed(generic_arguments),
        });
    } else {
        dummy_self_ty_path.path.segments.push(syn::PathSegment {
            ident: dummy_ident.clone(),
            arguments: syn::PathArguments::None,
        });
    }
    let dummy_self_ty = syn::Type::Path(dummy_self_ty_path);
    let mut dummy_impl = item_impl.clone();
    let item_impl_span = item_impl.span();
    let mut item_struct = syn::ItemStruct {
        attrs: item_impl.attrs,
        vis: syn::Visibility::Inherited,
        struct_token: syn::token::Struct { span: item_impl.impl_token.span },
        ident: dummy_ident,
        generics: item_impl.generics.clone(),
        fields: syn::Fields::Unnamed(struct_field),
        semi_token: Some(syn::token::Semi { spans: [item_impl_span] }),
    };
    // Both the struct and its impl end up unused so we add these attributes.
    let allow_attr: syn::Attribute = parse_quote!(#[allow(unused, dead_code)]);
    item_struct.attrs.push(allow_attr.clone());
    dummy_impl.attrs.push(allow_attr);
    dummy_impl.self_ty = Box::new(dummy_self_ty);
    dummy_impl.items = item_impl.items.into_iter().map(|impl_item| {
        match impl_item {
            // For whatever reason, syn parses function stubs correctly
            // by assuming that the semicolon at their end is wrapped in
            // braces (functions require a brace-delimited list of Items
            // inside of them, the semicolon gets converted to a
            // Verbatim).
            //
            // This does however mean that we will silently discard the
            // contents of any "implementation" of an extern function.
            syn::ImplItem::Method(impl_item_method) => {
                let span = impl_item_method.span();
                let dummy_fn_tokens = create_dummy_fn(mod_path_clone.clone(), Some(self_ty.clone()), impl_item_method.sig, impl_item_method.attrs)?;
                Ok(parse_quote_spanned! { span => #dummy_fn_tokens })
            }
            // Both of these should be OK
            syn::ImplItem::Type(_) | syn::ImplItem::Const(_) => Ok(impl_item),
            _ => {
                Err(syn::Error::new(
                    impl_item.span(),
                    format!("Invalid extern_spec: invalid impl item: {:?}\n extern impls may only contain function stubs such as fn len(v: &Vec<T>) -> usize;", impl_item)
                ))
            }
        }
    }).collect::<syn::Result<Vec<syn::ImplItem>>>()?;
    Ok(TokenStream::from_iter(
        [item_struct.to_token_stream(), dummy_impl.to_token_stream()].into_iter(),
    ))
}

fn create_dummy_ident(dummy_prefix: &mut String, ty: &syn::Type) -> syn::Result<syn::Ident> {
    use syn::Type::*;
    match ty {
        Reference(ty_ref) => {
            if ty_ref.mutability.is_some() {
                dummy_prefix.push_str("Mut");
            };
            dummy_prefix.push_str("Ref");
            create_dummy_ident(dummy_prefix, ty_ref.elem.as_ref())
        }
        Slice(ty_slice) => {
            dummy_prefix.push_str("Slice");
            create_dummy_ident(dummy_prefix, ty_slice.elem.as_ref())
        }
        Path(ty_path) => create_dummy_ident_from_path(dummy_prefix, &ty_path.path),
        _ => {
            Err(syn::Error::new(
                ty.span(),
                format!("Invalid extern_spec: unsupported type {:?}", ty),
            ))
        }
    }
}

fn create_dummy_ident_from_path(
    dummy_prefix: &mut String,
    path: &syn::Path,
) -> syn::Result<syn::Ident> {
    // For paths, we mangle the last identifier
    if let Some(path_segment) = path.segments.last() {
        // Mangle the identifier using the dummy_prefix
        let ident = syn::Ident::new(
            &format!("{}{}", dummy_prefix, path_segment.ident),
            path_segment.ident.span(),
        );
        Ok(ident)
    } else {
        Err(syn::Error::new(path.span(), format!("Invalid extern_spec: empty Path {:?}", path)))
    }
}

/// Create a dummy struct with a single unnamed field that is the external struct.
///
/// Example:
///
/// ```ignore
/// #[extern_spec(std::vec)]
/// #[flux::refined_by(n: int)]
/// struct Vec<T>;
///
/// =>
///
/// #[flux::extern_spec]
/// #[allow(unused, dead_code)]
/// #[flux::refined_by(n: int)]
/// struct FluxExternStructVec<T>(std::vec::Vec<T>);
/// ```
fn create_dummy_struct(
    mod_path: Option<syn::Path>,
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
        let dummy_field: syn::FieldsUnnamed = if let Some(mod_path) = mod_path {
            parse_quote_spanned! {item_struct_span =>
                ( #mod_path :: #ident #generics )
            }
        } else {
            parse_quote_spanned! {item_struct_span =>
                ( #ident #generics )
            }
        };
        dummy_struct.fields = syn::Fields::Unnamed(dummy_field);
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
/// 3. Replace its body with a single expression that is a function call.
/// 4. The function call is of the form mod_path::fn_ident<generic_args>(params)
///    where the generic args and params have been modified so that they function as
///    arguments to the call instead of being a part of the function signature.
/// 5. Finally, we suppress dead_code/unused warnings and add the flux::extern_spec
///    so that flux knows this is the generated dummy function for the external function
///    that is being called.
fn create_dummy_fn(
    mod_path: Option<syn::Path>,
    self_ty: Option<syn::Type>,
    sig: syn::Signature,
    attrs: Vec<syn::Attribute>,
) -> syn::Result<TokenStream> {
    let span = sig.span();
    let mut mangled_sig = sig.clone();
    let ident = sig.ident;
    mangled_sig.ident = format_ident!("flux_extern_spec_{}", ident);
    let generic_call_args = transform_generic_params_to_call_args(sig.generics.params);
    let call_args = transform_params_to_call_args(sig.inputs);
    let fn_path: syn::TypePath = match (mod_path, self_ty) {
        // I'm sure there's a more clever way to deal with the :: between
        // mod_path and ident, but let's just be explicit so that we get it
        // right.
        (None, None) => parse_quote_spanned!( ident.span() => #ident ),
        (Some(mod_path), None) => parse_quote_spanned!( ident.span() => #mod_path :: #ident ),
        (None, Some(self_ty)) => parse_quote_spanned!( ident.span() => < #self_ty > :: #ident ),
        (Some(mod_path), Some(self_ty)) => {
            parse_quote_spanned!( ident.span() => < #mod_path :: #self_ty > :: #ident )
        }
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
