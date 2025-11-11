mod ast;
mod extern_spec;

use proc_macro2::{Ident, TokenStream, TokenTree};
use quote::{ToTokens, quote, quote_spanned};
use syn::{
    Attribute, ItemEnum, ItemStruct, Token, bracketed, parse::ParseStream, parse_quote,
    spanned::Spanned,
};

pub const FLUX_ATTRS: &[&str] = &[
    "assoc",
    "field",
    "generics",
    "invariant",
    "opaque",
    "reflect",
    "refined_by",
    "sig",
    "trusted",
    "trusted_impl",
    "proven_externally",
    "variant",
    "should_fail",
    "opts",
    "reft",
    "no_panic",
];

pub fn extern_spec(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    extern_spec::transform_extern_spec(attr, tokens).unwrap_or_else(|err| err.to_compile_error())
}

pub fn flux_tool_item_attr(name: &str, attr: TokenStream, item: TokenStream) -> TokenStream {
    // I don't really know what I'm doing here, but spanning the quote with the item's span seems
    // to behave correctly.
    let span = item.span();
    let name = TokenTree::Ident(Ident::new(name, span));
    if attr.is_empty() {
        quote_spanned! {span=>
            #[flux_tool::#name]
            #item
        }
    } else {
        quote_spanned! {span=>
            #[flux_tool::#name(#attr)]
            #item
        }
    }
}

pub fn refined_by(attr: TokenStream, item: TokenStream) -> TokenStream {
    let span = item.span();
    let mut item = match syn::parse2::<syn::Item>(item) {
        Ok(item) => item,
        Err(err) => return err.to_compile_error(),
    };

    match &mut item {
        syn::Item::Enum(item_enum) => refined_by_enum(item_enum),
        syn::Item::Struct(item_struct) => refined_by_struct(item_struct),
        _ => return syn::Error::new(span, "expected struct or enum").to_compile_error(),
    }

    if cfg!(flux_sysroot) {
        quote_spanned! {span=>
            #[flux_tool::refined_by(#attr)]
            #item
        }
    } else {
        item.to_token_stream()
    }
}

fn refined_by_enum(item_enum: &mut ItemEnum) {
    for variant in &mut item_enum.variants {
        flux_tool_attrs(&mut variant.attrs);
    }
}

fn refined_by_struct(item_struct: &mut ItemStruct) {
    for field in &mut item_struct.fields {
        flux_tool_attrs(&mut field.attrs);
    }
}

fn flux_tool_attrs(attrs: &mut Vec<Attribute>) {
    if cfg!(flux_sysroot) {
        for attr in attrs {
            transform_flux_attr(attr);
        }
    } else {
        attrs.retain(|attr| !is_flux_attr(attr));
    }
}

fn path_is_one_of(path: &syn::Path, idents: &[&str]) -> bool {
    idents.iter().any(|ident| path.is_ident(ident))
}

fn is_flux_attr(attr: &syn::Attribute) -> bool {
    let path = attr.path();
    if path.segments.len() >= 2 {
        let ident = &path.segments[0].ident;
        ident == "flux" || ident == "flux_rs"
    } else {
        path_is_one_of(path, FLUX_ATTRS)
    }
}

fn transform_flux_attr(attr: &mut syn::Attribute) {
    let path = path_of_attr_mut(attr);
    if path.leading_colon.is_some() {
        return;
    }
    if path.segments.len() >= 2 {
        let ident = &mut path.segments[0].ident;
        if ident == "flux" || ident == "flux_rs" {
            *ident = Ident::new("flux_tool", ident.span());
        }
        return;
    } else if path_is_one_of(path, FLUX_ATTRS) {
        *path = parse_quote!(flux_tool::#path);
    }
}

fn path_of_attr_mut(attr: &mut Attribute) -> &mut syn::Path {
    match &mut attr.meta {
        syn::Meta::Path(path) => path,
        syn::Meta::List(metalist) => &mut metalist.path,
        syn::Meta::NameValue(namevalue) => &mut namevalue.path,
    }
}

pub fn flux(tokens: TokenStream) -> TokenStream {
    syn::parse2::<ast::Items>(tokens)
        .map_or_else(|err| err.to_compile_error(), ToTokens::into_token_stream)
}

pub fn defs(tokens: TokenStream) -> TokenStream {
    quote! {
        #[flux::defs { #tokens }]
        const _: () = {};
    }
}

pub fn tokens_or_default<T: ToTokens + Default>(x: Option<&T>, tokens: &mut TokenStream) {
    match x {
        Some(t) => t.to_tokens(tokens),
        None => T::default().to_tokens(tokens),
    }
}

fn parse_inner(input: ParseStream, attrs: &mut Vec<Attribute>) -> syn::Result<()> {
    while input.peek(Token![#]) && input.peek2(Token![!]) {
        attrs.push(input.call(single_parse_inner)?);
    }
    Ok(())
}

fn single_parse_inner(input: ParseStream) -> syn::Result<Attribute> {
    let content;
    Ok(Attribute {
        pound_token: input.parse()?,
        style: syn::AttrStyle::Inner(input.parse()?),
        bracket_token: bracketed!(content in input),
        meta: content.parse()?,
    })
}

fn outer(attrs: &[Attribute]) -> impl Iterator<Item = &Attribute> {
    fn is_outer(attr: &&Attribute) -> bool {
        match attr.style {
            syn::AttrStyle::Outer => true,
            syn::AttrStyle::Inner(_) => false,
        }
    }
    attrs.iter().filter(is_outer)
}

fn inner(attrs: &[Attribute]) -> impl Iterator<Item = &Attribute> {
    fn is_inner(attr: &&Attribute) -> bool {
        match attr.style {
            syn::AttrStyle::Outer => false,
            syn::AttrStyle::Inner(_) => true,
        }
    }
    attrs.iter().filter(is_inner)
}
