mod ast;
mod extern_spec;

use proc_macro2::{Ident, TokenStream, TokenTree};
use quote::{quote, quote_spanned, ToTokens};
use syn::{parse_quote, spanned::Spanned, Attribute, ItemEnum, ItemStruct};

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
        flux_tool_attrs(&mut variant.attrs, &["variant"]);
    }
}

fn refined_by_struct(item_struct: &mut ItemStruct) {
    for field in &mut item_struct.fields {
        flux_tool_attrs(&mut field.attrs, &["field"]);
    }
}

fn flux_tool_attrs(attrs: &mut Vec<Attribute>, names: &[&str]) {
    let mut j = 0;
    for i in 0..attrs.len() {
        if cfg!(flux_sysroot) {
            if path_is_one_of(attrs[i].path(), names) {
                flux_tool_attr(&mut attrs[i]);
                attrs.swap(i, j);
                j += 1;
            }
        } else if !path_is_one_of(attrs[i].path(), names) {
            attrs.swap(i, j);
            j += 1;
        }
    }
    if !cfg!(flux_sysroot) {
        attrs.truncate(j);
    }
}

fn path_is_one_of(path: &syn::Path, idents: &[&str]) -> bool {
    idents.iter().any(|ident| path.is_ident(ident))
}

fn flux_tool_attr(attr: &mut Attribute) {
    let path = match &mut attr.meta {
        syn::Meta::Path(path) => path,
        syn::Meta::List(metalist) => &mut metalist.path,
        syn::Meta::NameValue(namevalue) => &mut namevalue.path,
    };
    *path = parse_quote!(flux_tool::#path);
}

pub fn flux(tokens: TokenStream) -> TokenStream {
    syn::parse2::<ast::Items>(tokens)
        .map_or_else(|err| err.to_compile_error(), ToTokens::into_token_stream)
}

pub fn defs(tokens: TokenStream) -> TokenStream {
    quote! {
        mod flux_defs {
            #![flux::defs {
                #tokens
            }]
        }
    }
}
