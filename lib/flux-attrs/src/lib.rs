mod ast;
mod extern_spec;

use proc_macro2::{Ident, TokenStream, TokenTree};
use quote::ToTokens;
use syn::{parse_quote, spanned::Spanned, Attribute, ItemEnum, ItemStruct};

pub fn extern_spec(attr: TokenStream, tokens: TokenStream) -> TokenStream {
    extern_spec::transform_extern_spec(attr, tokens).unwrap_or_else(|err| err.to_compile_error())
}

pub fn flux_tool_attr(name: &str, attr: TokenStream, item: TokenStream) -> TokenStream {
    let name = TokenTree::Ident(Ident::new(name, attr.span()));
    let a = quote::quote! {
        #[flux_tool::#name(#attr)]
        #item
    };
    println!("{}", a.to_token_stream());
    a
}

pub fn flux_tool_adt_attr(name: &str, attr: TokenStream, item: TokenStream) -> TokenStream {
    let span = item.span();
    let mut item = match syn::parse2::<syn::Item>(item) {
        Ok(item) => item,
        Err(err) => return err.to_compile_error(),
    };

    match &mut item {
        syn::Item::Enum(item_enum) => {
            if let Err(err) = transform_enum(item_enum) {
                return err.into_compile_error();
            }
        }
        syn::Item::Struct(item_struct) => {
            if let Err(err) = transform_struct(item_struct) {
                return err.into_compile_error();
            }
        }

        _ => return syn::Error::new(span, "expected struct or enum").to_compile_error(),
    }

    println!("{}", item.to_token_stream());

    let name = TokenTree::Ident(Ident::new(name, attr.span()));
    quote::quote! {
        #[flux_tool::#name(#attr)]
        #item
    }
}

fn transform_enum(item_enum: &mut ItemEnum) -> syn::Result<()> {
    for variant in &mut item_enum.variants {
        transform_helper_attrs(&mut variant.attrs, "variant")?;
    }
    Ok(())
}

fn transform_struct(item_struct: &mut ItemStruct) -> syn::Result<()> {
    for field in &mut item_struct.fields {
        transform_helper_attrs(&mut field.attrs, "field")?;
    }
    Ok(())
}

fn transform_helper_attrs(attrs: &mut Vec<Attribute>, name: &str) -> syn::Result<()> {
    let mut j = 0;
    for i in 0..attrs.len() {
        if !attrs[i].meta.path().is_ident(name) {
            continue;
        }
        if cfg!(flux_sysroot) {
            attrs[i] = transform_helper_attr(&attrs[i], name)?;
        } else {
            attrs.swap(i, j);
            j += 1;
        }
    }
    if cfg!(sys_root) {
        attrs.truncate(j);
    }
    Ok(())
}

fn transform_helper_attr(attr: &Attribute, name: &str) -> syn::Result<Attribute> {
    let metalist = &attr.meta.require_list()?;
    let tokens = &metalist.tokens;
    let name = Ident::new(name, metalist.path.span());
    Ok(parse_quote!(#[flux_tool::#name(#tokens)]))
}

pub fn flux(tokens: TokenStream) -> TokenStream {
    syn::parse2::<ast::Items>(tokens)
        .map_or_else(|err| err.to_compile_error(), ToTokens::into_token_stream)
}
