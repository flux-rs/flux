use std::mem;

use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote, quote_spanned, ToTokens, TokenStreamExt};
use syn::{
    braced,
    parse::{Parse, ParseStream},
    parse_quote, parse_quote_spanned,
    punctuated::Punctuated,
    spanned::Spanned,
    token::Brace,
    Attribute, Expr, FnArg, GenericArgument, GenericParam, Generics, Signature, Token, Type,
    TypePath,
};

use crate::flux_tool_attrs;

pub(crate) fn transform_extern_spec(
    attr: TokenStream,
    tokens: TokenStream,
) -> syn::Result<TokenStream> {
    let mod_path: Option<syn::Path> =
        if !attr.is_empty() { Some(syn::parse2(attr)?) } else { None };
    let mod_use = mod_path.map(UseWildcard);
    let span = tokens.span();
    match syn::parse2::<ExternItem>(tokens)? {
        ExternItem::Struct(item_struct) => extern_struct_to_tokens(mod_use, item_struct),
        ExternItem::Enum(item_enum) => extern_enum_to_tokens(mod_use, item_enum),
        ExternItem::Trait(item_trait) => extern_trait_to_tokens(mod_use, item_trait),
        ExternItem::Fn(extern_fn) => extern_fn_to_tokens(mod_use, extern_fn),
        ExternItem::Impl(extern_item_impl) => {
            extern_impl_to_tokens(span, mod_use, extern_item_impl)
        }
    }
}

fn extern_fn_to_tokens(
    mod_use: Option<UseWildcard>,
    mut extern_fn: ExternFn,
) -> syn::Result<TokenStream> {
    extern_fn.prepare(None, None, true);
    Ok(quote! {
        #[flux_tool::extern_spec]
        const _: () = {
            #mod_use

            #extern_fn
        };
    })
}

fn extern_enum_to_tokens(
    mod_use: Option<UseWildcard>,
    mut item_enum: syn::ItemEnum,
) -> syn::Result<TokenStream> {
    let span = item_enum.span();
    let ident = item_enum.ident;

    item_enum.ident = format_ident!("__FluxExternEnum{}", ident);

    flux_tool_attrs(&mut item_enum.attrs);
    for variant in &mut item_enum.variants {
        flux_tool_attrs(&mut variant.attrs);
    }

    let dummy_struct = format_ident!("__FluxExternVariant");
    let generics = &item_enum.generics;
    let args = generic_params_to_args(&generics.params);

    Ok(quote_spanned! {span=>
        #[flux_tool::extern_spec]
        const _: () = {
            #mod_use

            struct #dummy_struct #generics ( #ident < #args > );

            #[allow(unused, dead_code)]
            #item_enum
        };
    })
}

fn extern_struct_to_tokens(
    mod_use: Option<UseWildcard>,
    mut item_struct: syn::ItemStruct,
) -> syn::Result<TokenStream> {
    let item_struct_span = item_struct.span();
    let ident = item_struct.ident;

    let generics = &item_struct.generics;
    let args = generic_params_to_args(&generics.params);

    // Prepare struct
    item_struct.ident = format_ident!("__FluxExternSpecStruct{}", ident);
    flux_tool_attrs(&mut item_struct.attrs);
    for field in &mut item_struct.fields {
        flux_tool_attrs(&mut field.attrs);
    }
    if let syn::Fields::Unit = &item_struct.fields {
        if !has_opaque_attr(&item_struct.attrs) {
            item_struct.attrs.push(parse_quote!(#[flux_tool::opaque]));
        }
        item_struct.fields = syn::Fields::Unnamed(parse_quote! { (#ident < #args >) });
    }

    // Dummy struct used to extract def_id
    let dummy_struct = format_ident!("__FluxExternSpecExtract{}", ident);

    Ok(quote_spanned! {item_struct_span =>
        #[allow(unused, dead_code)]
        #[flux_tool::extern_spec]
        const _: () = {
            #mod_use

            struct #dummy_struct #generics (#ident < #args >);

            #item_struct
        };
    })
}

fn has_opaque_attr(attrs: &[syn::Attribute]) -> bool {
    attrs
        .iter()
        .any(|attr| path_matches(attr.path(), &["flux_tool", "opaque"]))
}

fn path_matches(path: &syn::Path, x: &[&str]) -> bool {
    let mut i = 0;
    for segment in &path.segments {
        if i == x.len() {
            return false;
        }
        if segment.ident != x[i] {
            return false;
        }
        i += 1;
    }
    true
}

fn extern_trait_to_tokens(
    mod_use: Option<UseWildcard>,
    item_trait: syn::ItemTrait,
) -> syn::Result<TokenStream> {
    let item_trait_span = item_trait.span();
    if !item_trait.supertraits.is_empty() {
        return Err(syn::Error::new(
            item_trait.supertraits.span(),
            "invalid extern spec: extern specs on traits cannot have supertraits",
        ));
    }
    if !item_trait.items.is_empty() {
        return Err(syn::Error::new(
            item_trait_span,
            "invalid extern spec: extern specs on traits cannot have items",
        ));
    }

    let trait_ident = item_trait.ident;
    let mut attrs = item_trait.attrs;
    flux_tool_attrs(&mut attrs);

    let generics = item_trait.generics;
    let args = generic_params_to_args(&generics.params);

    let dummy_ident = format_ident!("__FluxExternTrait{}", trait_ident);
    let super_trait = quote!(#trait_ident < # args >);

    Ok(quote_spanned! {item_trait_span =>
        #[flux_tool::extern_spec]
        #[allow(unused, dead_code)]
        const _: () = {
            #mod_use

            #(#attrs)*
            trait #dummy_ident #generics: #super_trait {}
        };
    })
}

fn extern_impl_to_tokens(
    span: Span,
    mod_use: Option<UseWildcard>,
    mut extern_item_impl: ExternItemImpl,
) -> syn::Result<TokenStream> {
    extern_item_impl.prepare();
    let extern_item_impl = extern_item_impl; // no more mutation

    let self_ty = &extern_item_impl.self_ty;
    let (impl_generics, ty_generics, where_clause) = &extern_item_impl.generics.split_for_impl();

    let dummy_ident = &extern_item_impl.dummy_ident;
    let mut fields = generic_params_to_fields(&extern_item_impl.generics.params);
    fields.push(parse_quote!(#self_ty));

    let dummy_impl = if let Some((_, trait_, _)) = &extern_item_impl.trait_ {
        Some(quote!(
            impl #impl_generics #dummy_ident #ty_generics #where_clause {
                fn __flux_extern_extract_impl_id() where #self_ty: #trait_ {}
            }
        ))
    } else {
        None
    };

    Ok(quote_spanned! {span=>
        #[allow(unused, dead_code, unused_variables)]
        #[flux_tool::extern_spec]
        const _: () = {
            #mod_use

            struct #dummy_ident #impl_generics ( #fields ) #where_clause;

            #dummy_impl

            #extern_item_impl
        };
    })
}

enum ExternItem {
    Struct(syn::ItemStruct),
    Enum(syn::ItemEnum),
    Trait(syn::ItemTrait),
    Fn(ExternFn),
    Impl(ExternItemImpl),
}

struct ExternFn {
    attrs: Vec<Attribute>,
    sig: Signature,
    block: Option<TokenStream>,
}

struct ExternItemImpl {
    attrs: Vec<Attribute>,
    impl_token: Token![impl],
    generics: Generics,
    trait_: Option<(Option<Token![!]>, syn::Path, Token![for])>,
    self_ty: Box<Type>,
    brace_token: Brace,
    items: Vec<ExternFn>,
    dummy_ident: syn::Ident,
}

impl ExternItem {
    fn replace_attrs(&mut self, new: Vec<Attribute>) -> Vec<Attribute> {
        match self {
            ExternItem::Struct(syn::ItemStruct { attrs, .. })
            | ExternItem::Enum(syn::ItemEnum { attrs, .. })
            | ExternItem::Trait(syn::ItemTrait { attrs, .. })
            | ExternItem::Fn(ExternFn { attrs, .. })
            | ExternItem::Impl(ExternItemImpl { attrs, .. }) => mem::replace(attrs, new),
        }
    }
}

impl ExternItemImpl {
    fn prepare(&mut self) {
        flux_tool_attrs(&mut self.attrs);
        let trait_ = self.trait_.as_ref().map(|(_, path, _)| path);

        for item in &mut self.items {
            item.prepare(Some(&self.self_ty), trait_, false);
        }
    }
}

impl ToTokens for ExternItemImpl {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let (impl_generics, ty_generics, where_clause) = self.generics.split_for_impl();

        tokens.append_all(&self.attrs);

        self.impl_token.to_tokens(tokens);
        impl_generics.to_tokens(tokens);

        self.dummy_ident.to_tokens(tokens);
        ty_generics.to_tokens(tokens);

        where_clause.to_tokens(tokens);
        self.brace_token.surround(tokens, |tokens| {
            for item in &self.items {
                item.to_tokens(tokens);
            }
        });
    }
}

impl ExternFn {
    fn prepare(&mut self, self_ty: Option<&syn::Type>, trait_: Option<&syn::Path>, mangle: bool) {
        flux_tool_attrs(&mut self.attrs);
        if let Some(self_ty) = self_ty {
            struct ReplaceSelf<'a> {
                self_ty: &'a syn::Type,
            }

            impl syn::visit_mut::VisitMut for ReplaceSelf<'_> {
                fn visit_type_mut(&mut self, ty: &mut syn::Type) {
                    if let syn::Type::Path(type_path) = ty {
                        if type_path.path.is_ident("Self") {
                            *ty = self.self_ty.clone();
                        }
                    }
                }
            }

            syn::visit_mut::visit_signature_mut(&mut ReplaceSelf { self_ty }, &mut self.sig);

            self.change_receiver(self_ty);
        }
        self.fill_body(self_ty, trait_);
        if mangle {
            self.sig.ident = format_ident!("__flux_extern_spec_{}", self.sig.ident);
        }
    }

    fn change_receiver(&mut self, self_ty: &syn::Type) {
        if let Some(first) = self.sig.inputs.first_mut() {
            if let FnArg::Receiver(receiver) = first {
                let ident = format_ident!("__self", span = receiver.self_token.span);

                *first = if receiver.colon_token.is_some() {
                    // If there's a colon this is an arbitrary self types and we leave it as is.
                    let receiver_ty = &receiver.ty;
                    parse_quote!(#ident : #receiver_ty)
                } else if let Some((ampersand, lft)) = &receiver.reference {
                    let mutbl = receiver.mutability;
                    parse_quote!(#ident : #ampersand #lft #mutbl #self_ty)
                } else {
                    parse_quote!(#ident : #self_ty)
                };
            }
        }
    }

    fn fill_body(&mut self, self_ty: Option<&syn::Type>, trait_: Option<&syn::Path>) {
        let ident = &self.sig.ident;
        let fn_path = match (self_ty, trait_) {
            (None, _) => quote!(#ident),
            (Some(self_ty), None) => quote!(< #self_ty > :: #ident),
            (Some(self_ty), Some(trait_)) => {
                quote!(< #self_ty as #trait_ > :: #ident)
            }
        };
        let generic_args = generic_params_to_args(&self.sig.generics.params);
        let fn_args = fn_params_to_args(&self.sig.inputs);
        self.block = Some(quote!({ #fn_path :: <#generic_args> ( #fn_args ) }));
    }
}

impl ToTokens for ExternFn {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        debug_assert!(self.block.is_some());
        tokens.append_all(&self.attrs);
        self.sig.to_tokens(tokens);
        self.block.to_tokens(tokens);
    }
}

impl Parse for ExternItem {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let attrs = input.call(Attribute::parse_outer)?;
        let lookahead = input.lookahead1();
        let mut item = if lookahead.peek(Token![fn]) {
            ExternItem::Fn(input.parse()?)
        } else if lookahead.peek(Token![impl]) {
            ExternItem::Impl(input.parse()?)
        } else if lookahead.peek(Token![struct]) {
            ExternItem::Struct(input.parse()?)
        } else if lookahead.peek(Token![enum]) {
            let enm = input.parse();
            ExternItem::Enum(enm?)
        } else if lookahead.peek(Token![trait]) {
            ExternItem::Trait(input.parse()?)
        } else {
            return Err(lookahead.error());
        };
        item.replace_attrs(attrs);
        Ok(item)
    }
}

impl Parse for ExternFn {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let attrs = input.call(Attribute::parse_outer)?;
        let sig = input.parse()?;
        input.parse::<Token![;]>()?;
        Ok(ExternFn { attrs, sig, block: None })
    }
}

impl Parse for ExternItemImpl {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let attrs = input.call(Attribute::parse_outer)?;
        let impl_token = input.parse()?;
        let generics = input.parse()?;

        let mut first_ty: Type = input.parse()?;
        let self_ty: Type;
        let trait_;

        let is_impl_for = input.peek(Token![for]);
        if is_impl_for {
            let for_token: Token![for] = input.parse()?;
            let mut first_ty_ref = &first_ty;
            while let Type::Group(ty) = first_ty_ref {
                first_ty_ref = &ty.elem;
            }
            if let Type::Path(TypePath { qself: None, .. }) = first_ty_ref {
                while let Type::Group(ty) = first_ty {
                    first_ty = *ty.elem;
                }
                if let Type::Path(TypePath { qself: None, path }) = first_ty {
                    trait_ = Some((None, path, for_token));
                } else {
                    unreachable!();
                }
            } else {
                trait_ = None;
            }
            self_ty = input.parse()?;
        } else {
            trait_ = None;
            self_ty = first_ty;
        }

        let content;
        let brace_token = braced!(content in input);
        let mut items = Vec::new();
        while !content.is_empty() {
            items.push(content.parse()?);
        }

        let mut dummy_prefix = "__FluxExternImplStruct".to_string();
        if let Some(trait_path) = trait_.as_ref().map(|(_, path, _)| path) {
            dummy_prefix.push_str(&create_dummy_string_from_path(trait_path)?);
        }
        let dummy_ident = create_dummy_ident(&mut dummy_prefix, &self_ty)?;

        Ok(ExternItemImpl {
            attrs,
            impl_token,
            generics,
            trait_,
            self_ty: Box::new(self_ty),
            brace_token,
            items,
            dummy_ident,
        })
    }
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
                format!("invalid extern_spec: unsupported type {:?}", ty),
            ))
        }
    }
}

fn create_dummy_string_from_path(path: &syn::Path) -> syn::Result<String> {
    if let Some(path_segment) = path.segments.last() {
        // Mangle the identifier using the dummy_prefix
        let str = format!("{}", path_segment.ident);
        Ok(str)
    } else {
        Err(syn::Error::new(path.span(), format!("invalid extern_spec: empty Path {:?}", path)))
    }
}

fn create_dummy_ident_from_path(dummy_prefix: &str, path: &syn::Path) -> syn::Result<syn::Ident> {
    // For paths, we mangle the last identifier
    if let Some(path_segment) = path.segments.last() {
        // Mangle the identifier using the dummy_prefix
        let ident = syn::Ident::new(
            &format!("{}{}", dummy_prefix, path_segment.ident),
            path_segment.ident.span(),
        );
        Ok(ident)
    } else {
        Err(syn::Error::new(path.span(), format!("invalid extern_spec: empty Path {:?}", path)))
    }
}

// Cribbed from Prusti's extern_spec_rewriter
fn generic_params_to_args(
    generic_params: &Punctuated<GenericParam, Token!(,)>,
) -> Punctuated<GenericArgument, Token!(,)> {
    generic_params
        .iter()
        .map(|param| -> GenericArgument {
            let span = param.span();
            match param {
                GenericParam::Type(syn::TypeParam { ident, .. }) => {
                    parse_quote_spanned!(span => #ident )
                }
                GenericParam::Lifetime(syn::LifetimeParam { lifetime, .. }) => {
                    parse_quote_spanned!(span => #lifetime )
                }
                GenericParam::Const(syn::ConstParam { ident, .. }) => {
                    parse_quote_spanned!(span => #ident )
                }
            }
        })
        .collect()
}

/// Given a list of generic parameters creates a list of fields that use all non-const parameters
fn generic_params_to_fields(
    params: &Punctuated<GenericParam, Token![,]>,
) -> Punctuated<syn::Field, Token![,]> {
    params
        .iter()
        .filter_map(|param| -> Option<syn::Field> {
            let span = param.span();
            match param {
                GenericParam::Lifetime(syn::LifetimeParam { lifetime, .. }) => {
                    Some(parse_quote_spanned!(span=> &#lifetime ()))
                }
                GenericParam::Type(syn::TypeParam { ident, .. }) => {
                    Some(parse_quote_spanned!(span=> #ident))
                }
                GenericParam::Const(..) => None,
            }
        })
        .collect()
}

// Cribbed from Prusti's extern_spec_rewriter
fn fn_params_to_args(params: &Punctuated<FnArg, Token!(,)>) -> Punctuated<Expr, Token!(,)> {
    params
        .iter()
        .map(|param| -> Expr {
            match param {
                FnArg::Typed(pat_type) => {
                    match pat_type.pat.as_ref() {
                        syn::Pat::Ident(pat) => {
                            let ident = &pat.ident;
                            parse_quote!(#ident)
                        }
                        _ => {
                            unimplemented!(
                                "extern specs don't support patterns other than simple identifiers"
                            )
                        }
                    }
                }
                FnArg::Receiver(_) => {
                    let span = param.span();
                    parse_quote_spanned!(span=> self)
                }
            }
        })
        .collect()
}

struct UseWildcard(syn::Path);

impl ToTokens for UseWildcard {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let path = &self.0;
        tokens.extend(quote!(use #path::*;))
    }
}
