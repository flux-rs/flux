use std::mem;

use proc_macro2::TokenStream;
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
    match syn::parse2::<ExternItem>(tokens)? {
        ExternItem::Struct(item_struct) => extern_struct_spec(mod_path, item_struct),
        ExternItem::Enum(item_enum) => extern_enum_spec(mod_path, item_enum),
        ExternItem::Trait(item_trait) => extern_trait_spec(mod_path, item_trait),
        ExternItem::Fn(mut extern_fn) => {
            extern_fn.prepare(&mod_path, None, None, true);
            Ok(extern_fn.into_token_stream())
        }
        ExternItem::Impl(extern_item_impl) => extern_impl_spec(mod_path, extern_item_impl),
    }
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
    mod_path: Option<syn::Path>,
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
    fn prepare(&mut self, mod_path: Option<syn::Path>) -> syn::Result<()> {
        self.mod_path = mod_path;
        let trait_ = self.trait_.as_ref().map(|(_, path, _)| path);

        for item in &mut self.items {
            item.prepare(&self.mod_path, Some(&self.self_ty), trait_, false);
        }
        Ok(())
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

            if let Some((_, trait_, _for_token)) = &self.trait_ {
                let self_ty = &self.self_ty;
                quote!(
                    #[flux_tool::fake_impl]
                    #[flux_tool::ignore]
                    fn __flux_extern_impl_fake_method<FluxFake : #trait_>(x: #self_ty) {}
                )
                .to_tokens(tokens);
            }
        });
    }
}

impl ExternFn {
    fn prepare(
        &mut self,
        mod_path: &Option<syn::Path>,
        self_ty: Option<&syn::Type>,
        trait_: Option<&syn::Path>,
        mangle: bool,
    ) {
        flux_tool_attrs(&mut self.attrs);
        if let Some(self_ty) = self_ty {
            self.change_receiver(self_ty);
        }
        self.fill_body(mod_path, self_ty, trait_);
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

    fn fill_body(
        &mut self,
        mod_path: &Option<syn::Path>,
        self_ty: Option<&syn::Type>,
        trait_: Option<&syn::Path>,
    ) {
        let ident = &self.sig.ident;
        let fn_path = match (mod_path, self_ty, trait_) {
            (None, None, _) => quote_spanned! { ident.span() => #ident },
            (Some(mod_path), None, _) => quote_spanned!(ident.span()=> #mod_path :: #ident ),
            (None, Some(self_ty), None) => quote_spanned!(ident.span()=> < #self_ty > :: #ident ),
            (None, Some(self_ty), Some(trait_)) => {
                quote_spanned!(ident.span()=> < #self_ty as #trait_ > :: #ident )
            }
            (Some(mod_path), Some(self_ty), None) => {
                quote_spanned!(ident.span()=> < #mod_path :: #self_ty > :: #ident )
            }
            (Some(mod_path), Some(self_ty), Some(trait_)) => {
                quote_spanned!(ident.span()=> < #mod_path :: #self_ty as #trait_ > :: #ident )
            }
        };
        let generic_args = generic_params_to_args(&self.sig.generics.params);
        let args = fn_params_to_args(&self.sig.inputs);
        self.block = Some(quote!( { #fn_path :: <#generic_args> ( #args ) } ));
    }
}

impl ToTokens for ExternFn {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        debug_assert!(self.block.is_some());
        quote!(#[flux::extern_spec]).to_tokens(tokens);
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
            mod_path: None,
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

/// Create a dummy enum with the same variants and an extra `Fake` variant that contains the original type
/// Also see the note in [lower_adt_def]
/// Example:
///
/// ```ignore
/// #[extern_spec]
/// enum Option<T> {
///     #[flux::variant(Option<T>[false])]
///     None,
///     #[flux::variant({T} -> Option<T>[true])]
///     Some(T),
/// }
///
/// =>
///
/// #[flux::extern_spec]
/// #[allow(unused, dead_code)]
/// #[flux::refined_by(b:bool)]
/// pub enum __FluxExternEnumOption<T> {
///     #[flux::variant(Option<T>[false])]
///     None,
///     #[flux::variant({T} -> Option<T>[true])]
///     Some(T),
///     // this fellow is here just so we can get a hold of the original `Option` ...
///     FluxExternEnumFake(Option<T>),
/// }
/// ```
fn extern_enum_spec(
    mod_path: Option<syn::Path>,
    mut item_enum: syn::ItemEnum,
) -> syn::Result<TokenStream> {
    let span = item_enum.span();
    let ident = item_enum.ident;

    item_enum.ident = format_ident!("__FluxExternEnum{}", ident);

    flux_tool_attrs(&mut item_enum.attrs);
    for variant in &mut item_enum.variants {
        flux_tool_attrs(&mut variant.attrs);
    }

    let dummy_variant_name = format_ident!("__FluxExternVariant");
    let args = generic_params_to_args(&item_enum.generics.params);
    let dummy_variant: syn::Variant = if let Some(mod_path) = mod_path {
        parse_quote_spanned! {span =>
            #dummy_variant_name ( #mod_path :: #ident < #args > )
        }
    } else {
        parse_quote_spanned! {span =>
            #dummy_variant_name ( #ident < #args >)
        }
    };
    item_enum.variants.push(dummy_variant);

    Ok(quote_spanned! {span =>
        const _: () = {
            #[allow(unused, dead_code)]
            #[flux_tool::extern_spec]
            #item_enum
        };
    })
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
fn extern_struct_spec(
    mod_path: Option<syn::Path>,
    item_struct: syn::ItemStruct,
) -> syn::Result<TokenStream> {
    let item_struct_span = item_struct.span();
    let fields_span = item_struct.fields.span();
    let syn::Fields::Unit = item_struct.fields else {
        return Err(syn::Error::new(
            fields_span,
            "invalid extern spec: extern specs on structs cannot have fields, i.e. they must look like struct Vec<T>;",
        ));
    };

    let struct_ident = item_struct.ident;
    let dummy_ident = format_ident!("__FluxExternStruct{}", struct_ident);
    let mut attrs = item_struct.attrs;
    flux_tool_attrs(&mut attrs);
    let generics = item_struct.generics;
    let args = generic_params_to_args(&generics.params);
    let field = if let Some(mod_path) = mod_path {
        quote!(#mod_path :: #struct_ident < #args >)
    } else {
        quote!(#struct_ident < #args >)
    };

    Ok(quote_spanned! {item_struct_span =>
        const _: () = {
            #[flux_tool::extern_spec]
            #[allow(unused, dead_code)]
            #(#attrs)*
            struct #dummy_ident #generics (#field);
        };
    })
}

/// Create a dummy trait with a single super-trait that is the external trait
///
/// Example:
///
/// ```ignore
/// #[extern_spec(std::vec)]
/// #[flux::generics(Self as base)]
/// #[flux::assoc(fn f(self: Self) -> bool)]
/// trait MyTrait {}
///
/// =>
///
/// #[flux::extern_spec]
/// #[allow(unused, dead_code)]
/// #[flux::generics(Self as base)]
/// #[flux::assoc(fn f(self: Self) -> bool)]
/// trait __FluxExternTraitMyTrait: MyTrait {}
/// ```
fn extern_trait_spec(
    mod_path: Option<syn::Path>,
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

    let super_trait = if let Some(mod_path) = mod_path {
        quote_spanned! {item_trait_span =>
            #mod_path :: #trait_ident < #args >
        }
    } else {
        quote_spanned! {item_trait_span =>
            #trait_ident < # args >
        }
    };
    Ok(quote_spanned! {item_trait_span =>
        const _: () = {
            #[flux_tool::extern_spec]
            #[allow(unused, dead_code)]
            #(#attrs)*
            trait #dummy_ident #generics: #super_trait {}
        };
    })
}

fn extern_impl_spec(
    mod_path: Option<syn::Path>,
    mut extern_item_impl: ExternItemImpl,
) -> syn::Result<TokenStream> {
    extern_item_impl.prepare(mod_path)?;

    let dummy_impl_struct = &extern_item_impl.dummy_ident;
    let generics = &extern_item_impl.generics;
    let fields = generic_params_to_fields(&extern_item_impl.generics.params);

    Ok(quote! {
        #[allow(unused, dead_code, unused_variables)]
        const _: () = {
            #[flux_tool::ignore]
            struct #dummy_impl_struct #generics ( #fields );

            #[flux_tool::extern_spec]
            #extern_item_impl
        };
    })
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
