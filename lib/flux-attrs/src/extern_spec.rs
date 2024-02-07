use std::mem;

use proc_macro2::TokenStream;
use quote::{format_ident, quote, quote_spanned, ToTokens, TokenStreamExt};
use syn::{
    braced,
    parse::{Parse, ParseStream},
    parse_quote_spanned,
    punctuated::Punctuated,
    spanned::Spanned,
    token::{Brace, Comma},
    Attribute, Expr, FnArg, GenericArgument, GenericParam, Generics, ItemStruct, Signature, Token,
    Type, TypePath,
};

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
    dummy_ident: Option<syn::Ident>,
}

impl ExternItem {
    fn replace_attrs(&mut self, new: Vec<Attribute>) -> Vec<Attribute> {
        match self {
            ExternItem::Struct(ItemStruct { attrs, .. })
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
        // TODO(RJ): need a unique-id instead of this hack (#generics), to generate distinct struct (names)
        // for multiple impl blocks for the same type (see rset03.rs)

        let trait_ = self.trait_.as_ref().map(|(_, path, _)| path.clone());

        let mut dummy_prefix = format!("__FluxExternImplStruct{:?}", self.generics.params.len());
        if let Some(trait_path) = &trait_ {
            dummy_prefix.push_str(&create_dummy_string_from_path(trait_path)?);
        }

        self.dummy_ident = Some(create_dummy_ident(&mut dummy_prefix, &self.self_ty)?);
        for item in &mut self.items {
            item.prepare(&self.mod_path, Some(&self.self_ty), &trait_, false);
        }
        Ok(())
    }

    fn find_generics_attr(&self) -> Option<&Attribute> {
        self.attrs.iter().find(|attr| {
            let segments = &attr.path().segments;
            if segments.len() != 2 {
                return false;
            }
            segments[0].ident == "flux" && segments[1].ident == "generics"
        })
    }

    fn dummy_impl_struct(&self) -> syn::ItemStruct {
        let self_ty = &self.self_ty;

        let mut params = self.generics.params.clone();
        strip_generics_eq_default(&mut params);

        let struct_field: syn::FieldsUnnamed = if let Some(mod_path) = &self.mod_path {
            if params.is_empty() {
                parse_quote_spanned!(self_ty.span()=> ( #mod_path :: #self_ty ) )
            } else {
                parse_quote_spanned!(self_ty.span()=> ( #params, #mod_path :: #self_ty ) )
            }
        } else if params.is_empty() {
            parse_quote_spanned!(self_ty.span()=> ( #self_ty ) )
        } else {
            parse_quote_spanned!(self_ty.span()=> ( #params, #self_ty ) )
        };

        syn::ItemStruct {
            attrs: self.find_generics_attr().into_iter().cloned().collect(),
            vis: syn::Visibility::Inherited,
            struct_token: syn::token::Struct { span: self.impl_token.span },
            ident: self.dummy_ident.as_ref().unwrap().clone(),
            generics: self.generics.clone(),
            fields: syn::Fields::Unnamed(struct_field),
            semi_token: Some(syn::token::Semi { spans: [self.impl_token.span] }),
        }
    }
}

impl ToTokens for ExternItemImpl {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let dummy_struct = self.dummy_impl_struct();
        dummy_struct.to_tokens(tokens);
        let (impl_generics, ty_generics, where_clause) = self.generics.split_for_impl();

        quote!(#[allow(unused, dead_code)]).to_tokens(tokens);
        quote!(#[flux::extern_spec]).to_tokens(tokens);
        tokens.append_all(&self.attrs);

        self.impl_token.to_tokens(tokens);
        impl_generics.to_tokens(tokens);

        let dummy_ident = self.dummy_ident.as_ref().unwrap();
        quote!(#dummy_ident #ty_generics).to_tokens(tokens);
        where_clause.to_tokens(tokens);
        self.brace_token.surround(tokens, |tokens| {
            for item in &self.items {
                item.to_tokens(tokens);
            }

            if let Some((_, trait_, _for_token)) = &self.trait_ {
                let self_ty = &self.self_ty;
                quote!(#[allow(unused_variables)]).to_tokens(tokens);
                // TODO: this is simpler but somehow fails, see note in [_extract_extern_def_id_from_extern_spec_impl_new]
                // let fake_fn =
                //     quote!(fn __flux_extern_impl_fake_method() where #self_ty : #trait_, {});
                let fake_fn =
                    quote!(fn __flux_extern_impl_fake_method<FluxFake : #trait_>(x: #self_ty) {});
                quote!(#[flux::fake_impl]).to_tokens(tokens);
                fake_fn.to_tokens(tokens);
            }
        });
    }
}

impl ExternFn {
    fn prepare(
        &mut self,
        mod_path: &Option<syn::Path>,
        self_ty: Option<&syn::Type>,
        trait_: &Option<syn::Path>,
        mangle: bool,
    ) {
        self.fill_body(mod_path, self_ty, trait_);
        if mangle {
            self.sig.ident = format_ident!("__flux_extern_spec_{}", self.sig.ident);
        }
    }

    fn fill_body(
        &mut self,
        mod_path: &Option<syn::Path>,
        self_ty: Option<&syn::Type>,
        trait_: &Option<syn::Path>,
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
        let args = params_to_args(&self.sig.inputs);
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

        Ok(ExternItemImpl {
            attrs,
            impl_token,
            generics,
            trait_,
            self_ty: Box::new(self_ty),
            brace_token,
            items,
            mod_path: None,
            dummy_ident: None,
        })
    }
}

pub(crate) fn transform_extern_spec(
    attr: TokenStream,
    tokens: TokenStream,
) -> syn::Result<TokenStream> {
    let mod_path: Option<syn::Path> =
        if !attr.is_empty() { Some(syn::parse2(attr)?) } else { None };
    match syn::parse2::<ExternItem>(tokens)? {
        ExternItem::Struct(item_struct) => create_dummy_struct(mod_path, item_struct),
        ExternItem::Enum(item_enum) => create_dummy_enum(mod_path, item_enum),
        ExternItem::Trait(item_trait) => create_dummy_trait(mod_path, item_trait),
        ExternItem::Fn(mut extern_fn) => {
            extern_fn.prepare(&mod_path, None, &None, true);
            Ok(extern_fn.into_token_stream())
        }
        ExternItem::Impl(mut extern_item_impl) => {
            extern_item_impl.prepare(mod_path)?;
            Ok(extern_item_impl.into_token_stream())
        }
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

/// Takes a `syn::Generics` (obtained from the *definition* of a struct or impl) and removes all the
/// stuff that is not needed for *uses* i.e. in the anonymous field of the dummy struct.
///
/// Example:
/// Given
/// ```ignore
/// #[extern_spec]
/// struct HashSet<T, S = RandomState>;
/// ```
/// we want to remove the `S = RandomState` part from the generics of the dummy struct to generate
/// ```ignore
/// struct __FluxExternStructHashSet<T, S = RandomState>(HashSet<T, S>);
/// ```
fn strip_generics_eq_default(params: &mut Punctuated<GenericParam, Comma>) {
    for param in params {
        match param {
            GenericParam::Type(type_param) => {
                type_param.bounds = Punctuated::new();
                type_param.eq_token = None;
                type_param.default = None;
            }
            GenericParam::Lifetime(lifetime_param) => {
                lifetime_param.colon_token = None;
            }
            GenericParam::Const(const_param) => {
                const_param.eq_token = None;
                const_param.default = None;
            }
        }
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
/// ```
///
/// =>
///
/// ```ignore
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
fn create_dummy_enum(
    mod_path: Option<syn::Path>,
    item_enum: syn::ItemEnum,
) -> syn::Result<TokenStream> {
    let item_enum_span = item_enum.span();
    let mut dummy_enum = item_enum.clone();
    let ident = item_enum.ident;
    let mut generics = item_enum.generics;
    strip_generics_eq_default(&mut generics.params);

    dummy_enum.ident = format_ident!("__FluxExternEnum{}", ident);
    let dummy_variant_name = format_ident!("FluxExternEnumFake");

    let dummy_variant: syn::Variant = if let Some(mod_path) = mod_path {
        parse_quote_spanned! {item_enum_span =>
                              #dummy_variant_name ( #mod_path :: #ident #generics )
        }
    } else {
        parse_quote_spanned! {item_enum_span =>
                              #dummy_variant_name ( #ident #generics )
        }
    };

    dummy_enum.variants.push(dummy_variant);

    let dummy_enum_with_attrs: syn::ItemEnum = parse_quote_spanned! { item_enum_span =>
                                                                          #[flux::extern_spec]
                                                                          #[allow(unused, dead_code)]
                                                                          #dummy_enum
    };
    Ok(dummy_enum_with_attrs.to_token_stream())
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
    let syn::Fields::Unit = item_struct.fields else {
        return Err(syn::Error::new(
            fields_span,
            "invalid extern spec: extern specs on structs cannot have fields, i.e. they must look like struct Vec<T>;",
        ));
    };
    let mut dummy_struct = item_struct.clone();
    let ident = item_struct.ident;
    let mut generics = item_struct.generics;
    strip_generics_eq_default(&mut generics.params);

    dummy_struct.ident = format_ident!("__FluxExternStruct{}", ident);
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
fn create_dummy_trait(
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

    let mut dummy_trait = item_trait.clone();
    let ident = item_trait.ident;
    let mut generics = item_trait.generics;
    strip_generics_eq_default(&mut generics.params);

    dummy_trait.ident = format_ident!("__FluxExternTrait{}", ident);
    dummy_trait.auto_token = None;

    let dummy_super: syn::TypeParamBound = if let Some(mod_path) = mod_path {
        parse_quote_spanned! {item_trait_span =>
                              ( #mod_path :: #ident #generics )
        }
    } else {
        parse_quote_spanned! {item_trait_span =>
                              ( #ident #generics )
        }
    };
    dummy_trait.supertraits.push(dummy_super);
    let dummy_trait_with_attrs: syn::ItemTrait = parse_quote_spanned! { item_trait_span =>
        #[flux::extern_spec]
        #[allow(unused, dead_code)]
        #dummy_trait
    };
    Ok(dummy_trait_with_attrs.to_token_stream())
}

// Cribbed from Prusti's extern_spec_rewriter
fn generic_params_to_args(
    generic_params: &Punctuated<GenericParam, Token!(,)>,
) -> Punctuated<GenericArgument, Token!(,)> {
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
        })
        .collect()
}

// Cribbed from Prusti's extern_spec_rewriter
fn params_to_args(params: &Punctuated<FnArg, Token!(,)>) -> Punctuated<Expr, Token!(,)> {
    params
        .iter()
        .map(|param| -> Expr {
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
        })
        .collect()
}
