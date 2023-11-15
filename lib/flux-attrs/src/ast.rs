use std::mem;

use proc_macro2::{TokenStream, TokenTree};
use quote::{quote, quote_spanned, ToTokens, TokenStreamExt};
use syn::{
    braced, bracketed,
    ext::IdentExt,
    parenthesized,
    parse::{Parse, ParseStream, Peek},
    punctuated::Punctuated,
    token::{self, Mut, Paren},
    Attribute, Generics, Ident, Result, Token, Visibility,
};

pub struct Items(Vec<Item>);

pub enum Item {
    Struct(ItemStruct),
    Enum(syn::ItemEnum),
    Use(syn::ItemUse),
    Type(ItemType),
    Fn(ItemFn),
    Impl(ItemImpl),
}

#[derive(Debug)]
pub struct ItemFn {
    pub attrs: Vec<Attribute>,
    pub vis: Visibility,
    pub sig: Signature,
    pub block: Block,
}

pub struct ItemStruct {
    pub attrs: Vec<Attribute>,
    pub vis: Visibility,
    pub struct_token: Token![struct],
    pub ident: Ident,
    pub generics: Generics,
    pub refined_by: RefinedBy,
    pub fields: Fields,
    pub semi_token: Option<Token![;]>,
}

pub struct RefinedBy {
    pub refined_by: Option<(kw::refined, kw::by)>,
    pub bracket_token: token::Bracket,
    pub params: Punctuated<RefinedByParam, Token![,]>,
}

pub struct RefinedByParam {
    pub ident: Ident,
    pub colon_token: Option<Token![:]>,
    pub sort: Ident,
}

pub enum Fields {
    /// Named fields of a struct or struct variant such as `Point { x: f64,
    /// y: f64 }`.
    Named(FieldsNamed),

    /// Unnamed fields of a tuple struct or tuple variant such as `Some(T)`.
    Unnamed(FieldsUnnamed),

    /// Unit struct or unit variant such as `None`.
    Unit,
}

pub struct FieldsNamed {
    pub brace_token: token::Brace,
    pub named: Punctuated<Field, Token![,]>,
}

pub struct FieldsUnnamed {
    pub paren_token: token::Paren,
    pub unnamed: Punctuated<Field, Token![,]>,
}

pub struct Field {
    pub attrs: Vec<Attribute>,

    pub vis: Visibility,

    pub mutability: syn::FieldMutability,

    /// Name of the field, if any.
    ///
    /// Fields of tuple structs have no names.
    pub ident: Option<Ident>,

    pub colon_token: Option<Token![:]>,

    pub ty: Type,
}

pub struct ItemType {
    pub attrs: Vec<Attribute>,
    pub vis: Visibility,
    pub type_token: Token![type],
    pub ident: Ident,
    pub generics: Generics,
    pub index_params: Option<IndexParams>,
    pub eq_token: Token![=],
    pub ty: Box<Type>,
    pub semi_token: Token![;],
}

pub struct IndexParams {
    pub bracket_token: token::Bracket,
    pub params: Punctuated<ExistsParam, Token![,]>,
}

pub struct ItemImpl {
    pub attrs: Vec<Attribute>,
    pub impl_token: Token![impl],
    pub generics: Generics,
    pub trait_: Option<(syn::Path, Token![for])>,
    /// The Self type of the impl.
    pub self_ty: Box<syn::Type>,
    pub brace_token: token::Brace,
    pub items: Vec<ImplItem>,
}

pub enum ImplItem {
    Fn(ImplItemFn),
    Type(syn::ImplItemType),
}

pub struct ImplItemFn {
    pub attrs: Vec<Attribute>,
    pub vis: Visibility,
    pub sig: Signature,
    pub block: Block,
}

#[derive(Debug)]
pub struct Signature {
    pub fn_token: Token![fn],
    pub ident: Ident,
    pub generics: Generics,
    pub paren_token: Paren,
    pub inputs: Punctuated<FnArg, Token![,]>,
    pub output: ReturnType,
    pub requires: Option<Requires>,
    pub ensures: Option<Ensures>,
}

#[derive(Debug)]
pub struct Ensures {
    pub ensures_token: kw::ensures,
    pub constraints: Punctuated<Constraint, Token![,]>,
}

#[derive(Debug)]
pub struct Requires {
    pub requires_token: kw::requires,
    pub constraint: Expr,
}

#[derive(Debug)]
pub struct Constraint {
    pub ident: Ident,
    pub colon_token: Token![:],
    pub ty: Box<Type>,
}

#[derive(Debug)]
pub enum FnArg {
    StrgRef(StrgRef),
    Typed(PatType),
}

#[derive(Debug)]
pub struct PatType {
    pub pat: Pat,
    pub colon_token: Token![:],
    pub ty: Type,
    pub pred: Option<PatTypePredicate>,
}

#[derive(Debug)]
pub enum Pat {
    Ident(PatIdent),
    Wild(Token![_]),
}

#[derive(Debug)]
pub struct PatIdent {
    pub mutability: Option<Token![mut]>,
    pub ident: Ident,
}

#[derive(Debug)]
pub struct PatTypePredicate {
    pub brace_token: token::Brace,
    pub pred: Expr,
}

#[derive(Debug)]
pub struct StrgRef {
    pub pat: Pat,
    pub colon_token: Token![:],
    pub and_token: Token![&],
    pub strg_token: kw::strg,
    pub ty: Box<Type>,
}

#[derive(Debug)]
pub enum Type {
    Base(BaseType),
    Indexed(TypeIndexed),
    Exists(TypeExists),
    GeneralExists(TypeGeneralExists),
    Reference(TypeReference),
    Constraint(TypeConstraint),
    Array(TypeArray),
}

#[derive(Debug)]
pub struct TypeIndexed {
    pub bty: BaseType,
    pub bracket_token: token::Bracket,
    pub expr: Expr,
}

#[derive(Debug)]
pub struct TypeExists {
    pub bty: BaseType,
    pub brace_token: token::Brace,
    pub ident: Ident,
    pub colon_token: Token![:],
    pub expr: Expr,
}

#[derive(Debug)]
pub struct TypeGeneralExists {
    pub brace_token: token::Brace,
    pub params: Punctuated<ExistsParam, Token![,]>,
    pub dot_token: Token![.],
    pub ty: Box<Type>,
    pub or_token: Option<Token![|]>,
    pub pred: Option<Expr>,
}

#[derive(Debug)]
pub struct ExistsParam {
    pub ident: Ident,
    pub colon_token: Option<Token![:]>,
    pub sort: Option<Ident>,
}

#[derive(Debug)]
pub struct TypeReference {
    pub and_token: Token![&],
    pub mutability: Option<Mut>,
    pub elem: Box<Type>,
}

#[derive(Debug)]
pub struct TypeConstraint {
    pub brace_token: token::Brace,
    pub ty: Box<Type>,
    pub or_token: Token![|],
    pub pred: Expr,
}

#[derive(Debug)]
pub struct TypeArray {
    pub bracket_token: token::Bracket,
    pub ty: Box<Type>,
    pub semi_token: Token![;],
    pub len: TokenStream,
}

#[derive(Debug)]
pub struct TypeHole {}

#[derive(Debug)]
pub enum BaseType {
    Path(Path),
    Slice(TypeSlice),
}

#[derive(Debug)]
pub struct Path {
    pub segments: Punctuated<PathSegment, Token![::]>,
}

#[derive(Debug)]
pub struct TypeSlice {
    pub bracket_token: token::Bracket,
    pub ty: Box<Type>,
}

#[derive(Debug)]
pub struct PathSegment {
    pub ident: Ident,
    pub arguments: PathArguments,
}

#[derive(Debug)]
pub enum PathArguments {
    None,
    AngleBracketed(AngleBracketedGenericArguments),
}

#[derive(Debug)]
pub struct AngleBracketedGenericArguments {
    pub lt_token: Token![<],
    pub args: Punctuated<GenericArgument, Token![,]>,
    pub gt_token: Token![>],
}

#[derive(Debug)]
pub enum GenericArgument {
    Type(Type),
}

#[derive(Debug)]
pub enum ReturnType {
    Default,
    Type(Token![->], Box<Type>),
}

pub type Expr = TokenStream;

#[derive(Debug)]
pub struct Block {
    pub brace_token: token::Brace,
    pub stmts: TokenStream,
}

impl Parse for Items {
    fn parse(input: ParseStream) -> Result<Self> {
        let mut result = Vec::new();
        while !input.is_empty() {
            let value = input.parse()?;
            result.push(value);
        }
        Ok(Self(result))
    }
}

impl Parse for Item {
    fn parse(input: ParseStream) -> Result<Self> {
        let attrs = input.call(Attribute::parse_outer)?;
        let ahead = input.fork();
        let _: Visibility = ahead.parse()?;
        let lookahead = ahead.lookahead1();
        let mut item = if lookahead.peek(Token![fn]) {
            Item::Fn(input.parse()?)
        } else if lookahead.peek(Token![impl]) {
            Item::Impl(input.parse()?)
        } else if lookahead.peek(Token![struct]) {
            Item::Struct(input.parse()?)
        } else if lookahead.peek(Token![enum]) {
            Item::Enum(input.parse()?)
        } else if lookahead.peek(Token![use]) {
            Item::Use(input.parse()?)
        } else if lookahead.peek(Token![type]) {
            Item::Type(input.parse()?)
        } else {
            return Err(lookahead.error());
        };
        item.replace_attrs(attrs);
        Ok(item)
    }
}

impl Parse for ItemStruct {
    fn parse(input: ParseStream) -> Result<Self> {
        let attrs = input.call(Attribute::parse_outer)?;
        let vis = input.parse::<Visibility>()?;
        let struct_token = input.parse::<Token![struct]>()?;
        let ident = input.parse::<Ident>()?;
        let generics = input.parse::<Generics>()?;
        let refined_by = input.parse::<RefinedBy>()?;
        let (where_clause, fields, semi_token) = data_struct(input)?;
        Ok(ItemStruct {
            attrs,
            vis,
            struct_token,
            ident,
            generics: Generics { where_clause, ..generics },
            refined_by,
            fields,
            semi_token,
        })
    }
}

impl Parse for RefinedBy {
    fn parse(input: ParseStream) -> Result<Self> {
        let refined_by =
            if input.peek(kw::refined) { Some((input.parse()?, input.parse()?)) } else { None };
        let content;
        Ok(RefinedBy {
            refined_by,
            bracket_token: bracketed!(content in input),
            params: Punctuated::parse_terminated(&content)?,
        })
    }
}

impl Parse for RefinedByParam {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(RefinedByParam {
            ident: input.parse()?,
            colon_token: input.parse()?,
            sort: input.parse()?,
        })
    }
}

fn data_struct(
    input: ParseStream,
) -> Result<(Option<syn::WhereClause>, Fields, Option<Token![;]>)> {
    let mut lookahead = input.lookahead1();
    let mut where_clause = None;
    if lookahead.peek(Token![where]) {
        where_clause = Some(input.parse()?);
        lookahead = input.lookahead1();
    }

    if where_clause.is_none() && lookahead.peek(token::Paren) {
        let fields = input.parse()?;

        lookahead = input.lookahead1();
        if lookahead.peek(Token![where]) {
            where_clause = Some(input.parse()?);
            lookahead = input.lookahead1();
        }

        if lookahead.peek(Token![;]) {
            let semi = input.parse()?;
            Ok((where_clause, Fields::Unnamed(fields), Some(semi)))
        } else {
            Err(lookahead.error())
        }
    } else if lookahead.peek(token::Brace) {
        let fields = input.parse()?;
        Ok((where_clause, Fields::Named(fields), None))
    } else if lookahead.peek(Token![;]) {
        let semi = input.parse()?;
        Ok((where_clause, Fields::Unit, Some(semi)))
    } else {
        Err(lookahead.error())
    }
}

impl Parse for FieldsUnnamed {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;
        Ok(FieldsUnnamed {
            paren_token: parenthesized!(content in input),
            unnamed: content.parse_terminated(Field::parse_unnamed, Token![,])?,
        })
    }
}

impl Parse for FieldsNamed {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;
        Ok(FieldsNamed {
            brace_token: braced!(content in input),
            named: content.parse_terminated(Field::parse_named, Token![,])?,
        })
    }
}

impl Field {
    fn parse_unnamed(input: ParseStream) -> Result<Self> {
        Ok(Field {
            attrs: input.call(Attribute::parse_outer)?,
            vis: input.parse()?,
            mutability: syn::FieldMutability::None,
            ident: None,
            colon_token: None,
            ty: input.parse()?,
        })
    }

    fn parse_named(input: ParseStream) -> Result<Self> {
        let attrs = input.call(Attribute::parse_outer)?;
        let vis: Visibility = input.parse()?;

        let ident = input.parse()?;
        let colon_token: Token![:] = input.parse()?;
        let ty = input.parse()?;
        Ok(Field {
            attrs,
            vis,
            mutability: syn::FieldMutability::None,
            ident: Some(ident),
            colon_token: Some(colon_token),
            ty,
        })
    }
}

impl Parse for ItemFn {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(ItemFn {
            attrs: input.call(Attribute::parse_outer)?,
            vis: input.parse()?,
            sig: input.parse()?,
            block: input.parse()?,
        })
    }
}

impl Parse for ItemType {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(ItemType {
            attrs: input.call(Attribute::parse_outer)?,
            vis: input.parse()?,
            type_token: input.parse()?,
            ident: input.parse()?,
            generics: input.parse()?,
            index_params: parse_index_params(input)?,
            eq_token: input.parse()?,
            ty: input.parse()?,
            semi_token: input.parse()?,
        })
    }
}

fn parse_index_params(input: ParseStream) -> Result<Option<IndexParams>> {
    if input.peek(token::Bracket) {
        let content;
        Ok(Some(IndexParams {
            bracket_token: bracketed!(content in input),
            params: Punctuated::parse_terminated(&content)?,
        }))
    } else {
        Ok(None)
    }
}

impl Parse for ItemImpl {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;
        let attrs = input.call(Attribute::parse_outer)?;
        let impl_token = input.parse()?;
        let generics = input.parse()?;

        let mut first_ty = input.parse()?;

        let trait_;
        let self_ty;
        if input.peek(Token![for]) {
            let for_token: Token![for] = input.parse()?;
            let mut first_ty_ref = &first_ty;
            while let syn::Type::Group(ty) = first_ty_ref {
                first_ty_ref = &ty.elem;
            }
            if let syn::Type::Path(syn::TypePath { qself: None, .. }) = first_ty_ref {
                while let syn::Type::Group(ty) = first_ty {
                    first_ty = *ty.elem;
                }
                if let syn::Type::Path(syn::TypePath { qself: None, path }) = first_ty {
                    trait_ = Some((path, for_token));
                } else {
                    unreachable!();
                }
            } else {
                return Err(syn::Error::new_spanned(first_ty_ref, "expected trait path"));
            }
            self_ty = input.parse()?;
        } else {
            trait_ = None;
            self_ty = first_ty;
        }

        Ok(ItemImpl {
            attrs,
            impl_token,
            generics,
            self_ty: Box::new(self_ty),
            trait_,
            brace_token: braced!(content in input),
            items: {
                let mut items = Vec::new();
                while !content.is_empty() {
                    let value = content.parse()?;
                    items.push(value);
                }
                items
            },
        })
    }
}

impl ImplItem {
    fn replace_attrs(&mut self, new: Vec<Attribute>) -> Vec<Attribute> {
        match self {
            ImplItem::Fn(ImplItemFn { attrs, .. })
            | ImplItem::Type(syn::ImplItemType { attrs, .. }) => mem::replace(attrs, new),
        }
    }
}

impl Parse for ImplItem {
    fn parse(input: ParseStream) -> Result<Self> {
        let attrs = input.call(Attribute::parse_outer)?;
        let ahead = input.fork();
        let _: Visibility = ahead.parse()?;
        let lookahead = ahead.lookahead1();
        let mut item = if lookahead.peek(Token![fn]) {
            ImplItem::Fn(input.parse()?)
        } else if lookahead.peek(Token![type]) {
            ImplItem::Type(input.parse()?)
        } else {
            return Err(lookahead.error());
        };
        item.replace_attrs(attrs);
        Ok(item)
    }
}

impl Parse for ImplItemFn {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(ImplItemFn {
            attrs: input.call(Attribute::parse_outer)?,
            vis: input.parse()?,
            sig: input.parse()?,
            block: input.parse()?,
        })
    }
}

impl Parse for Signature {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;
        let fn_token = input.parse()?;
        let ident = input.parse()?;
        let mut generics: syn::Generics = input.parse()?;
        let paren_token = parenthesized!(content in input);
        let inputs = content.parse_terminated(FnArg::parse, Token![,])?;
        let output = input.parse()?;
        generics.where_clause = input.parse()?;
        let requires = parse_requires(input)?;
        let ensures = parse_ensures(input)?;
        Ok(Signature { fn_token, ident, generics, paren_token, inputs, output, requires, ensures })
    }
}

fn parse_requires(input: ParseStream) -> Result<Option<Requires>> {
    if input.peek(kw::requires) {
        let requires_token = input.parse()?;
        let mut constraint = TokenStream::new();
        loop {
            let tt: TokenTree = input.parse()?;
            constraint.append(tt);
            if input.is_empty() || input.peek(kw::ensures) || input.peek(token::Brace) {
                break;
            }
        }
        Ok(Some(Requires { requires_token, constraint }))
    } else {
        Ok(None)
    }
}

fn parse_ensures(input: ParseStream) -> Result<Option<Ensures>> {
    if input.peek(kw::ensures) {
        Ok(Some(Ensures {
            ensures_token: input.parse()?,
            constraints: parse_until(input, Constraint::parse, Token![,], token::Brace)?,
        }))
    } else {
        Ok(None)
    }
}

impl Parse for Constraint {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Constraint {
            ident: parse_ident_or_self(input)?,
            colon_token: input.parse()?,
            ty: input.parse()?,
        })
    }
}

impl Parse for FnArg {
    fn parse(input: ParseStream) -> Result<Self> {
        let pat = input.parse()?;
        let colon_token = input.parse()?;
        let fn_arg = if input.peek(Token![&]) && input.peek2(kw::strg) {
            let and_token = input.parse()?;
            let strg_token = input.parse()?;
            let ty = input.parse()?;
            FnArg::StrgRef(StrgRef { pat, colon_token, and_token, strg_token, ty })
        } else if input.peek(Ident) {
            let bty: BaseType = input.parse()?;
            let mut pred = None;
            let ty = if input.peek(token::Bracket) {
                let content;
                Type::Indexed(TypeIndexed {
                    bty,
                    bracket_token: bracketed!(content in input),
                    expr: content.parse()?,
                })
            } else if input.peek(token::Brace) {
                let content;
                let brace_token = braced!(content in input);
                if content.peek(Ident) && content.peek2(Token![:]) {
                    Type::Exists(TypeExists {
                        bty,
                        brace_token,
                        ident: content.parse()?,
                        colon_token: content.parse()?,
                        expr: content.parse()?,
                    })
                } else {
                    pred = Some(PatTypePredicate { brace_token, pred: content.parse()? });
                    Type::Base(bty)
                }
            } else {
                Type::Base(bty)
            };
            FnArg::Typed(PatType { pat, colon_token, ty, pred })
        } else {
            FnArg::Typed(PatType { pat, colon_token, ty: input.parse()?, pred: None })
        };
        Ok(fn_arg)
    }
}

impl Parse for Pat {
    fn parse(input: ParseStream) -> Result<Self> {
        let pat = if input.peek(Token![_]) {
            Pat::Wild(input.parse()?)
        } else {
            Pat::Ident(PatIdent { mutability: input.parse()?, ident: parse_ident_or_self(input)? })
        };
        Ok(pat)
    }
}

impl Parse for ReturnType {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.peek(Token![->]) {
            Ok(ReturnType::Type(input.parse()?, input.parse()?))
        } else {
            Ok(ReturnType::Default)
        }
    }
}

impl Parse for Type {
    fn parse(input: ParseStream) -> Result<Self> {
        let ty = if input.peek(Token![&]) {
            Type::Reference(input.parse()?)
        } else if input.peek(token::Brace) {
            let content;
            let brace_token = braced!(content in input);
            if content.peek(Ident)
                && (content.peek2(Token![:])
                    || content.peek2(Token![,])
                    || content.peek2(Token![.]))
            {
                let params = parse_until(&content, ExistsParam::parse, Token![,], Token![.])?;
                let dot_token = content.parse()?;
                let ty = content.parse()?;
                let mut or_token = None;
                let mut pred = None;
                if content.peek(Token![|]) {
                    or_token = Some(content.parse()?);
                    pred = Some(content.parse()?);
                }
                Type::GeneralExists(TypeGeneralExists {
                    brace_token,
                    params,
                    dot_token,
                    ty,
                    or_token,
                    pred,
                })
            } else {
                Type::Constraint(TypeConstraint {
                    brace_token,
                    ty: content.parse()?,
                    or_token: content.parse()?,
                    pred: content.parse()?,
                })
            }
        } else if input.peek(token::Bracket) {
            let content;
            let bracket_token = bracketed!(content in input);
            let ty = content.parse()?;
            if content.peek(Token![;]) {
                Type::Array(TypeArray {
                    bracket_token,
                    ty,
                    semi_token: content.parse()?,
                    len: content.parse()?,
                })
            } else {
                parse_rty(&content, BaseType::Slice(TypeSlice { bracket_token, ty }))?
            }
        } else {
            parse_rty(input, input.parse()?)?
        };
        Ok(ty)
    }
}

fn parse_rty(input: ParseStream, bty: BaseType) -> Result<Type> {
    let ty = if input.peek(token::Bracket) {
        let content;
        Type::Indexed(TypeIndexed {
            bty,
            bracket_token: bracketed!(content in input),
            expr: content.parse()?,
        })
    } else if input.peek(token::Brace) {
        let ahead = input.fork();
        let mut content;
        braced!(content in ahead);
        if content.peek(Ident) && content.peek2(Token![:]) {
            Type::Exists(TypeExists {
                bty,
                brace_token: braced!(content in input),
                ident: content.parse()?,
                colon_token: content.parse()?,
                expr: content.parse()?,
            })
        } else {
            Type::Base(bty)
        }
    } else {
        Type::Base(bty)
    };
    Ok(ty)
}

impl Parse for TypeReference {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(TypeReference {
            and_token: input.parse()?,
            mutability: input.parse()?,
            elem: input.parse()?,
        })
    }
}

impl Parse for BaseType {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.peek(token::Bracket) {
            let content;
            Ok(BaseType::Slice(TypeSlice {
                bracket_token: bracketed!(content in input),
                ty: content.parse()?,
            }))
        } else {
            Ok(BaseType::Path(input.parse()?))
        }
    }
}

impl Parse for Path {
    fn parse(input: ParseStream) -> Result<Self> {
        let mut segments = Punctuated::new();
        segments.push_value(input.parse()?);
        while input.peek(Token![::]) {
            segments.push_punct(input.parse()?);
            segments.push_value(input.parse()?);
        }
        Ok(Path { segments })
    }
}

impl Parse for PathSegment {
    fn parse(input: ParseStream) -> Result<Self> {
        let ident =
            if input.peek(Token![Self]) { input.call(Ident::parse_any)? } else { input.parse()? };
        let arguments = if input.peek(Token![<]) && !input.peek(Token![<=]) {
            PathArguments::AngleBracketed(input.parse()?)
        } else {
            PathArguments::None
        };
        Ok(PathSegment { ident, arguments })
    }
}

impl Parse for AngleBracketedGenericArguments {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(AngleBracketedGenericArguments {
            lt_token: input.parse()?,
            args: parse_until(input, GenericArgument::parse, Token![,], Token![>])?,
            gt_token: input.parse()?,
        })
    }
}

impl Parse for GenericArgument {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(GenericArgument::Type(input.parse()?))
    }
}

impl Parse for ExistsParam {
    fn parse(input: ParseStream) -> Result<Self> {
        let ident = input.parse()?;
        let mut colon_token = None;
        let mut sort = None;
        if input.peek(Token![:]) {
            colon_token = Some(input.parse()?);
            sort = Some(input.parse()?);
        }
        Ok(ExistsParam { ident, colon_token, sort })
    }
}

impl Parse for Block {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;
        Ok(Block { brace_token: braced!(content in input), stmts: content.parse()? })
    }
}

fn parse_until<T: Parse, P1: Peek, P2: Peek>(
    input: ParseStream,
    parser: fn(ParseStream) -> Result<T>,
    sep: P1,
    end: P2,
) -> Result<Punctuated<T, P1::Token>>
where
    P1::Token: Parse,
{
    let _ = sep;
    let mut params = Punctuated::new();
    loop {
        if input.peek(end) {
            return Ok(params);
        }
        params.push_value(parser(input)?);
        if input.peek(end) {
            return Ok(params);
        }
        params.push_punct(input.parse()?);
    }
}

fn parse_ident_or_self(input: ParseStream) -> Result<Ident> {
    if input.peek(Token![self]) {
        input.call(Ident::parse_any)
    } else {
        input.parse()
    }
}

mod kw {
    syn::custom_keyword!(strg);
    syn::custom_keyword!(ensures);
    syn::custom_keyword!(requires);
    syn::custom_keyword!(refined);
    syn::custom_keyword!(by);
}

#[derive(Copy, Clone, Eq, PartialEq)]
enum Mode {
    Flux,
    Rust,
}

impl Item {
    fn replace_attrs(&mut self, new: Vec<Attribute>) -> Vec<Attribute> {
        match self {
            Item::Fn(ItemFn { attrs, .. })
            | Item::Impl(ItemImpl { attrs, .. })
            | Item::Enum(syn::ItemEnum { attrs, .. })
            | Item::Struct(ItemStruct { attrs, .. })
            | Item::Use(syn::ItemUse { attrs, .. })
            | Item::Type(ItemType { attrs, .. }) => mem::replace(attrs, new),
        }
    }
}

impl ToTokens for Items {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.append_all(&self.0);
    }
}

impl ToTokens for Item {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            Item::Fn(item_fn) => item_fn.to_tokens(tokens),
            Item::Impl(item_impl) => item_impl.to_tokens(tokens),
            Item::Struct(item_struct) => item_struct.to_tokens(tokens),
            Item::Enum(item_enum) => item_enum.to_tokens(tokens),
            Item::Use(item_use) => item_use.to_tokens(tokens),
            Item::Type(item_type) => item_type.to_tokens(tokens),
        }
    }
}

impl ToTokens for ItemStruct {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        #[cfg(flux_sysroot)]
        {
            let refined_by = &self.refined_by;
            quote! {
                #[flux_tool::refined_by(#refined_by)]
            }
            .to_tokens(tokens);
        }
        tokens.append_all(&self.attrs);
        self.vis.to_tokens(tokens);
        self.struct_token.to_tokens(tokens);
        self.ident.to_tokens(tokens);
        self.generics.to_tokens(tokens);
        self.fields.to_tokens(tokens);
        self.semi_token.to_tokens(tokens);
    }
}

impl ToTokens for RefinedBy {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        for param in self.params.pairs() {
            param.value().to_tokens(tokens);
            param.punct().to_tokens(tokens);
        }
    }
}

impl ToTokens for RefinedByParam {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.ident.to_tokens(tokens);
        self.colon_token.to_tokens(tokens);
        self.sort.to_tokens(tokens);
    }
}

impl ToTokens for Fields {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            Fields::Named(fields) => fields.to_tokens(tokens),
            Fields::Unnamed(fields) => fields.to_tokens(tokens),
            Fields::Unit => {}
        }
    }
}

impl ToTokens for FieldsNamed {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let FieldsNamed { brace_token, named } = self;
        brace_token.surround(tokens, |tokens| {
            named.to_tokens(tokens);
        });
    }
}

impl ToTokens for FieldsUnnamed {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let FieldsUnnamed { paren_token, unnamed } = self;
        paren_token.surround(tokens, |tokens| {
            unnamed.to_tokens(tokens);
        });
    }
}

impl ToTokens for Field {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let Field { attrs, vis, mutability: _, ident, colon_token, ty } = self;
        #[cfg(flux_sysroot)]
        {
            let flux_ty = ToTokensFlux(ty);
            quote! {
                #[flux_tool::field(#flux_ty)]
            }
            .to_tokens(tokens);
        }
        tokens.append_all(attrs);
        vis.to_tokens(tokens);
        ident.to_tokens(tokens);
        colon_token.to_tokens(tokens);
        ty.to_tokens_inner(tokens, Mode::Rust);
    }
}

impl ToTokens for ItemFn {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let ItemFn { attrs, vis, sig, block } = self;
        #[cfg(flux_sysroot)]
        {
            let flux_sig = ToTokensFlux(sig);
            quote!(#[flux_tool::sig(#flux_sig)]).to_tokens(tokens);
        }
        let rust_sig = ToTokensRust(sig);
        quote! {
            #(#attrs)*
            #vis #rust_sig #block
        }
        .to_tokens(tokens);
    }
}

impl ToTokens for ItemType {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let flux_type = ToTokensFlux(self);
        let rust_type = ToTokensRust(self);
        quote! {
            #[flux_tool::alias(#flux_type)]
            #rust_type
        }
        .to_tokens(tokens);
    }
}

impl ToTokens for ToTokensFlux<&ItemType> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.0.to_tokens_inner(tokens, Mode::Flux);
    }
}

impl ToTokens for ToTokensRust<&ItemType> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.0.to_tokens_inner(tokens, Mode::Rust);
    }
}

impl ToTokens for ToTokensFlux<&Type> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.0.to_tokens_inner(tokens, Mode::Flux);
    }
}

impl ItemType {
    fn to_tokens_inner(&self, tokens: &mut TokenStream, mode: Mode) {
        if mode == Mode::Rust {
            tokens.append_all(&self.attrs);
            self.vis.to_tokens(tokens);
        }
        self.type_token.to_tokens(tokens);
        self.ident.to_tokens(tokens);
        self.generics.to_tokens(tokens);
        if let Some(params) = &self.index_params {
            params.to_tokens_inner(tokens, mode);
        }
        self.eq_token.to_tokens(tokens);
        self.ty.to_tokens_inner(tokens, mode);
        if mode == Mode::Rust {
            self.semi_token.to_tokens(tokens);
        }
    }
}

impl IndexParams {
    fn to_tokens_inner(&self, tokens: &mut TokenStream, mode: Mode) {
        if mode == Mode::Flux {
            self.bracket_token.surround(tokens, |tokens| {
                for param in self.params.pairs() {
                    param.value().to_tokens_inner(tokens);
                    param.punct().to_tokens(tokens);
                }
            });
        }
    }
}

impl ToTokens for ItemImpl {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.append_all(&self.attrs);
        self.impl_token.to_tokens(tokens);
        self.generics.to_tokens(tokens);
        if let Some((trait_, for_token)) = &self.trait_ {
            trait_.to_tokens(tokens);
            for_token.to_tokens(tokens);
        }
        self.self_ty.to_tokens(tokens);
        self.brace_token
            .surround(tokens, |tokens| tokens.append_all(&self.items));
    }
}

impl ToTokens for ImplItem {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            ImplItem::Fn(impl_item_fn) => impl_item_fn.to_tokens(tokens),
            ImplItem::Type(impl_item_ty) => impl_item_ty.to_tokens(tokens),
        }
    }
}

impl ToTokens for ImplItemFn {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let ImplItemFn { attrs, vis, sig, block } = self;
        #[cfg(flux_sysroot)]
        {
            let flux_sig = ToTokensFlux(sig);
            quote!(#[flux_tool::sig(#flux_sig)]).to_tokens(tokens);
        }
        let rust_sig = ToTokensRust(sig);
        quote! {
            #(#attrs)*
            #vis #rust_sig #block
        }
        .to_tokens(tokens);
    }
}

struct ToTokensFlux<T>(T);

impl ToTokens for ToTokensFlux<&Signature> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.0.to_tokens_inner(tokens, Mode::Flux);
    }
}

struct ToTokensRust<T>(T);

impl ToTokens for ToTokensRust<&Signature> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.0.to_tokens_inner(tokens, Mode::Rust);
    }
}

impl Signature {
    fn to_tokens_inner(&self, tokens: &mut TokenStream, mode: Mode) {
        self.fn_token.to_tokens(tokens);
        if mode == Mode::Rust {
            self.ident.to_tokens(tokens);
            self.generics.to_tokens(tokens);
        }
        self.paren_token.surround(tokens, |tokens| {
            for fn_arg in self.inputs.pairs() {
                fn_arg.value().to_tokens_inner(tokens, mode);
                fn_arg.punct().to_tokens(tokens);
            }
        });
        self.output.to_tokens_inner(tokens, mode);
        if mode == Mode::Rust {
            self.generics.where_clause.to_tokens(tokens);
        }
        if let Some(requires) = &self.requires {
            requires.to_tokens_inner(tokens, mode);
        }
        if let Some(ensures) = &self.ensures {
            ensures.to_tokens_inner(tokens, mode);
        }
    }
}

impl Requires {
    fn to_tokens_inner(&self, tokens: &mut TokenStream, mode: Mode) {
        if mode == Mode::Flux {
            self.requires_token.to_tokens(tokens);
            self.constraint.to_tokens(tokens);
        }
    }
}

impl Ensures {
    fn to_tokens_inner(&self, tokens: &mut TokenStream, mode: Mode) {
        if mode == Mode::Flux {
            self.ensures_token.to_tokens(tokens);
            for constraint in self.constraints.pairs() {
                constraint.value().to_tokens_inner(tokens);
                constraint.punct().to_tokens(tokens);
            }
        }
    }
}

impl Constraint {
    fn to_tokens_inner(&self, tokens: &mut TokenStream) {
        self.ident.to_tokens(tokens);
        self.colon_token.to_tokens(tokens);
        self.ty.to_tokens_inner(tokens, Mode::Flux);
    }
}

impl FnArg {
    fn to_tokens_inner(&self, tokens: &mut TokenStream, mode: Mode) {
        match self {
            FnArg::StrgRef(strg_ref) => strg_ref.to_tokens_inner(tokens, mode),
            FnArg::Typed(pat_type) => {
                pat_type.to_tokens_inner(tokens, mode);
            }
        }
    }
}

impl StrgRef {
    fn to_tokens_inner(&self, tokens: &mut TokenStream, mode: Mode) {
        self.pat.to_tokens_inner(tokens, mode);
        self.colon_token.to_tokens(tokens);
        self.and_token.to_tokens(tokens);
        match mode {
            Mode::Flux => self.strg_token.to_tokens(tokens),
            Mode::Rust => {
                let span = self.strg_token.span;
                quote_spanned!(span=> mut).to_tokens(tokens);
            }
        }
        self.ty.to_tokens_inner(tokens, mode);
    }
}

impl ReturnType {
    fn to_tokens_inner(&self, tokens: &mut TokenStream, mode: Mode) {
        match self {
            ReturnType::Default => {}
            ReturnType::Type(arrow, ty) => {
                arrow.to_tokens(tokens);
                ty.to_tokens_inner(tokens, mode);
            }
        }
    }
}

impl PatType {
    fn to_tokens_inner(&self, tokens: &mut TokenStream, mode: Mode) {
        self.pat.to_tokens_inner(tokens, mode);
        self.colon_token.to_tokens(tokens);
        self.ty.to_tokens_inner(tokens, mode);
        if mode == Mode::Flux {
            if let Some(pred) = &self.pred {
                pred.to_tokens_inner(tokens);
            }
        }
    }
}

impl Pat {
    fn to_tokens_inner(&self, tokens: &mut TokenStream, mode: Mode) {
        match self {
            Pat::Ident(pat_ident) => pat_ident.to_tokens_inner(tokens, mode),
            Pat::Wild(underscore_token) => {
                underscore_token.to_tokens(tokens);
            }
        }
    }
}

impl PatIdent {
    fn to_tokens_inner(&self, tokens: &mut TokenStream, mode: Mode) {
        if mode == Mode::Rust {
            self.mutability.to_tokens(tokens);
        }
        self.ident.to_tokens(tokens);
    }
}

impl Type {
    fn to_tokens_inner(&self, tokens: &mut TokenStream, mode: Mode) {
        match self {
            Type::Base(bty) => bty.to_tokens_inner(tokens, mode),
            Type::Indexed(ty_indexed) => ty_indexed.to_tokens_inner(tokens, mode),
            Type::Exists(ty_exists) => ty_exists.to_tokens_inner(tokens, mode),
            Type::GeneralExists(ty_general_exists) => {
                ty_general_exists.to_tokens_inner(tokens, mode);
            }
            Type::Reference(ty_reference) => ty_reference.to_tokens_inner(tokens, mode),
            Type::Constraint(ty_constraint) => ty_constraint.to_tokens_inner(tokens, mode),
            Type::Array(ty_array) => ty_array.to_tokens_inner(tokens, mode),
        }
    }
}

impl TypeReference {
    fn to_tokens_inner(&self, tokens: &mut TokenStream, mode: Mode) {
        self.and_token.to_tokens(tokens);
        self.mutability.to_tokens(tokens);
        self.elem.to_tokens_inner(tokens, mode);
    }
}

impl TypeIndexed {
    fn to_tokens_inner(&self, tokens: &mut TokenStream, mode: Mode) {
        self.bty.to_tokens_inner(tokens, mode);
        if mode == Mode::Flux {
            self.bracket_token.surround(tokens, |tokens| {
                self.expr.to_tokens(tokens);
            });
        }
    }
}

impl TypeArray {
    fn to_tokens_inner(&self, tokens: &mut TokenStream, mode: Mode) {
        self.bracket_token.surround(tokens, |tokens| {
            self.ty.to_tokens_inner(tokens, mode);
            self.semi_token.to_tokens(tokens);
            if mode == Mode::Rust {
                self.len.to_tokens(tokens);
            } else {
                quote!(_).to_tokens(tokens);
            }
        });
    }
}

impl TypeConstraint {
    fn to_tokens_inner(&self, tokens: &mut TokenStream, mode: Mode) {
        if mode == Mode::Flux {
            self.brace_token.surround(tokens, |tokens| {
                self.ty.to_tokens_inner(tokens, mode);
                self.or_token.to_tokens(tokens);
                self.pred.to_tokens(tokens);
            });
        } else {
            self.ty.to_tokens_inner(tokens, mode);
        }
    }
}

impl TypeExists {
    fn to_tokens_inner(&self, tokens: &mut TokenStream, mode: Mode) {
        self.bty.to_tokens_inner(tokens, mode);
        if mode == Mode::Flux {
            self.brace_token.surround(tokens, |tokens| {
                self.ident.to_tokens(tokens);
                self.colon_token.to_tokens(tokens);
                self.expr.to_tokens(tokens);
            });
        }
    }
}

impl TypeGeneralExists {
    fn to_tokens_inner(&self, tokens: &mut TokenStream, mode: Mode) {
        self.ty.to_tokens_inner(tokens, mode);
        if mode == Mode::Flux {
            self.brace_token.surround(tokens, |tokens| {
                for fn_arg in self.params.pairs() {
                    fn_arg.value().to_tokens_inner(tokens);
                    fn_arg.punct().to_tokens(tokens);
                }
                self.dot_token.to_tokens(tokens);
                self.ty.to_tokens_inner(tokens, mode);
                self.or_token.to_tokens(tokens);
                self.pred.to_tokens(tokens);
            });
        }
    }
}

impl BaseType {
    fn to_tokens_inner(&self, tokens: &mut TokenStream, mode: Mode) {
        match self {
            BaseType::Path(path) => path.to_tokens_inner(tokens, mode),
            BaseType::Slice(type_slice) => {
                type_slice.to_tokens_inner(tokens, mode);
            }
        }
    }
}

impl TypeSlice {
    fn to_tokens_inner(&self, tokens: &mut TokenStream, mode: Mode) {
        self.bracket_token.surround(tokens, |tokens| {
            self.ty.to_tokens_inner(tokens, mode);
        });
    }
}

impl PatTypePredicate {
    fn to_tokens_inner(&self, tokens: &mut TokenStream) {
        self.brace_token
            .surround(tokens, |tokens| self.pred.to_tokens(tokens));
    }
}

impl ExistsParam {
    fn to_tokens_inner(&self, tokens: &mut TokenStream) {
        self.ident.to_tokens(tokens);
        self.colon_token.to_tokens(tokens);
        self.sort.to_tokens(tokens);
    }
}

impl Path {
    fn to_tokens_inner(&self, tokens: &mut TokenStream, mode: Mode) {
        for segment in self.segments.pairs() {
            segment.value().to_tokens_inner(tokens, mode);
            segment.punct().to_tokens(tokens);
        }
    }
}

impl PathSegment {
    fn to_tokens_inner(&self, tokens: &mut TokenStream, mode: Mode) {
        self.ident.to_tokens(tokens);
        self.arguments.to_tokens_inner(tokens, mode);
    }
}

impl PathArguments {
    fn to_tokens_inner(&self, tokens: &mut TokenStream, mode: Mode) {
        match self {
            PathArguments::None => {}
            PathArguments::AngleBracketed(args) => args.to_tokens_inner(tokens, mode),
        }
    }
}

impl AngleBracketedGenericArguments {
    fn to_tokens_inner(&self, tokens: &mut TokenStream, mode: Mode) {
        self.lt_token.to_tokens(tokens);
        for arg in self.args.pairs() {
            arg.value().to_tokens_inner(tokens, mode);
            arg.punct().to_tokens(tokens);
        }
        self.gt_token.to_tokens(tokens);
    }
}

impl GenericArgument {
    fn to_tokens_inner(&self, tokens: &mut TokenStream, mode: Mode) {
        match self {
            GenericArgument::Type(ty) => ty.to_tokens_inner(tokens, mode),
        }
    }
}

impl ToTokens for Block {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.brace_token
            .surround(tokens, |tokens| self.stmts.to_tokens(tokens));
    }
}
