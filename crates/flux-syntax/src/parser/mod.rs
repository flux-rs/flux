pub(crate) mod lookahead;
mod utils;
use std::{collections::HashSet, str::FromStr, vec};

use lookahead::{AnyLit, LAngle, NonReserved, RAngle};
use rustc_span::sym::Output;
use utils::{
    angle, braces, brackets, delimited, opt_angle, parens, punctuated_until,
    punctuated_with_trailing, repeat_while, sep1, until,
};

use crate::{
    ParseCtxt, ParseError, ParseResult,
    parser::lookahead::{AnyOf, Expected, PeekExpected},
    surface::{
        self, Async,
        Attr::{self},
        BaseSort, BaseTy, BaseTyKind, BinOp, BindKind, ConstArg, ConstArgKind, ConstructorArg,
        DetachedInherentImpl, DetachedItem, DetachedItemKind, DetachedSpecs, DetachedTrait,
        DetachedTraitImpl, Ensures, EnumDef, Expr, ExprKind, ExprPath, ExprPathSegment, FieldExpr,
        FluxItem, FnInput, FnOutput, FnRetTy, FnSig, GenericArg, GenericArgKind, GenericBounds,
        GenericParam, Generics, Ident, ImplAssocReft, Indices, LetDecl, LitKind, Mutability,
        ParamMode, Path, PathSegment, PrimOpProp, Qualifier, QuantKind, RefineArg, RefineParam,
        RefineParams, Requires, Sort, SortDecl, SortPath, SpecFunc, Spread, StructDef,
        TraitAssocReft, TraitRef, Trusted, Ty, TyAlias, TyKind, UnOp, VariantDef, VariantRet,
        WhereBoundPredicate,
    },
    symbols::{kw, sym},
    token::{self, Comma, Delimiter::*, IdentIsRaw, Or, Token, TokenKind},
};

/// An attribute that's considered part of the *syntax* of an item.
///
/// This is in contrast to a [`surface::Attr`] which changes the behavior of an item. For example,
/// a `#[refined_by(...)]` is part of the syntax of an adt: we could think of a different syntax
/// that doesn't use an attribute. The existence of a syntax attribute in the token stream can be
/// used to decide how to keep parsing, for example, if we see a `#[reft]` we know that the next
/// item bust be an associated refinement and not a method inside an impl or trait.
enum SyntaxAttr {
    /// A `#[reft]` attribute
    Reft,
    /// A `#[invariant]` attribute
    Invariant(Expr),
    /// A `#[refined_by(...)]` attribute
    RefinedBy(RefineParams),
    /// A `#[hide]` attribute
    ///
    /// NOTE(nilehmann) This should be considered a normal attribute, but we haven't implemented
    /// attributes for flux items. If we start seeing more of these we should consider implementing
    /// the infrastructure necesary to keep a list of attributes inside the flux item like we do
    /// for rust items.
    Hide,
    /// a `#[opaque]` attribute
    Opaque,
}

#[derive(Default)]
struct ParsedAttrs {
    normal: Vec<Attr>,
    syntax: Vec<SyntaxAttr>,
}

impl ParsedAttrs {
    fn is_reft(&self) -> bool {
        self.syntax
            .iter()
            .any(|attr| matches!(attr, SyntaxAttr::Reft))
    }

    fn is_hide(&self) -> bool {
        self.syntax
            .iter()
            .any(|attr| matches!(attr, SyntaxAttr::Hide))
    }

    fn is_opaque(&self) -> bool {
        self.syntax
            .iter()
            .any(|attr| matches!(attr, SyntaxAttr::Opaque))
    }

    fn refined_by(&mut self) -> Option<RefineParams> {
        let pos = self
            .syntax
            .iter()
            .position(|x| matches!(x, SyntaxAttr::RefinedBy(_)))?;
        if let SyntaxAttr::RefinedBy(params) = self.syntax.remove(pos) {
            Some(params)
        } else {
            None
        }
    }

    fn invariant(&mut self) -> Option<Expr> {
        let pos = self
            .syntax
            .iter()
            .position(|x| matches!(x, SyntaxAttr::Invariant(_)))?;
        if let SyntaxAttr::Invariant(exp) = self.syntax.remove(pos) { Some(exp) } else { None }
    }
}

/// ```text
///   yes ⟨ , reason = ⟨literal⟩ ⟩?
/// | no ⟨ , reason = ⟨literal⟩ ⟩?
/// | reason = ⟨literal⟩
/// ```
pub(crate) fn parse_yes_or_no_with_reason(cx: &mut ParseCtxt) -> ParseResult<bool> {
    let mut lookahead = cx.lookahead1();
    if lookahead.advance_if(sym::yes) {
        if cx.advance_if(token::Comma) {
            parse_reason(cx)?;
        }
        Ok(true)
    } else if lookahead.advance_if(sym::no) {
        if cx.advance_if(token::Comma) {
            parse_reason(cx)?;
        }
        Ok(false)
    } else if lookahead.peek(sym::reason) {
        parse_reason(cx)?;
        Ok(true)
    } else {
        Err(lookahead.into_error())
    }
}

/// ```text
/// ⟨reason⟩ := reason = ⟨literal⟩
/// ```
fn parse_reason(cx: &mut ParseCtxt) -> ParseResult {
    cx.expect(sym::reason)?;
    cx.expect(token::Eq)?;
    cx.expect(AnyLit)
}

/// ```text
/// ⟨ident_list⟩ := ⟨ident⟩,*
/// ```
pub(crate) fn parse_ident_list(cx: &mut ParseCtxt) -> ParseResult<Vec<Ident>> {
    punctuated_until(cx, Comma, token::Eof, parse_ident)
}

/// ```text
/// ⟨flux_items⟩ := ⟨flux_item⟩*
/// ```
pub(crate) fn parse_flux_items(cx: &mut ParseCtxt) -> ParseResult<Vec<FluxItem>> {
    until(cx, token::Eof, parse_flux_item)
}

/// ```text
/// ⟨flux_item⟩ := ⟨func_def⟩
///              | ⟨qualifier⟩
///              | ⟨sort_decl⟩
///              | ⟨primop_prop⟩
/// ```
fn parse_flux_item(cx: &mut ParseCtxt) -> ParseResult<FluxItem> {
    let mut lookahead = cx.lookahead1();
    if lookahead.peek(token::Pound) || lookahead.peek(kw::Fn) {
        parse_reft_func(cx).map(FluxItem::FuncDef)
    } else if lookahead.peek(kw::Local) || lookahead.peek(kw::Qualifier) {
        parse_qualifier(cx).map(FluxItem::Qualifier)
    } else if lookahead.peek(kw::Opaque) {
        parse_sort_decl(cx).map(FluxItem::SortDecl)
    } else if lookahead.peek(kw::Property) {
        parse_primop_property(cx).map(FluxItem::PrimOpProp)
    } else {
        Err(lookahead.into_error())
    }
}

///```text
/// ⟨specs⟩ ::= ⟨specs⟩*
/// ```
pub(crate) fn parse_detached_specs(cx: &mut ParseCtxt) -> ParseResult<surface::DetachedSpecs> {
    let items = until(cx, token::Eof, parse_detached_item)?;
    Ok(surface::DetachedSpecs { items })
}

///```text
/// ⟨specs⟩ ::= ⟨fn-spec⟩
///           | ⟨struct-spec⟩
///           | ⟨enum-spec⟩
///           | ⟨mod⟩
///           | ⟨impl⟩
/// ```
pub(crate) fn parse_detached_item(cx: &mut ParseCtxt) -> ParseResult<DetachedItem> {
    let attrs = parse_attrs(cx)?;
    let mut lookahead = cx.lookahead1();
    if lookahead.peek(kw::Fn) {
        Ok(parse_detached_fn_sig(cx, attrs)?.map_kind(DetachedItemKind::FnSig))
    } else if lookahead.peek(kw::Mod) {
        parse_detached_mod(cx)
    } else if lookahead.peek(kw::Struct) {
        parse_detached_struct(cx, attrs)
    } else if lookahead.peek(kw::Enum) {
        parse_detached_enum(cx, attrs)
    } else if lookahead.peek(kw::Impl) {
        parse_detached_impl(cx, attrs)
    } else if lookahead.peek(kw::Trait) {
        parse_detached_trait(cx, attrs)
    } else {
        Err(lookahead.into_error())
    }
}

///```text
/// ⟨field⟩ ::= ⟨ident⟩ : ⟨type⟩
/// ```
fn parse_detached_field(cx: &mut ParseCtxt) -> ParseResult<(Ident, Ty)> {
    let ident = parse_ident(cx)?;
    cx.expect(token::Colon)?;
    let ty = parse_type(cx)?;
    Ok((ident, ty))
}

///```text
/// ⟨enum⟩ := enum Ident ⟨refine_info⟩ { ⟨variant⟩* }
/// ```
fn parse_detached_enum(cx: &mut ParseCtxt, mut attrs: ParsedAttrs) -> ParseResult<DetachedItem> {
    cx.expect(kw::Enum)?;
    let path = parse_expr_path(cx)?;
    let generics = Some(parse_opt_generics(cx)?);
    let refined_by = attrs.refined_by();
    let invariants = attrs.invariant().into_iter().collect();
    let variants = braces(cx, Comma, |cx| parse_variant(cx, true))?
        .into_iter()
        .map(Some)
        .collect();
    let enum_def = EnumDef { generics, refined_by, variants, invariants, reflected: false };
    Ok(DetachedItem {
        attrs: attrs.normal,
        path,
        kind: DetachedItemKind::Enum(enum_def),
        node_id: cx.next_node_id(),
    })
}

fn parse_detached_struct(cx: &mut ParseCtxt, mut attrs: ParsedAttrs) -> ParseResult<DetachedItem> {
    cx.expect(kw::Struct)?;
    let path = parse_expr_path(cx)?;
    let generics = Some(parse_opt_generics(cx)?);
    let refined_by = attrs.refined_by();
    let opaque = attrs.is_opaque();
    let invariants = attrs.invariant().into_iter().collect();
    let fields = if cx.peek(token::OpenBrace) {
        braces(cx, Comma, parse_detached_field)?
            .into_iter()
            .map(|(_, ty)| Some(ty))
            .collect()
    } else if cx.peek(token::OpenParen) {
        parens(cx, Comma, parse_type)?
            .into_iter()
            .map(Some)
            .collect()
    } else {
        cx.expect(token::Semi)?;
        vec![]
    };
    let struct_def = StructDef { generics, opaque, refined_by, invariants, fields };
    Ok(DetachedItem {
        attrs: attrs.normal,
        path,
        kind: DetachedItemKind::Struct(struct_def),
        node_id: cx.next_node_id(),
    })
}

fn ident_path(cx: &mut ParseCtxt, ident: Ident) -> ExprPath {
    let span = ident.span;
    let segments = vec![ExprPathSegment { ident, node_id: cx.next_node_id() }];
    ExprPath { segments, span, node_id: cx.next_node_id() }
}

fn parse_detached_fn_sig(
    cx: &mut ParseCtxt,
    attrs: ParsedAttrs,
) -> ParseResult<DetachedItem<FnSig>> {
    let fn_sig = parse_fn_sig(cx, token::Semi)?;
    let span = fn_sig.span;
    let ident = fn_sig
        .ident
        .ok_or(ParseError { kind: crate::ParseErrorKind::InvalidDetachedSpec, span })?;
    let path = ident_path(cx, ident);
    Ok(DetachedItem { attrs: attrs.normal, path, kind: fn_sig, node_id: cx.next_node_id() })
}

///```text
/// ⟨mod⟩ ::= mod ⟨ident⟩ { ⟨specs⟩ }
/// ```
fn parse_detached_mod(cx: &mut ParseCtxt) -> ParseResult<DetachedItem> {
    cx.expect(kw::Mod)?;
    let path = parse_expr_path(cx)?;
    cx.expect(TokenKind::open_delim(Brace))?;
    let items = until(cx, TokenKind::close_delim(Brace), parse_detached_item)?;
    cx.expect(TokenKind::close_delim(Brace))?;
    Ok(DetachedItem {
        attrs: vec![],
        path,
        kind: DetachedItemKind::Mod(DetachedSpecs { items }),
        node_id: cx.next_node_id(),
    })
}

///```text
/// ⟨trait-spec⟩ ::= trait Ident { ⟨fn-spec⟩* }
/// ```
fn parse_detached_trait(cx: &mut ParseCtxt, attrs: ParsedAttrs) -> ParseResult<DetachedItem> {
    cx.expect(kw::Trait)?;
    let path = parse_expr_path(cx)?;
    let _generics = parse_opt_generics(cx)?;
    cx.expect(TokenKind::open_delim(Brace))?;

    let mut items = vec![];
    let mut refts = vec![];
    while !cx.peek(TokenKind::close_delim(Brace)) {
        let assoc_item_attrs = parse_attrs(cx)?;
        if assoc_item_attrs.is_reft() {
            refts.push(parse_trait_assoc_reft(cx)?);
        } else {
            items.push(parse_detached_fn_sig(cx, assoc_item_attrs)?);
        }
    }
    cx.expect(TokenKind::close_delim(Brace))?;
    Ok(DetachedItem {
        attrs: attrs.normal,
        path,
        kind: DetachedItemKind::Trait(DetachedTrait { items, refts }),
        node_id: cx.next_node_id(),
    })
}

///```text
/// ⟨impl-spec⟩ ::= impl Ident (for Ident)? { ⟨#[assoc] impl_assoc_reft⟩* ⟨fn-spec⟩* }
/// ```
fn parse_detached_impl(cx: &mut ParseCtxt, attrs: ParsedAttrs) -> ParseResult<DetachedItem> {
    let lo = cx.lo();
    cx.expect(kw::Impl)?;
    let hi = cx.hi();
    let span = cx.mk_span(lo, hi);
    let outer_path = parse_expr_path(cx)?;
    let _generics = parse_opt_generics(cx)?;
    let inner_path = if cx.advance_if(kw::For) {
        let path = parse_expr_path(cx)?;
        let _generics = parse_opt_generics(cx)?;
        Some(path)
    } else {
        None
    };
    cx.expect(TokenKind::open_delim(Brace))?;

    let mut items = vec![];
    let mut refts = vec![];
    while !cx.peek(TokenKind::close_delim(Brace)) {
        // if inner_path.is_none, we are parsing an inherent impl with no associated-refts
        let assoc_item_attrs = parse_attrs(cx)?;
        if assoc_item_attrs.is_reft() && inner_path.is_some() {
            refts.push(parse_impl_assoc_reft(cx)?);
        } else {
            items.push(parse_detached_fn_sig(cx, assoc_item_attrs)?);
        }
    }
    cx.expect(TokenKind::close_delim(Brace))?;
    if let Some(path) = inner_path {
        Ok(DetachedItem {
            attrs: attrs.normal,
            path,
            kind: DetachedItemKind::TraitImpl(DetachedTraitImpl {
                trait_: outer_path,
                items,
                refts,
                span,
            }),
            node_id: cx.next_node_id(),
        })
    } else {
        Ok(DetachedItem {
            attrs: attrs.normal,
            path: outer_path,
            kind: DetachedItemKind::InherentImpl(DetachedInherentImpl { items, span }),
            node_id: cx.next_node_id(),
        })
    }
}

fn parse_attr(cx: &mut ParseCtxt, attrs: &mut ParsedAttrs) -> ParseResult {
    cx.expect(token::Pound)?;
    cx.expect(token::OpenBracket)?;
    let mut lookahead = cx.lookahead1();
    if lookahead.advance_if(kw::Trusted) {
        if cx.advance_if(token::OpenParen) {
            parse_reason(cx)?;
            cx.expect(token::CloseParen)?;
        }
        attrs.normal.push(Attr::Trusted(Trusted::Yes));
    } else if lookahead.advance_if(sym::hide) {
        attrs.syntax.push(SyntaxAttr::Hide);
    } else if lookahead.advance_if(kw::Opaque) {
        attrs.syntax.push(SyntaxAttr::Opaque);
    } else if lookahead.advance_if(kw::Reft) {
        attrs.syntax.push(SyntaxAttr::Reft);
    } else if lookahead.advance_if(kw::RefinedBy) {
        attrs
            .syntax
            .push(SyntaxAttr::RefinedBy(delimited(cx, Parenthesis, parse_refined_by)?));
    } else if lookahead.advance_if(kw::Invariant) {
        attrs
            .syntax
            .push(SyntaxAttr::Invariant(delimited(cx, Parenthesis, |cx| parse_expr(cx, true))?));
    } else {
        return Err(lookahead.into_error());
    };
    cx.expect(token::CloseBracket)
}

fn parse_attrs(cx: &mut ParseCtxt) -> ParseResult<ParsedAttrs> {
    let mut attrs = ParsedAttrs::default();
    repeat_while(cx, token::Pound, |cx| parse_attr(cx, &mut attrs))?;
    Ok(attrs)
}

/// ```text
/// ⟨func_def⟩ := ⟨ # [ hide ] ⟩?
///               fn ⟨ident⟩ ⟨ < ⟨ident⟩,* > ⟩?
///               ( ⟨refine_param⟩,* )
///               ->
///               ⟨sort⟩
/// ```
fn parse_reft_func(cx: &mut ParseCtxt) -> ParseResult<SpecFunc> {
    let attrs = parse_attrs(cx)?;
    let hide = attrs.is_hide();
    cx.expect(kw::Fn)?;
    let name = parse_ident(cx)?;
    let sort_vars = opt_angle(cx, Comma, parse_ident)?;
    let params = parens(cx, Comma, |cx| parse_refine_param(cx, RequireSort::Yes))?;
    cx.expect(token::RArrow)?;
    let output = parse_sort(cx)?;
    let body = if cx.peek(token::OpenBrace) {
        Some(parse_block(cx)?)
    } else {
        cx.expect(token::Semi)?;
        None
    };
    Ok(SpecFunc { name, sort_vars, params, output, body, hide })
}

/// ```text
/// ⟨qualifier⟩ :=  ⟨ local ⟩?
///                 qualifier ⟨ident⟩ ( ⟨refine_param⟩,* )
///                 ⟨block⟩
/// ```
fn parse_qualifier(cx: &mut ParseCtxt) -> ParseResult<Qualifier> {
    let lo = cx.lo();
    let local = cx.advance_if(kw::Local);
    cx.expect(kw::Qualifier)?;
    let name = parse_ident(cx)?;
    let params = parens(cx, Comma, |cx| parse_refine_param(cx, RequireSort::Yes))?;
    let expr = parse_block(cx)?;
    let hi = cx.hi();
    Ok(Qualifier { global: !local, name, params, expr, span: cx.mk_span(lo, hi) })
}

/// ```text
/// ⟨sort_decl⟩ := opaque sort ⟨ident⟩ ;
/// ```
fn parse_sort_decl(cx: &mut ParseCtxt) -> ParseResult<SortDecl> {
    cx.expect(kw::Opaque)?;
    cx.expect(kw::Sort)?;
    let name = parse_ident(cx)?;
    let sort_vars = opt_angle(cx, Comma, parse_ident)?;
    cx.expect(token::Semi)?;
    Ok(SortDecl { name, sort_vars })
}

/// `⟨bin_op⟩ := ⟨ a binary operator ⟩
fn parse_binop(cx: &mut ParseCtxt) -> ParseResult<BinOp> {
    let (op, ntokens) = cx
        .peek_binop()
        .ok_or_else(|| cx.unexpected_token(vec![Expected::Str("binary operator")]))?;
    cx.advance_by(ntokens);
    Ok(op)
}

/// ```text
/// ⟨primop_prop⟩ := property ⟨ident⟩ [ ⟨bin_op⟩ ] ( ⟨refine_param⟩,* ) ⟨block⟩
/// ```
fn parse_primop_property(cx: &mut ParseCtxt) -> ParseResult<PrimOpProp> {
    let lo = cx.lo();
    cx.expect(kw::Property)?;

    // Parse the name
    let name = parse_ident(cx)?;

    // Parse the operator
    cx.expect(token::OpenBracket)?;
    let op = parse_binop(cx)?;
    cx.expect(token::CloseBracket)?;

    // Parse the args
    let params = parens(cx, Comma, |cx| parse_refine_param(cx, RequireSort::No))?;

    let body = parse_block(cx)?;
    let hi = cx.hi();

    Ok(PrimOpProp { name, op, params, body, span: cx.mk_span(lo, hi) })
}

pub(crate) fn parse_trait_assoc_refts(cx: &mut ParseCtxt) -> ParseResult<Vec<TraitAssocReft>> {
    until(cx, token::Eof, parse_trait_assoc_reft)
}

/// ```text
/// ⟨trait_assoc_reft⟩ := fn ⟨ident⟩ ( ⟨refine_param⟩,* ) -> ⟨base_sort⟩ ;?
///                     | fn ⟨ident⟩ ( ⟨refine_param⟩,* ) -> ⟨base_sort⟩ ⟨block⟩
///                     | final fn ⟨ident⟩ ( ⟨refine_param⟩,* ) -> ⟨base_sort⟩ ⟨block⟩
/// ```
fn parse_trait_assoc_reft(cx: &mut ParseCtxt) -> ParseResult<TraitAssocReft> {
    let lo = cx.lo();
    let final_ = cx.advance_if(kw::Final);
    cx.expect(kw::Fn)?;
    let name = parse_ident(cx)?;
    let params = parens(cx, Comma, |cx| parse_refine_param(cx, RequireSort::Yes))?;
    cx.expect(token::RArrow)?;
    let output = parse_base_sort(cx)?;
    let body = if cx.peek(token::OpenBrace) {
        Some(parse_block(cx)?)
    } else {
        cx.advance_if(token::Semi);
        None
    };
    let hi = cx.hi();
    Ok(TraitAssocReft { name, params, output, body, span: cx.mk_span(lo, hi), final_ })
}

pub(crate) fn parse_impl_assoc_refts(cx: &mut ParseCtxt) -> ParseResult<Vec<ImplAssocReft>> {
    until(cx, token::Eof, parse_impl_assoc_reft)
}

/// ```text
/// ⟨impl_assoc_reft⟩ := fn ⟨ident⟩ ( ⟨refine_param⟩,* ) -> ⟨base_sort⟩ ⟨block⟩
/// ```
fn parse_impl_assoc_reft(cx: &mut ParseCtxt) -> ParseResult<ImplAssocReft> {
    let lo = cx.lo();
    cx.expect(kw::Fn)?;
    let name = parse_ident(cx)?;
    let params = parens(cx, Comma, |cx| parse_refine_param(cx, RequireSort::Yes))?;
    cx.expect(token::RArrow)?;
    let output = parse_base_sort(cx)?;
    let body = parse_block(cx)?;
    let hi = cx.hi();
    Ok(ImplAssocReft { name, params, output, body, span: cx.mk_span(lo, hi) })
}

/// ```text
/// ⟨refined_by⟩ := ⟨refine_param⟩,*
/// ```
pub(crate) fn parse_refined_by(cx: &mut ParseCtxt) -> ParseResult<RefineParams> {
    punctuated_until(cx, Comma, token::Eof, |cx| parse_refine_param(cx, RequireSort::Yes))
}

/// ```text
/// ⟨variant⟩ := ⟨fields⟩ -> ⟨variant_ret⟩
///            | ⟨fields⟩
///            | ⟨variant_ret⟩
/// ```
pub(crate) fn parse_variant(cx: &mut ParseCtxt, ret_arrow: bool) -> ParseResult<VariantDef> {
    let lo = cx.lo();
    let mut fields = vec![];
    let mut ret = None;
    let ident = if ret_arrow || cx.peek2(NonReserved, token::OpenParen) {
        Some(parse_ident(cx)?)
    } else {
        None
    };
    if cx.peek(token::OpenParen) || cx.peek(token::OpenBrace) {
        fields = parse_fields(cx)?;
        if cx.advance_if(token::RArrow) {
            ret = Some(parse_variant_ret(cx)?);
        }
    } else {
        if ret_arrow {
            cx.expect(token::RArrow)?;
        }
        ret = Some(parse_variant_ret(cx)?);
    };
    let hi = cx.hi();
    Ok(VariantDef { ident, fields, ret, node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) })
}

/// ```text
/// ⟨fields⟩ := ( ⟨ty⟩,* ) | { ⟨ty⟩,* }
/// ```
fn parse_fields(cx: &mut ParseCtxt) -> ParseResult<Vec<Ty>> {
    let mut lookahead = cx.lookahead1();
    if lookahead.peek(token::OpenParen) {
        parens(cx, Comma, parse_type)
    } else if lookahead.peek(token::OpenBrace) {
        braces(cx, Comma, parse_type)
    } else {
        Err(lookahead.into_error())
    }
}

/// ```text
/// ⟨variant_ret⟩ := ⟨path⟩ ⟨ [ ⟨refine_arg⟩,? ] ⟩?
/// ```
fn parse_variant_ret(cx: &mut ParseCtxt) -> ParseResult<VariantRet> {
    let path = parse_path(cx)?;
    let indices = if cx.peek(token::OpenBracket) {
        parse_indices(cx)?
    } else {
        let hi = cx.hi();
        Indices { indices: vec![], span: cx.mk_span(hi, hi) }
    };
    Ok(VariantRet { path, indices })
}

pub(crate) fn parse_type_alias(cx: &mut ParseCtxt) -> ParseResult<TyAlias> {
    let lo = cx.lo();
    cx.expect(kw::Type)?;
    let ident = parse_ident(cx)?;
    let generics = parse_opt_generics(cx)?;
    let params = if cx.peek(token::OpenParen) {
        parens(cx, Comma, |cx| parse_refine_param(cx, RequireSort::Yes))?
    } else {
        vec![]
    };
    let index = if cx.peek(token::OpenBracket) {
        Some(delimited(cx, Bracket, |cx| parse_refine_param(cx, RequireSort::Yes))?)
    } else {
        None
    };
    cx.expect(token::Eq)?;
    let ty = parse_type(cx)?;
    let hi = cx.hi();
    Ok(TyAlias {
        ident,
        generics,
        params,
        index,
        ty,
        node_id: cx.next_node_id(),
        span: cx.mk_span(lo, hi),
    })
}

fn parse_opt_generics(cx: &mut ParseCtxt) -> ParseResult<Generics> {
    if !cx.peek(LAngle) {
        let hi = cx.hi();
        return Ok(Generics { params: vec![], predicates: None, span: cx.mk_span(hi, hi) });
    }
    let lo = cx.lo();
    let params = angle(cx, Comma, parse_generic_param)?;
    let hi = cx.hi();
    Ok(Generics { params, predicates: None, span: cx.mk_span(lo, hi) })
}

fn parse_generic_param(cx: &mut ParseCtxt) -> ParseResult<GenericParam> {
    let name = parse_ident(cx)?;
    Ok(GenericParam { name, node_id: cx.next_node_id() })
}

fn invalid_ident_err(ident: &Ident) -> ParseError {
    ParseError { kind: crate::ParseErrorKind::InvalidBinding, span: ident.span }
}

fn mut_as_strg(inputs: Vec<FnInput>, ensures: &[Ensures]) -> ParseResult<Vec<FnInput>> {
    // 1. Gather ensures
    let locs = ensures
        .iter()
        .filter_map(|ens| if let Ensures::Type(ident, _, _) = ens { Some(ident) } else { None })
        .collect::<HashSet<_>>();
    // 2. Walk over inputs and transform references mentioned in ensures
    let mut res = vec![];
    for input in inputs {
        if let FnInput::Ty(Some(ident), _, _) = &input
            && locs.contains(&ident)
        {
            // a known location: better be a mut or else, error!
            let FnInput::Ty(Some(ident), ty, id) = input else {
                return Err(invalid_ident_err(ident));
            };
            let TyKind::Ref(Mutability::Mut, inner_ty) = ty.kind else {
                return Err(invalid_ident_err(&ident));
            };
            res.push(FnInput::StrgRef(ident, *inner_ty, id));
        } else {
            // not a known location, leave unchanged
            res.push(input);
        }
    }
    Ok(res)
}

/// ```text
/// ⟨fn_sig⟩ := ⟨asyncness⟩ fn ⟨ident⟩?
///             ⟨ [ ⟨refine_param⟩,* ] ⟩?
///             ( ⟨fn_inputs⟩,* )
///             ⟨-> ⟨ty⟩⟩?
///             ⟨requires⟩ ⟨ensures⟩ ⟨where⟩
/// ```
pub(crate) fn parse_fn_sig<T: PeekExpected>(cx: &mut ParseCtxt, end: T) -> ParseResult<FnSig> {
    let lo = cx.lo();
    let asyncness = parse_asyncness(cx);
    cx.expect(kw::Fn)?;
    let ident = if cx.peek(NonReserved) { Some(parse_ident(cx)?) } else { None };
    let mut generics = parse_opt_generics(cx)?;
    let params = if cx.peek(token::OpenBracket) {
        brackets(cx, Comma, |cx| parse_refine_param(cx, RequireSort::Maybe))?
    } else {
        vec![]
    };
    let inputs = parens(cx, Comma, parse_fn_input)?;
    let returns = parse_fn_ret(cx)?;
    let requires = parse_opt_requires(cx)?;
    let ensures = parse_opt_ensures(cx)?;
    let inputs = mut_as_strg(inputs, &ensures)?;
    generics.predicates = parse_opt_where(cx)?;
    cx.expect(end)?;
    let hi = cx.hi();
    Ok(FnSig {
        asyncness,
        generics,
        params,
        ident,
        inputs,
        requires,
        output: FnOutput { returns, ensures, node_id: cx.next_node_id() },
        node_id: cx.next_node_id(),
        span: cx.mk_span(lo, hi),
    })
}

/// ```text
/// ⟨requires⟩ := ⟨ requires ⟨requires_clause⟩,* ⟩?
/// ```
fn parse_opt_requires(cx: &mut ParseCtxt) -> ParseResult<Vec<Requires>> {
    if !cx.advance_if(kw::Requires) {
        return Ok(vec![]);
    }
    punctuated_until(
        cx,
        Comma,
        |t: TokenKind| t.is_keyword(kw::Ensures) || t.is_keyword(kw::Where) || t.is_eof(),
        parse_requires_clause,
    )
}

/// ```text
/// ⟨requires_clause⟩ := ⟨ forall ⟨refine_param⟩,+ . ⟩? ⟨expr⟩
/// ```
fn parse_requires_clause(cx: &mut ParseCtxt) -> ParseResult<Requires> {
    let mut params = vec![];
    if cx.advance_if(kw::Forall) {
        params = sep1(cx, Comma, |cx| parse_refine_param(cx, RequireSort::Maybe))?;
        cx.expect(token::Dot)?;
    }
    let pred = parse_expr(cx, true)?;
    Ok(Requires { params, pred })
}

/// ```text
/// ⟨ensures⟩ := ⟨ensures ⟨ensures_clause⟩,*⟩?
/// ```
fn parse_opt_ensures(cx: &mut ParseCtxt) -> ParseResult<Vec<Ensures>> {
    if !cx.advance_if(kw::Ensures) {
        return Ok(vec![]);
    }
    punctuated_until(
        cx,
        Comma,
        |t: TokenKind| t.is_keyword(kw::Where) || t.is_eof(),
        parse_ensures_clause,
    )
}

/// ```text
/// ⟨ensures_clause⟩ :=  ⟨ident⟩ : ⟨ty⟩
///                   |  ⟨expr⟩
/// ```
fn parse_ensures_clause(cx: &mut ParseCtxt) -> ParseResult<Ensures> {
    if cx.peek2(NonReserved, token::Colon) {
        // ⟨ident⟩ : ⟨ty⟩
        let ident = parse_ident(cx)?;
        cx.expect(token::Colon)?;
        let ty = parse_type(cx)?;
        Ok(Ensures::Type(ident, ty, cx.next_node_id()))
    } else {
        // ⟨expr⟩
        Ok(Ensures::Pred(parse_expr(cx, true)?))
    }
}

fn parse_opt_where(cx: &mut ParseCtxt) -> ParseResult<Option<Vec<WhereBoundPredicate>>> {
    if !cx.advance_if(kw::Where) {
        return Ok(None);
    }
    Ok(Some(punctuated_until(cx, Comma, token::Eof, parse_where_bound)?))
}

fn parse_where_bound(cx: &mut ParseCtxt) -> ParseResult<WhereBoundPredicate> {
    let lo = cx.lo();
    let bounded_ty = parse_type(cx)?;
    cx.expect(token::Colon)?;
    let bounds = parse_generic_bounds(cx)?;
    let hi = cx.hi();
    Ok(WhereBoundPredicate { span: cx.mk_span(lo, hi), bounded_ty, bounds })
}

/// ```text
/// ⟨fn_ret⟩ := ⟨ -> ⟨ty⟩ ⟩?
/// ```
fn parse_fn_ret(cx: &mut ParseCtxt) -> ParseResult<FnRetTy> {
    if cx.advance_if(token::RArrow) {
        Ok(FnRetTy::Ty(Box::new(parse_type(cx)?)))
    } else {
        let hi = cx.hi();
        Ok(FnRetTy::Default(cx.mk_span(hi, hi)))
    }
}

/// ```text
/// ⟨fn_input⟩ := ⟨ident⟩ : &strg ⟨ty⟩
///             | ⟨ident⟩ : ⟨path⟩ { ⟨expr⟩ }
///             | ⟨ident⟩ : ⟨ty⟩
///             | ⟨ty⟩
/// ```
fn parse_fn_input(cx: &mut ParseCtxt) -> ParseResult<FnInput> {
    if cx.peek2(NonReserved, token::Colon) {
        let bind = parse_ident(cx)?;
        cx.expect(token::Colon)?;
        if cx.advance_if2(token::And, kw::Strg) {
            // ⟨ident⟩ : &strg ⟨ty⟩
            Ok(FnInput::StrgRef(bind, parse_type(cx)?, cx.next_node_id()))
        } else if cx.peek(NonReserved) {
            let path = parse_path(cx)?;
            if cx.peek3(token::OpenBrace, NonReserved, token::Colon) {
                // ⟨ident⟩ : ⟨path⟩ { ⟨ident⟩ : ⟨expr⟩ }
                let bty = path_to_bty(path);
                let ty = parse_bty_exists(cx, bty)?;
                Ok(FnInput::Ty(Some(bind), ty, cx.next_node_id()))
            } else if cx.peek(token::OpenBrace) {
                // ⟨ident⟩ : ⟨path⟩ { ⟨expr⟩ }
                let pred = delimited(cx, Brace, |cx| parse_expr(cx, true))?;
                Ok(FnInput::Constr(bind, path, pred, cx.next_node_id()))
            } else {
                // ⟨ident⟩ : ⟨ty⟩
                let bty = path_to_bty(path);
                let ty = parse_bty_rhs(cx, bty)?;
                Ok(FnInput::Ty(Some(bind), ty, cx.next_node_id()))
            }
        } else {
            // ⟨ident⟩ : ⟨ty⟩
            Ok(FnInput::Ty(Some(bind), parse_type(cx)?, cx.next_node_id()))
        }
    } else {
        // ⟨ty⟩
        Ok(FnInput::Ty(None, parse_type(cx)?, cx.next_node_id()))
    }
}

/// ```text
/// ⟨asyncness⟩ := async?
/// ```
fn parse_asyncness(cx: &mut ParseCtxt) -> Async {
    let lo = cx.lo();
    if cx.advance_if(kw::Async) {
        Async::Yes { node_id: cx.next_node_id(), span: cx.mk_span(lo, cx.hi()) }
    } else {
        Async::No
    }
}

/// ```text
/// ⟨ty⟩ := _
///       | { ⟨ident⟩ ⟨,⟨ident⟩⟩* . ⟨ty⟩ | ⟨block_expr⟩ }
///       | ( ⟨ty⟩,* )
///       | { ⟨ty⟩ | ⟨block_expr⟩ }
///       | { ⟨refine_param⟩ ⟨,⟨refine_param⟩⟩* . ⟨ty⟩ | ⟨block_expr⟩ }
///       | & mut? ⟨ty⟩
///       | [ ⟨ty⟩ ; ⟨const_arg⟩ ]
///       | impl ⟨path⟩
///       | ⟨bty⟩
///       | ⟨bty⟩ [ ⟨refine_arg⟩,* ]
///       | ⟨bty⟩ { ⟨ident⟩ : ⟨block_expr⟩ }
///
/// ⟨bty⟩ := ⟨path⟩ | ⟨qpath⟩ | [ ⟨ty⟩ ]
/// ```
pub(crate) fn parse_type(cx: &mut ParseCtxt) -> ParseResult<Ty> {
    let lo = cx.lo();
    let mut lookahead = cx.lookahead1();
    let kind = if lookahead.advance_if(kw::Underscore) {
        TyKind::Hole
    } else if lookahead.advance_if(token::OpenParen) {
        // ( ⟨ty⟩,* )
        let (mut tys, trailing) =
            punctuated_with_trailing(cx, Comma, token::CloseParen, parse_type)?;
        cx.expect(token::CloseParen)?;
        if tys.len() == 1 && !trailing {
            return Ok(tys.remove(0));
        } else {
            TyKind::Tuple(tys)
        }
    } else if lookahead.peek(token::OpenBrace) {
        delimited(cx, Brace, |cx| {
            if cx.peek2(NonReserved, AnyOf([token::Comma, token::Dot, token::Colon])) {
                // { ⟨refine_param⟩ ⟨,⟨refine_param⟩⟩* . ⟨ty⟩ | ⟨block_expr⟩ }
                parse_general_exists(cx)
            } else {
                // { ⟨ty⟩ | ⟨block_expr⟩ }
                let ty = parse_type(cx)?;
                cx.expect(token::Or)?;
                let pred = parse_block_expr(cx)?;
                Ok(TyKind::Constr(pred, Box::new(ty)))
            }
        })?
    } else if lookahead.advance_if(token::And) {
        //  & mut? ⟨ty⟩
        let mutbl = if cx.advance_if(kw::Mut) { Mutability::Mut } else { Mutability::Not };
        TyKind::Ref(mutbl, Box::new(parse_type(cx)?))
    } else if lookahead.advance_if(token::OpenBracket) {
        let ty = parse_type(cx)?;
        if cx.advance_if(token::Semi) {
            // [ ⟨ty⟩ ; ⟨const_arg⟩ ]
            let len = parse_const_arg(cx)?;
            cx.expect(token::CloseBracket)?;
            TyKind::Array(Box::new(ty), len)
        } else {
            // [ ⟨ty⟩ ] ...
            cx.expect(token::CloseBracket)?;
            let span = cx.mk_span(lo, cx.hi());
            let kind = BaseTyKind::Slice(Box::new(ty));
            return parse_bty_rhs(cx, BaseTy { kind, span });
        }
    } else if lookahead.advance_if(kw::Impl) {
        // impl ⟨bounds⟩
        TyKind::ImplTrait(cx.next_node_id(), parse_generic_bounds(cx)?)
    } else if lookahead.peek(NonReserved) {
        // ⟨path⟩ ...
        let path = parse_path(cx)?;
        let bty = path_to_bty(path);
        return parse_bty_rhs(cx, bty);
    } else if lookahead.peek(LAngle) {
        // ⟨qpath⟩ ...
        let bty = parse_qpath(cx)?;
        return parse_bty_rhs(cx, bty);
    } else {
        return Err(lookahead.into_error());
    };
    let hi = cx.hi();
    Ok(Ty { kind, node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) })
}

/// ```text
/// ⟨qpath⟩ := < ⟨ty⟩ as ⟨segments⟩> :: ⟨segments⟩
/// ```
fn parse_qpath(cx: &mut ParseCtxt) -> ParseResult<BaseTy> {
    let lo = cx.lo();
    cx.expect(LAngle)?;
    let qself = parse_type(cx)?;
    cx.expect(kw::As)?;
    let mut segments = parse_segments(cx)?;
    cx.expect(RAngle)?;
    cx.expect(token::PathSep)?;
    segments.extend(parse_segments(cx)?);
    let hi = cx.hi();

    let span = cx.mk_span(lo, hi);
    let path = Path { segments, refine: vec![], node_id: cx.next_node_id(), span };
    let kind = BaseTyKind::Path(Some(Box::new(qself)), path);
    Ok(BaseTy { kind, span })
}

/// ```text
/// { ⟨refine_param⟩ ⟨,⟨refine_param⟩⟩* . ⟨ty⟩ | ⟨block_expr⟩ }
/// ```
fn parse_general_exists(cx: &mut ParseCtxt) -> ParseResult<TyKind> {
    let params = sep1(cx, Comma, |cx| parse_refine_param(cx, RequireSort::Maybe))?;
    cx.expect(token::Dot)?;
    let ty = parse_type(cx)?;
    let pred = if cx.advance_if(token::Or) { Some(parse_block_expr(cx)?) } else { None };
    Ok(TyKind::GeneralExists { params, ty: Box::new(ty), pred })
}

/// ```text
///    ⟨bty⟩ [ ⟨refine_arg⟩,* ]
/// |  ⟨bty⟩ { ⟨ident⟩ : ⟨block_expr⟩ }
/// |  ⟨bty⟩
/// ```
fn parse_bty_rhs(cx: &mut ParseCtxt, bty: BaseTy) -> ParseResult<Ty> {
    let lo = bty.span.lo();
    if cx.peek(token::OpenBracket) {
        // ⟨bty⟩ [ ⟨refine_arg⟩,* ]
        let indices = parse_indices(cx)?;
        let hi = cx.hi();
        let kind = TyKind::Indexed { bty, indices };
        Ok(Ty { kind, node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) })
    } else if cx.peek(token::OpenBrace) {
        // ⟨bty⟩ { ⟨ident⟩ : ⟨block_expr⟩ }
        parse_bty_exists(cx, bty)
    } else {
        // ⟨bty⟩
        let hi = cx.hi();
        let kind = TyKind::Base(bty);
        Ok(Ty { kind, node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) })
    }
}

/// ```text
/// ⟨bty⟩ { ⟨ident⟩ : ⟨block_expr⟩ }
/// ```
fn parse_bty_exists(cx: &mut ParseCtxt, bty: BaseTy) -> ParseResult<Ty> {
    let lo = bty.span.lo();
    delimited(cx, Brace, |cx| {
        let bind = parse_ident(cx)?;
        cx.expect(token::Colon)?;
        let pred = parse_block_expr(cx)?;
        let hi = cx.hi();
        let kind = TyKind::Exists { bind, bty, pred };
        Ok(Ty { kind, node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) })
    })
}

fn path_to_bty(path: Path) -> BaseTy {
    let span = path.span;
    BaseTy { kind: BaseTyKind::Path(None, path), span }
}

fn parse_indices(cx: &mut ParseCtxt) -> ParseResult<Indices> {
    let lo = cx.lo();
    let indices = brackets(cx, Comma, parse_refine_arg)?;
    let hi = cx.hi();
    Ok(Indices { indices, span: cx.mk_span(lo, hi) })
}

fn parse_fn_bound_input(cx: &mut ParseCtxt) -> ParseResult<GenericArg> {
    let lo = cx.lo();
    let tys = parens(cx, Comma, parse_type)?;
    let hi = cx.hi();
    let kind = TyKind::Tuple(tys);
    let span = cx.mk_span(lo, hi);
    let in_ty = Ty { kind, node_id: cx.next_node_id(), span };
    Ok(GenericArg { kind: GenericArgKind::Type(in_ty), node_id: cx.next_node_id() })
}

fn parse_fn_bound_output(cx: &mut ParseCtxt) -> ParseResult<GenericArg> {
    let lo = cx.lo();

    let ty = if cx.advance_if(token::RArrow) {
        parse_type(cx)?
    } else {
        Ty { kind: TyKind::Tuple(vec![]), node_id: cx.next_node_id(), span: cx.mk_span(lo, lo) }
    };
    let hi = cx.hi();
    let ident = Ident { name: Output, span: cx.mk_span(lo, hi) };
    Ok(GenericArg { kind: GenericArgKind::Constraint(ident, ty), node_id: cx.next_node_id() })
}

fn parse_fn_bound_path(cx: &mut ParseCtxt) -> ParseResult<Path> {
    let lo = cx.lo();
    let ident = parse_ident(cx)?;
    let in_arg = parse_fn_bound_input(cx)?;
    let out_arg = parse_fn_bound_output(cx)?;
    let args = vec![in_arg, out_arg];
    let segment = PathSegment { ident, args, node_id: cx.next_node_id() };
    let hi = cx.hi();
    Ok(Path {
        segments: vec![segment],
        refine: vec![],
        node_id: cx.next_node_id(),
        span: cx.mk_span(lo, hi),
    })
}

fn parse_generic_bounds(cx: &mut ParseCtxt) -> ParseResult<GenericBounds> {
    let path = if cx.peek(sym::FnOnce) || cx.peek(sym::FnMut) || cx.peek(sym::Fn) {
        parse_fn_bound_path(cx)?
    } else {
        parse_path(cx)?
    };
    Ok(vec![TraitRef { path, node_id: cx.next_node_id() }])
}

fn parse_const_arg(cx: &mut ParseCtxt) -> ParseResult<ConstArg> {
    let lo = cx.lo();
    let mut lookahead = cx.lookahead1();
    let kind = if lookahead.peek(AnyLit) {
        let len = parse_int(cx)?;
        ConstArgKind::Lit(len)
    } else if lookahead.advance_if(kw::Underscore) {
        ConstArgKind::Infer
    } else {
        return Err(lookahead.into_error());
    };
    let hi = cx.hi();
    Ok(ConstArg { kind, span: cx.mk_span(lo, hi) })
}

/// ```text
/// ⟨path⟩ := ⟨segments⟩ ⟨ ( ⟨refine_arg⟩,* ) ⟩?
/// ```
fn parse_path(cx: &mut ParseCtxt) -> ParseResult<Path> {
    let lo = cx.lo();
    let segments = parse_segments(cx)?;
    let refine =
        if cx.peek(token::OpenParen) { parens(cx, Comma, parse_refine_arg)? } else { vec![] };
    let hi = cx.hi();
    Ok(Path { segments, refine, node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) })
}

/// ```text
/// ⟨segments⟩ := ⟨segment⟩ ⟨:: ⟨segment⟩ ⟩*
/// ```
fn parse_segments(cx: &mut ParseCtxt) -> ParseResult<Vec<PathSegment>> {
    sep1(cx, token::PathSep, parse_segment)
}

/// ```text
/// ⟨segment⟩ := ⟨ident⟩ ⟨ < ⟨generic_arg⟩,* > ⟩?
/// ```
fn parse_segment(cx: &mut ParseCtxt) -> ParseResult<PathSegment> {
    let ident = parse_ident(cx)?;
    let args = opt_angle(cx, Comma, parse_generic_arg)?;
    Ok(PathSegment { ident, node_id: cx.next_node_id(), args })
}

/// ```text
/// ⟨generic_arg⟩ := ⟨ty⟩ | ⟨ident⟩ = ⟨ty⟩
/// ```
fn parse_generic_arg(cx: &mut ParseCtxt) -> ParseResult<GenericArg> {
    let kind = if cx.peek2(NonReserved, token::Eq) {
        let ident = parse_ident(cx)?;
        cx.expect(token::Eq)?;
        let ty = parse_type(cx)?;
        GenericArgKind::Constraint(ident, ty)
    } else {
        GenericArgKind::Type(parse_type(cx)?)
    };
    Ok(GenericArg { kind, node_id: cx.next_node_id() })
}

/// ```text
/// ⟨refine_arg⟩ :=  @ ⟨ident⟩
///               |  # ⟨ident⟩
///               |  |⟨⟨refine_parm⟩,*| ⟨expr⟩
///               |  ⟨expr⟩
/// ```
fn parse_refine_arg(cx: &mut ParseCtxt) -> ParseResult<RefineArg> {
    let lo = cx.lo();
    let arg = if cx.advance_if(token::At) {
        // @ ⟨ident⟩
        let bind = parse_ident(cx)?;
        let hi = cx.hi();
        RefineArg::Bind(bind, BindKind::At, cx.mk_span(lo, hi), cx.next_node_id())
    } else if cx.peek2(token::Pound, NonReserved) {
        // # ⟨ident⟩
        cx.expect(token::Pound)?;
        let bind = parse_ident(cx)?;
        let hi = cx.hi();
        RefineArg::Bind(bind, BindKind::Pound, cx.mk_span(lo, hi), cx.next_node_id())
    } else if cx.advance_if(Or) {
        let params =
            punctuated_until(cx, Comma, Or, |cx| parse_refine_param(cx, RequireSort::Maybe))?;
        cx.expect(Or)?;
        let body = parse_expr(cx, true)?;
        let hi = cx.hi();
        RefineArg::Abs(params, body, cx.mk_span(lo, hi), cx.next_node_id())
    } else {
        // ⟨expr⟩
        RefineArg::Expr(parse_expr(cx, true)?)
    };
    Ok(arg)
}

/// Whether a sort is required in a refinement parameter declaration.
enum RequireSort {
    /// Definitely require a sort
    Yes,
    /// Optional sort. Use [`Sort::Infer`] if not present
    Maybe,
    /// Definitely do not not require a sort. Always use [`Sort::Infer`]
    No,
}

fn parse_sort_if_required(cx: &mut ParseCtxt, require_sort: RequireSort) -> ParseResult<Sort> {
    match require_sort {
        RequireSort::No => Ok(Sort::Infer),
        RequireSort::Maybe => {
            if cx.advance_if(token::Colon) {
                parse_sort(cx)
            } else {
                Ok(Sort::Infer)
            }
        }
        RequireSort::Yes => {
            cx.expect(token::Colon)?;
            parse_sort(cx)
        }
    }
}

/// ```text
/// ⟨refine_param⟩ := ⟨mode⟩? ⟨ident⟩ ⟨ : ⟨sort⟩ ⟩?    if require_sort is Maybe
///                 | ⟨mode⟩? ⟨ident⟩ : ⟨sort⟩         if require_sort is Yes
///                 | ⟨mode⟩? ⟨ident⟩                  if require_sort is No
/// ```
fn parse_refine_param(cx: &mut ParseCtxt, require_sort: RequireSort) -> ParseResult<RefineParam> {
    let lo = cx.lo();
    let mode = parse_opt_param_mode(cx);
    let ident = parse_ident(cx)?;
    let sort = parse_sort_if_required(cx, require_sort)?;
    let hi = cx.hi();
    Ok(RefineParam { mode, ident, sort, span: cx.mk_span(lo, hi), node_id: cx.next_node_id() })
}

/// ```text
/// ⟨mode⟩ := ⟨ hrn | hdl ⟩?
/// ```
fn parse_opt_param_mode(cx: &mut ParseCtxt) -> Option<ParamMode> {
    if cx.advance_if(kw::Hrn) {
        Some(ParamMode::Horn)
    } else if cx.advance_if(kw::Hdl) {
        Some(ParamMode::Hindley)
    } else {
        None
    }
}

pub(crate) fn parse_expr(cx: &mut ParseCtxt, allow_struct: bool) -> ParseResult<Expr> {
    parse_binops(cx, Precedence::MIN, allow_struct)
}

fn parse_binops(cx: &mut ParseCtxt, base: Precedence, allow_struct: bool) -> ParseResult<Expr> {
    let mut lhs = unary_expr(cx, allow_struct)?;
    loop {
        let lo = cx.lo();
        let Some((op, ntokens)) = cx.peek_binop() else { break };
        let precedence = Precedence::of_binop(&op);
        if precedence < base {
            break;
        }
        cx.advance_by(ntokens);
        let next = match precedence.associativity() {
            Associativity::Right => precedence,
            Associativity::Left => precedence.next(),
            Associativity::None => {
                if let ExprKind::BinaryOp(op, ..) = &lhs.kind
                    && Precedence::of_binop(op) == precedence
                {
                    return Err(cx.cannot_be_chained(lo, cx.hi()));
                }
                precedence.next()
            }
        };
        let rhs = parse_binops(cx, next, allow_struct)?;
        let span = lhs.span.to(rhs.span);
        lhs = Expr {
            kind: ExprKind::BinaryOp(op, Box::new([lhs, rhs])),
            node_id: cx.next_node_id(),
            span,
        }
    }
    Ok(lhs)
}

/// ```text
/// ⟨unary_expr⟩ := - ⟨unary_expr⟩ | ! ⟨unary_expr⟩ | ⟨trailer_expr⟩
/// ```
fn unary_expr(cx: &mut ParseCtxt, allow_struct: bool) -> ParseResult<Expr> {
    let lo = cx.lo();
    let kind = if cx.advance_if(token::Minus) {
        ExprKind::UnaryOp(UnOp::Neg, Box::new(unary_expr(cx, allow_struct)?))
    } else if cx.advance_if(token::Bang) {
        ExprKind::UnaryOp(UnOp::Not, Box::new(unary_expr(cx, allow_struct)?))
    } else {
        return parse_trailer_expr(cx, allow_struct);
    };
    let hi = cx.hi();
    Ok(Expr { kind, node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) })
}

/// ```text
/// ⟨trailer_expr⟩ :=  ⟨trailer⟩ . ⟨ident⟩
///                 |  ⟨trailer⟩ ( ⟨expr⟩,* )
///                 |  ⟨atom⟩
/// ```
fn parse_trailer_expr(cx: &mut ParseCtxt, allow_struct: bool) -> ParseResult<Expr> {
    let lo = cx.lo();
    let mut e = parse_atom(cx, allow_struct)?;
    loop {
        let kind = if cx.advance_if(token::Dot) {
            // ⟨trailer⟩ . ⟨ident⟩
            let field = parse_ident(cx)?;
            ExprKind::Dot(Box::new(e), field)
        } else if cx.peek(token::OpenParen) {
            // ⟨trailer⟩ ( ⟨expr⟩,* )
            let args = parens(cx, Comma, |cx| parse_expr(cx, true))?;
            ExprKind::Call(Box::new(e), args)
        } else {
            break;
        };
        let hi = cx.hi();
        e = Expr { kind, node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) };
    }
    Ok(e)
}

/// ```text
/// ⟨atom⟩ := ⟨if_expr⟩
///         | ⟨lit⟩
///         | ( ⟨expr⟩ )
///         | ⟨epath⟩
///         | ⟨bounded_quant⟩
///         |  <⟨ty⟩ as ⟨path⟩> :: ⟨ident⟩
///         | [binop]
///         | ⟨epath⟩ { ⟨constructor_arg⟩,* }    if allow_struct
///         | { ⟨constructor_arg⟩,* }            if allow_struct
///         | #{ ⟨expr⟩,* }
/// ```
fn parse_atom(cx: &mut ParseCtxt, allow_struct: bool) -> ParseResult<Expr> {
    let lo = cx.lo();
    let mut lookahead = cx.lookahead1();
    if lookahead.peek(kw::If) {
        // ⟨if_expr⟩
        parse_if_expr(cx)
    } else if lookahead.peek(AnyLit) {
        // ⟨lit⟩
        parse_lit(cx)
    } else if lookahead.peek(token::OpenParen) {
        delimited(cx, Parenthesis, |cx| parse_expr(cx, true))
    } else if lookahead.advance_if(token::Pound) {
        // #{ ⟨expr⟩,* }
        let lo = cx.lo();
        let exprs = braces(cx, Comma, |cx| parse_expr(cx, true))?;
        let hi = cx.hi();
        let kind = ExprKind::SetLiteral(exprs);
        Ok(Expr { kind, node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) })
    } else if lookahead.peek(NonReserved) {
        let path = parse_expr_path(cx)?;
        let kind = if allow_struct && cx.peek(token::OpenBrace) {
            // ⟨epath⟩ { ⟨constructor_arg⟩,* }
            let args = braces(cx, Comma, parse_constructor_arg)?;
            ExprKind::Constructor(Some(path), args)
        } else {
            // ⟨epath⟩
            ExprKind::Path(path)
        };
        let hi = cx.hi();
        Ok(Expr { kind, node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) })
    } else if allow_struct && lookahead.peek(token::OpenBrace) {
        // { ⟨constructor_arg⟩,* }
        let args = braces(cx, Comma, parse_constructor_arg)?;
        let hi = cx.hi();
        Ok(Expr {
            kind: ExprKind::Constructor(None, args),
            node_id: cx.next_node_id(),
            span: cx.mk_span(lo, hi),
        })
    } else if lookahead.advance_if(LAngle) {
        // <⟨ty⟩ as ⟨path⟩> :: ⟨ident⟩
        let lo = cx.lo();
        let qself = parse_type(cx)?;
        cx.expect(kw::As)?;
        let path = parse_path(cx)?;
        cx.expect(RAngle)?;
        cx.expect(token::PathSep)?;
        let name = parse_ident(cx)?;
        let hi = cx.hi();
        let kind = ExprKind::AssocReft(Box::new(qself), path, name);
        Ok(Expr { kind, node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) })
    } else if lookahead.peek(token::OpenBracket) {
        parse_prim_uif(cx)
    } else if lookahead.peek(kw::Exists) || lookahead.peek(kw::Forall) {
        parse_bounded_quantifier(cx)
    } else {
        Err(lookahead.into_error())
    }
}

fn parse_prim_uif(cx: &mut ParseCtxt) -> ParseResult<Expr> {
    let lo = cx.lo();
    cx.expect(token::OpenBracket)?;
    let op = parse_binop(cx)?;
    cx.expect(token::CloseBracket)?;
    let hi = cx.hi();
    Ok(Expr { kind: ExprKind::PrimUIF(op), node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) })
}

/// ```text
/// ⟨bounded_quant⟩ := forall ⟨refine_param⟩ in ⟨int⟩..⟨int⟩ ⟨block⟩
///                  | exists ⟨refine_param⟩ in ⟨int⟩..⟨int⟩ ⟨block⟩
/// ```
fn parse_bounded_quantifier(cx: &mut ParseCtxt) -> ParseResult<Expr> {
    let lo = cx.lo();
    let mut lookahead = cx.lookahead1();
    let quant = if lookahead.advance_if(kw::Forall) {
        QuantKind::Forall
    } else if lookahead.advance_if(kw::Exists) {
        QuantKind::Exists
    } else {
        return Err(lookahead.into_error());
    };
    let param = parse_refine_param(cx, RequireSort::Maybe)?;
    cx.expect(kw::In)?;
    let start = parse_int(cx)?;
    cx.expect(token::DotDot)?;
    let end = parse_int(cx)?;
    let body = parse_block(cx)?;
    let hi = cx.hi();
    Ok(Expr {
        kind: ExprKind::BoundedQuant(quant, param, start..end, Box::new(body)),
        node_id: cx.next_node_id(),
        span: cx.mk_span(lo, hi),
    })
}

/// ```text
/// ⟨constructor_arg⟩ :=  ⟨ident⟩ : ⟨expr⟩ |  ..
/// ```
fn parse_constructor_arg(cx: &mut ParseCtxt) -> ParseResult<ConstructorArg> {
    let lo = cx.lo();
    let mut lookahead = cx.lookahead1();
    if lookahead.peek(NonReserved) {
        let ident = parse_ident(cx)?;
        cx.expect(token::Colon)?;
        let expr = parse_expr(cx, true)?;
        let hi = cx.hi();
        Ok(ConstructorArg::FieldExpr(FieldExpr {
            ident,
            expr,
            node_id: cx.next_node_id(),
            span: cx.mk_span(lo, hi),
        }))
    } else if lookahead.advance_if(token::DotDot) {
        let spread = parse_expr(cx, true)?;
        let hi = cx.hi();
        Ok(ConstructorArg::Spread(Spread {
            expr: spread,
            node_id: cx.next_node_id(),
            span: cx.mk_span(lo, hi),
        }))
    } else {
        Err(lookahead.into_error())
    }
}

/// `⟨epath⟩ := ⟨ident⟩ ⟨ :: ⟨ident⟩ ⟩*`
fn parse_expr_path(cx: &mut ParseCtxt) -> ParseResult<ExprPath> {
    let lo = cx.lo();
    let segments = sep1(cx, token::PathSep, parse_expr_path_segment)?;
    let hi = cx.hi();
    Ok(ExprPath { segments, node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) })
}

fn parse_expr_path_segment(cx: &mut ParseCtxt) -> ParseResult<ExprPathSegment> {
    Ok(ExprPathSegment { ident: parse_ident(cx)?, node_id: cx.next_node_id() })
}

/// `⟨if_expr⟩ := if ⟨expr⟩ ⟨block⟩ ⟨ else if ⟨expr⟩ ⟨block⟩ ⟩* else ⟨block⟩`
///
/// The `⟨expr⟩` in conditions is parsed with `allow_struct = false`
fn parse_if_expr(cx: &mut ParseCtxt) -> ParseResult<Expr> {
    let mut branches = vec![];

    loop {
        let lo = cx.lo();
        cx.expect(kw::If)?;
        let cond = parse_expr(cx, false)?;
        let then_ = parse_block(cx)?;
        branches.push((lo, cond, then_));
        cx.expect(kw::Else)?;

        if !cx.peek(kw::If) {
            break;
        }
    }
    let mut else_ = parse_block(cx)?;

    let hi = cx.hi();
    while let Some((lo, cond, then_)) = branches.pop() {
        else_ = Expr {
            kind: ExprKind::IfThenElse(Box::new([cond, then_, else_])),
            node_id: cx.next_node_id(),
            span: cx.mk_span(lo, hi),
        };
    }
    Ok(else_)
}

/// `⟨block⟩ := { ⟨block_expr⟩ }`
fn parse_block(cx: &mut ParseCtxt) -> ParseResult<Expr> {
    delimited(cx, Brace, parse_block_expr)
}

/// `⟨block_expr⟩ = ⟨let_decl⟩* ⟨expr⟩`
fn parse_block_expr(cx: &mut ParseCtxt) -> ParseResult<Expr> {
    let lo = cx.lo();
    let decls = repeat_while(cx, kw::Let, parse_let_decl)?;
    let body = parse_expr(cx, true)?;
    let hi = cx.hi();

    if decls.is_empty() {
        Ok(body)
    } else {
        let kind = ExprKind::Block(decls, Box::new(body));
        Ok(Expr { kind, node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) })
    }
}

/// `⟨let_decl⟩ := let ⟨refine_param⟩ = ⟨expr⟩ ;`
fn parse_let_decl(cx: &mut ParseCtxt) -> ParseResult<LetDecl> {
    cx.expect(kw::Let)?;
    let param = parse_refine_param(cx, RequireSort::Maybe)?;
    cx.expect(token::Eq)?;
    let init = parse_expr(cx, true)?;
    cx.expect(token::Semi)?;
    Ok(LetDecl { param, init })
}

/// ```text
/// ⟨lit⟩ := ⟨a Rust literal like an integer or a boolean⟩
/// ```
fn parse_lit(cx: &mut ParseCtxt) -> ParseResult<Expr> {
    if let Token { kind: token::Literal(lit), lo, hi } = cx.at(0) {
        cx.advance();
        Ok(Expr {
            kind: ExprKind::Literal(lit),
            node_id: cx.next_node_id(),
            span: cx.mk_span(lo, hi),
        })
    } else {
        Err(cx.unexpected_token(vec![AnyLit.expected()]))
    }
}

fn parse_ident(cx: &mut ParseCtxt) -> ParseResult<Ident> {
    if let Token { kind: token::Ident(name, is_raw), lo, hi } = cx.at(0)
        && (!cx.is_reserved(name) || is_raw == IdentIsRaw::Yes)
    {
        cx.advance();
        return Ok(Ident { name, span: cx.mk_span(lo, hi) });
    }
    Err(cx.unexpected_token(vec![NonReserved.expected()]))
}

fn parse_int<T: FromStr>(cx: &mut ParseCtxt) -> ParseResult<T> {
    if let token::Literal(lit) = cx.at(0).kind
        && let LitKind::Integer = lit.kind
        && let Ok(value) = lit.symbol.as_str().parse::<T>()
    {
        cx.advance();
        return Ok(value);
    }

    Err(cx.unexpected_token(vec![Expected::Str(std::any::type_name::<T>())]))
}

/// ```text
/// ⟨sort⟩ :=  ⟨base_sort⟩
///         |  ( ⟨base_sort⟩,* ) -> ⟨base_sort⟩
///         |  ⟨base_sort⟩ -> ⟨base_sort⟩
/// ```
fn parse_sort(cx: &mut ParseCtxt) -> ParseResult<Sort> {
    if cx.peek(token::OpenParen) {
        // ( ⟨base_sort⟩,* ) -> ⟨base_sort⟩
        let inputs = parens(cx, Comma, parse_base_sort)?;
        cx.expect(token::RArrow)?;
        let output = parse_base_sort(cx)?;
        Ok(Sort::Func { inputs, output })
    } else {
        let bsort = parse_base_sort(cx)?;
        if cx.advance_if(token::RArrow) {
            // ⟨base_sort⟩ -> ⟨base_sort⟩
            let output = parse_base_sort(cx)?;
            Ok(Sort::Func { inputs: vec![bsort], output })
        } else {
            // ⟨base_sort⟩
            Ok(Sort::Base(bsort))
        }
    }
}

/// ```text
/// ⟨base_sort⟩ := bitvec < ⟨u32⟩ >
///              | ⟨sort_path⟩ < ⟨base_sort⟩,* >
///              | < ⟨ty⟩ as ⟨path⟩ > :: ⟨segment⟩
/// ⟨sort_path⟩ := ⟨ident⟩ ⟨ :: ⟨ident⟩ ⟩* < (⟨base_sort⟩,*) >
/// ```
fn parse_base_sort(cx: &mut ParseCtxt) -> ParseResult<BaseSort> {
    if cx.advance_if(kw::Bitvec) {
        // bitvec < ⟨u32⟩ >
        cx.expect(LAngle)?;
        let len = parse_int(cx)?;
        cx.expect(RAngle)?;
        Ok(BaseSort::BitVec(len))
    } else if cx.advance_if(LAngle) {
        // < ⟨ty⟩ as ⟨path⟩ > :: ⟨segment⟩
        let qself = parse_type(cx)?;
        cx.expect(kw::As)?;
        let mut path = parse_path(cx)?;
        cx.expect(RAngle)?;
        cx.expect(token::PathSep)?;
        path.segments.push(parse_segment(cx)?);
        Ok(BaseSort::SortOf(Box::new(qself), path))
    } else {
        // ⟨sort_path⟩ < ⟨base_sort⟩,* >
        let segments = sep1(cx, token::PathSep, parse_ident)?;
        let args = opt_angle(cx, Comma, parse_base_sort)?;
        let path = SortPath { segments, args, node_id: cx.next_node_id() };
        Ok(BaseSort::Path(path))
    }
}

// Reference: https://doc.rust-lang.org/reference/expressions.html#expression-precedence
#[derive(Clone, Copy, PartialEq, PartialOrd, Debug)]
enum Precedence {
    /// <=>
    Iff,
    /// =>
    Implies,
    /// ||
    Or,
    /// &&
    And,
    /// == != < > <= >=
    Compare,
    /// |
    BitOr,
    /// ^
    BitXor,
    /// &
    BitAnd,
    /// << >>
    Shift,
    /// + -
    Sum,
    /// * / %
    Product,
    /// unary - and !
    Prefix,
}

enum Associativity {
    Right,
    Left,
    None,
}

impl Precedence {
    const MIN: Self = Precedence::Iff;

    fn of_binop(op: &BinOp) -> Precedence {
        match op {
            BinOp::Iff => Precedence::Iff,
            BinOp::Imp => Precedence::Implies,
            BinOp::Or => Precedence::Or,
            BinOp::And => Precedence::And,
            BinOp::Eq | BinOp::Ne | BinOp::Gt | BinOp::Ge | BinOp::Lt | BinOp::Le => {
                Precedence::Compare
            }
            BinOp::BitOr => Precedence::BitOr,
            BinOp::BitXor => Precedence::BitXor,
            BinOp::BitAnd => Precedence::BitAnd,
            BinOp::BitShl | BinOp::BitShr => Precedence::Shift,
            BinOp::Add | BinOp::Sub => Precedence::Sum,
            BinOp::Mul | BinOp::Div | BinOp::Mod => Precedence::Product,
        }
    }

    fn next(self) -> Precedence {
        match self {
            Precedence::Iff => Precedence::Implies,
            Precedence::Implies => Precedence::Or,
            Precedence::Or => Precedence::And,
            Precedence::And => Precedence::Compare,
            Precedence::Compare => Precedence::BitOr,
            Precedence::BitOr => Precedence::BitXor,
            Precedence::BitXor => Precedence::BitAnd,
            Precedence::BitAnd => Precedence::Shift,
            Precedence::Shift => Precedence::Sum,
            Precedence::Sum => Precedence::Product,
            Precedence::Product => Precedence::Prefix,
            Precedence::Prefix => Precedence::Prefix,
        }
    }

    fn associativity(self) -> Associativity {
        match self {
            Precedence::Or
            | Precedence::And
            | Precedence::BitOr
            | Precedence::BitXor
            | Precedence::BitAnd
            | Precedence::Shift
            | Precedence::Sum
            | Precedence::Product => Associativity::Left,
            Precedence::Compare | Precedence::Iff => Associativity::None,
            Precedence::Implies | Precedence::Prefix => Associativity::Right,
        }
    }
}
