use std::str::FromStr;

use rustc_span::BytePos;

use crate::{
    ParseCtxt, ParseResult,
    lexer::{
        Cursor,
        Delimiter::{self, *},
        Token::{self as Tok, Caret, CloseDelim, Comma, OpenDelim},
    },
    surface::{
        AliasReft, Async, BaseSort, BaseTy, BaseTyKind, BinOp, BindKind, ConstArg, ConstArgKind,
        ConstructorArg, Ensures, Expr, ExprKind, ExprPath, ExprPathSegment, FieldExpr, FnInput,
        FnOutput, FnRetTy, FnSig, GenericArg, GenericArgKind, GenericBounds, GenericParam,
        GenericParamKind, Generics, Ident, ImplAssocReft, Indices, Item, LitKind, Mutability,
        ParamMode, Path, PathSegment, QualNames, Qualifier, QuantKind, RefineArg, RefineParam,
        RefineParams, Requires, Sort, SortDecl, SortPath, SpecFunc, Spread, TraitAssocReft,
        TraitRef, Ty, TyAlias, TyKind, UnOp, VariantDef, VariantRet, WhereBoundPredicate,
    },
};

///   yes ⟨ , reason = ⟨literal⟩ ⟩?
/// | no ⟨ , reason = ⟨literal⟩ ⟩?
/// | reason = ⟨literal⟩
pub(crate) fn parse_yes_or_no_with_reason(cx: &mut ParseCtxt) -> ParseResult<bool> {
    if cx.advance_if("yes") {
        if cx.advance_if(Tok::Comma) {
            parse_reason(cx)?;
        }
        Ok(true)
    } else if cx.advance_if("no") {
        if cx.advance_if(Tok::Comma) {
            parse_reason(cx)?;
        }
        Ok(false)
    } else if cx.peek("reason") {
        parse_reason(cx)?;
        Ok(true)
    } else {
        Err(cx.unexpected_token())
    }
}

/// ⟨reason⟩ = reason = ⟨literal⟩
fn parse_reason(cx: &mut ParseCtxt) -> ParseResult {
    cx.expect("reason")?;
    cx.expect(Tok::Eq)?;
    cx.expect(AnyLit)
}

pub(crate) fn parse_qual_names(cx: &mut ParseCtxt) -> ParseResult<QualNames> {
    let names = sep_until(cx, Comma, Tok::Eof, parse_ident)?;
    Ok(QualNames { names })
}

pub(crate) fn parse_generics(cx: &mut ParseCtxt) -> ParseResult<Generics> {
    let lo = cx.lo();
    let params = sep_until(cx, Comma, Tok::Eof, parse_generic_param)?;
    let hi = cx.hi();
    Ok(Generics { params, predicates: None, span: cx.mk_span(lo, hi) })
}

pub(crate) fn parse_flux_items(cx: &mut ParseCtxt) -> ParseResult<Vec<Item>> {
    until(cx, Tok::Eof, parse_flux_item)
}

fn parse_flux_item(cx: &mut ParseCtxt) -> ParseResult<Item> {
    if cx.peek(Tok::Fn) {
        parse_reft_func(cx).map(Item::FuncDef)
    } else if cx.peek([Tok::Local, Tok::Qualifier]) {
        parse_qualifier(cx).map(Item::Qualifier)
    } else if cx.peek(Tok::Opaque) {
        parse_sort_decl(cx).map(Item::SortDecl)
    } else {
        Err(cx.unexpected_token())
    }
}

fn parse_reft_func(cx: &mut ParseCtxt) -> ParseResult<SpecFunc> {
    cx.expect(Tok::Fn)?;
    let name = parse_ident(cx)?;
    let sort_vars = opt_angle(cx, Comma, parse_ident)?;
    let params = parens(cx, Comma, |cx| parse_refine_param(cx, true))?;
    cx.expect(Tok::RArrow)?;
    let output = parse_sort(cx)?;
    let body = if cx.peek(OpenDelim(Brace)) {
        Some(parse_block_expr(cx)?)
    } else {
        cx.expect(Tok::Semi)?;
        None
    };
    Ok(SpecFunc { name, sort_vars, params, output, body })
}

fn parse_qualifier(cx: &mut ParseCtxt) -> ParseResult<Qualifier> {
    let lo = cx.lo();
    let local = cx.advance_if(Tok::Local);
    cx.expect(Tok::Qualifier)?;
    let name = parse_ident(cx)?;
    let params = parens(cx, Comma, |cx| parse_refine_param(cx, true))?;
    let expr = parse_block_expr(cx)?;
    let hi = cx.hi();
    Ok(Qualifier { global: !local, name, params, expr, span: cx.mk_span(lo, hi) })
}

fn parse_sort_decl(cx: &mut ParseCtxt) -> ParseResult<SortDecl> {
    cx.expect(Tok::Opaque)?;
    cx.expect(Tok::Sort)?;
    let name = parse_ident(cx)?;
    cx.expect(Tok::Semi)?;
    Ok(SortDecl { name })
}

pub(crate) fn parse_trait_assoc_refts(cx: &mut ParseCtxt) -> ParseResult<Vec<TraitAssocReft>> {
    until(cx, Tok::Eof, parse_trait_assoc_reft)
}

/// ⟨trait_assoc_reft⟩ := fn ⟨ident⟩ ( ⟨refine_param⟩,* ) -> ⟨base_sort⟩ ;?
///                     | fn ⟨ident⟩ ( ⟨refine_param⟩,* ) -> ⟨base_sort⟩ ⟨block_expr⟩
fn parse_trait_assoc_reft(cx: &mut ParseCtxt) -> ParseResult<TraitAssocReft> {
    let lo = cx.lo();
    cx.expect(Tok::Fn)?;
    let name = parse_ident(cx)?;
    let params = parens(cx, Comma, |cx| parse_refine_param(cx, true))?;
    cx.expect(Tok::RArrow)?;
    let output = parse_base_sort(cx)?;
    let body = if cx.peek(OpenDelim(Brace)) {
        Some(parse_block_expr(cx)?)
    } else {
        cx.advance_if(Tok::Semi);
        None
    };
    let hi = cx.hi();
    Ok(TraitAssocReft { name, params, output, body, span: cx.mk_span(lo, hi) })
}

pub(crate) fn parse_impl_assoc_refts(cx: &mut ParseCtxt) -> ParseResult<Vec<ImplAssocReft>> {
    until(cx, Tok::Eof, parse_impl_assoc_reft)
}

/// ⟨impl_assoc_reft⟩ := fn ⟨ident⟩ ( ⟨refine_param⟩,* ) -> ⟨base_sort⟩ ⟨block_expr⟩
fn parse_impl_assoc_reft(cx: &mut ParseCtxt) -> ParseResult<ImplAssocReft> {
    let lo = cx.lo();
    cx.expect(Tok::Fn)?;
    let name = parse_ident(cx)?;
    let params = parens(cx, Comma, |cx| parse_refine_param(cx, true))?;
    cx.expect(Tok::RArrow)?;
    let output = parse_base_sort(cx)?;
    let body = parse_block_expr(cx)?;
    let hi = cx.hi();
    Ok(ImplAssocReft { name, params, output, body, span: cx.mk_span(lo, hi) })
}

/// ⟨refined_by⟩ := ⟨refine_param⟩,*
pub(crate) fn parse_refined_by(cx: &mut ParseCtxt) -> ParseResult<RefineParams> {
    sep_until(cx, Comma, Tok::Eof, |cx| parse_refine_param(cx, true))
}

/// ⟨variant⟩ := ⟨fields⟩ -> ⟨variant_ret⟩
///            | ⟨fields⟩
///            | ⟨variant_ret⟩
pub(crate) fn parse_variant(cx: &mut ParseCtxt) -> ParseResult<VariantDef> {
    let lo = cx.lo();
    let mut fields = vec![];
    let mut ret = None;
    if cx.peek([OpenDelim(Parenthesis), OpenDelim(Brace)]) {
        fields = parse_fields(cx)?;
        if cx.advance_if(Tok::RArrow) {
            ret = Some(parse_variant_ret(cx)?);
        }
    } else {
        ret = Some(parse_variant_ret(cx)?);
    };
    let hi = cx.hi();
    Ok(VariantDef { fields, ret, node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) })
}

/// ⟨fields⟩ := ( ⟨ty⟩,* ) | { ⟨ty⟩,* }
fn parse_fields(cx: &mut ParseCtxt) -> ParseResult<Vec<Ty>> {
    if cx.peek(OpenDelim(Parenthesis)) {
        parens(cx, Comma, parse_type)
    } else if cx.peek(OpenDelim(Brace)) {
        braces(cx, Comma, parse_type)
    } else {
        Err(cx.unexpected_token())
    }
}

/// ⟨variant_ret⟩ := ⟨path⟩ ⟨ [ ⟨refine_arg⟩,? ] ⟩?
fn parse_variant_ret(cx: &mut ParseCtxt) -> ParseResult<VariantRet> {
    let path = parse_path(cx)?;
    let indices = if cx.peek(OpenDelim(Bracket)) {
        parse_indices(cx)?
    } else {
        let hi = cx.hi();
        Indices { indices: vec![], span: cx.mk_span(hi, hi) }
    };
    Ok(VariantRet { path, indices })
}

pub(crate) fn parse_type_alias(cx: &mut ParseCtxt) -> ParseResult<TyAlias> {
    let lo = cx.lo();
    cx.expect(Tok::Type)?;
    let ident = parse_ident(cx)?;
    let generics = parse_opt_generics(cx)?;
    let params = if cx.peek(OpenDelim(Parenthesis)) {
        parens(cx, Comma, |cx| parse_refine_param(cx, true))?
    } else {
        vec![]
    };
    let index = if cx.peek(OpenDelim(Bracket)) {
        Some(delimited(cx, Bracket, |cx| parse_refine_param(cx, true))?)
    } else {
        None
    };
    cx.expect(Tok::Eq)?;
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
    let mut kind = GenericParamKind::Type;
    if cx.advance_if(Tok::As) {
        if cx.advance_if("type") {
            kind = GenericParamKind::Type;
        } else if cx.advance_if("base") {
            cx.tokens.advance();
            kind = GenericParamKind::Base;
        } else {
            return Err(cx.unexpected_token());
        }
    };
    Ok(GenericParam { name, kind, node_id: cx.next_node_id() })
}

/// ⟨fn_sig⟩ := ⟨asyncness⟩ fn ⟨ident⟩?
///             ⟨ [ ⟨refine_param⟩,* ] ⟩?
///             ( ⟨fn_inputs⟩,* )
///             ⟨-> ⟨ty⟩⟩?
///             ⟨requires⟩ ⟨ensures⟩ ⟨where⟩
pub(crate) fn parse_fn_sig(cx: &mut ParseCtxt) -> ParseResult<FnSig> {
    let lo = cx.lo();
    let asyncness = parse_asyncness(cx);
    cx.expect(Tok::Fn)?;
    let ident = if cx.peek(AnyIdent) { Some(parse_ident(cx)?) } else { None };
    let mut generics = parse_opt_generics(cx)?;
    let params = if cx.peek(OpenDelim(Bracket)) {
        brackets(cx, Comma, |cx| parse_refine_param(cx, false))?
    } else {
        vec![]
    };
    let (inputs, _) = punctuated(cx, Parenthesis, Comma, parse_fn_input)?;
    let returns = parse_fn_ret(cx)?;
    let requires = parse_opt_requires(cx)?;
    let ensures = parse_opt_ensures(cx)?;
    generics.predicates = parse_opt_where(cx)?;
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

/// ⟨requires⟩ := ⟨ requires ⟨requires_clause⟩,* ⟩?
fn parse_opt_requires(cx: &mut ParseCtxt) -> ParseResult<Vec<Requires>> {
    if !cx.advance_if(Tok::Requires) {
        return Ok(vec![]);
    }
    sep_until(cx, Comma, [Tok::Ensures, Tok::Where, Tok::Eof], parse_requires_clause)
}

/// ⟨requires_clause⟩ := ⟨ forall ⟨refine_param⟩,+ . ⟩? ⟨expr⟩
fn parse_requires_clause(cx: &mut ParseCtxt) -> ParseResult<Requires> {
    let mut params = vec![];
    if cx.advance_if(Tok::Forall) {
        params = sep1(cx, Comma, |cx| parse_refine_param(cx, false))?;
        cx.expect(Tok::Dot)?;
    }
    let pred = parse_expr(cx, true)?;
    Ok(Requires { params, pred })
}

/// ⟨ensures⟩ := ⟨ensures ⟨ensures_clause⟩,*⟩?
fn parse_opt_ensures(cx: &mut ParseCtxt) -> ParseResult<Vec<Ensures>> {
    if !cx.advance_if(Tok::Ensures) {
        return Ok(vec![]);
    }
    sep_until(cx, Comma, [Tok::Where, Tok::Eof], parse_ensures_clause)
}

/// ⟨ensures_clause⟩ :=  ⟨ident⟩ : ⟨ty⟩
///                   |  ⟨expr⟩
fn parse_ensures_clause(cx: &mut ParseCtxt) -> ParseResult<Ensures> {
    if cx.peek2(AnyIdent, Tok::Colon) {
        // ⟨ident⟩ : ⟨ty⟩
        let ident = parse_ident(cx)?;
        cx.expect(Tok::Colon)?;
        let ty = parse_type(cx)?;
        Ok(Ensures::Type(ident, ty, cx.next_node_id()))
    } else {
        // ⟨expr⟩
        Ok(Ensures::Pred(parse_expr(cx, true)?))
    }
}

fn parse_opt_where(cx: &mut ParseCtxt) -> ParseResult<Option<Vec<WhereBoundPredicate>>> {
    if !cx.advance_if(Tok::Where) {
        return Ok(None);
    }
    Ok(Some(sep_until(cx, Comma, Tok::Eof, parse_where_bound)?))
}

fn parse_where_bound(cx: &mut ParseCtxt) -> ParseResult<WhereBoundPredicate> {
    let lo = cx.lo();
    let bounded_ty = parse_type(cx)?;
    cx.expect(Tok::Colon)?;
    let bounds = parse_generic_bounds(cx)?;
    let hi = cx.hi();
    Ok(WhereBoundPredicate { span: cx.mk_span(lo, hi), bounded_ty, bounds })
}

/// ⟨fn_ret⟩ := ⟨ -> ⟨ty⟩ ⟩?
fn parse_fn_ret(cx: &mut ParseCtxt) -> ParseResult<FnRetTy> {
    if cx.advance_if(Tok::RArrow) {
        Ok(FnRetTy::Ty(parse_type(cx)?))
    } else {
        let hi = cx.hi();
        Ok(FnRetTy::Default(cx.mk_span(hi, hi)))
    }
}

/// ⟨fn_input⟩ := ⟨ident⟩ : &strg ⟨ty⟩
///             | ⟨ident⟩ : ⟨path⟩ { ⟨expr⟩ }
///             | ⟨ident⟩ : ⟨ty⟩
///             | ⟨ty⟩
fn parse_fn_input(cx: &mut ParseCtxt) -> ParseResult<FnInput> {
    if cx.peek2(AnyIdent, Tok::Colon) {
        let bind = parse_ident(cx)?;
        cx.expect(Tok::Colon)?;
        if cx.advance_if2(Tok::And, Tok::Strg) {
            // ⟨ident⟩ : &strg ⟨ty⟩
            Ok(FnInput::StrgRef(bind, parse_type(cx)?, cx.next_node_id()))
        } else if cx.peek(AnyIdent) {
            let path = parse_path(cx)?;
            if cx.peek3(OpenDelim(Brace), AnyIdent, Tok::Colon) {
                // ⟨ident⟩ : ⟨ty⟩
                let bty = path_to_bty(path);
                let ty = parse_bty_exists(cx, bty)?;
                Ok(FnInput::Ty(Some(bind), ty, cx.next_node_id()))
            } else if cx.peek(OpenDelim(Brace)) {
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

/// ⟨asyncness⟩ := async?
fn parse_asyncness(cx: &mut ParseCtxt) -> Async {
    let lo = cx.lo();
    if cx.advance_if(Tok::Async) {
        Async::Yes { node_id: cx.next_node_id(), span: cx.mk_span(lo, cx.hi()) }
    } else {
        Async::No
    }
}

/// ⟨ty⟩ := _
///       | { ⟨ident⟩ ⟨,⟨ident⟩⟩* . ⟨ty⟩ | ⟨expr⟩ }
///       | ( ⟨ty⟩,* )
///       | { ⟨ty⟩ | ⟨expr⟩ }
///       | { ⟨refine_param⟩ ⟨,⟨refine_param⟩⟩* . ⟨ty⟩ | ⟨expr⟩ }
///       | & mut? ⟨ty⟩
///       | [ ⟨ty⟩ ; ⟨const_arg⟩ ]
///       | impl ⟨path⟩
///       | ⟨bty⟩
///       | ⟨bty⟩ [ ⟨refine_arg⟩,* ]
///       | ⟨bty⟩ { ⟨ident⟩ : ⟨expr⟩ }
///
/// ⟨bty⟩ := ⟨path⟩ | ⟨qpath⟩ | [ ⟨ty⟩ ]
pub(crate) fn parse_type(cx: &mut ParseCtxt) -> ParseResult<Ty> {
    let lo = cx.lo();
    let kind = if cx.advance_if(Tok::Underscore) {
        TyKind::Hole
    } else if cx.peek(OpenDelim(Parenthesis)) {
        // ( ⟨ty⟩,* )
        let (mut tys, trailing) = punctuated(cx, Parenthesis, Comma, parse_type)?;
        if tys.len() == 1 && !trailing {
            return Ok(tys.remove(0));
        } else {
            TyKind::Tuple(tys)
        }
    } else if cx.peek(OpenDelim(Brace)) {
        delimited(cx, Brace, |cx| {
            if cx.peek2(AnyIdent, [Tok::Comma, Tok::Dot, Tok::Colon]) {
                // { ⟨refine_param⟩ ⟨,⟨refine_param⟩⟩* . ⟨ty⟩ | ⟨expr⟩ }
                parse_general_exists(cx)
            } else {
                // { ⟨ty⟩ | ⟨expr⟩ }
                let ty = parse_type(cx)?;
                cx.expect(Tok::Caret)?;
                let pred = parse_expr(cx, true)?;
                Ok(TyKind::Constr(pred, Box::new(ty)))
            }
        })?
    } else if cx.advance_if(Tok::And) {
        //  & mut? ⟨ty⟩
        let mutbl = if cx.advance_if(Tok::Mut) { Mutability::Mut } else { Mutability::Not };
        TyKind::Ref(mutbl, Box::new(parse_type(cx)?))
    } else if cx.advance_if(OpenDelim(Bracket)) {
        let ty = parse_type(cx)?;
        if cx.advance_if(Tok::Semi) {
            // [ ⟨ty⟩ ; ⟨const_arg⟩ ]
            let len = parse_const_arg(cx)?;
            cx.expect(CloseDelim(Bracket))?;
            TyKind::Array(Box::new(ty), len)
        } else {
            // [ ⟨ty⟩ ] ⟨[ ⟨refine_arg⟩,* ]⟩
            cx.expect(CloseDelim(Bracket))?;
            let hi = cx.hi();
            let kind = BaseTyKind::Slice(Box::new(ty));
            let bty = BaseTy { kind, span: cx.mk_span(lo, hi) };
            return parse_bty_rhs(cx, bty);
        }
    } else if cx.advance_if(Tok::Impl) {
        // impl ⟨bounds⟩
        TyKind::ImplTrait(cx.next_node_id(), parse_generic_bounds(cx)?)
    } else if cx.peek(AnyIdent) {
        let path = parse_path(cx)?;
        let bty = path_to_bty(path);
        return parse_bty_rhs(cx, bty);
    } else if cx.peek(LAngle) {
        let bty = parse_qpath(cx)?;
        return parse_bty_rhs(cx, bty);
    } else {
        return Err(cx.unexpected_token());
    };
    let hi = cx.hi();
    Ok(Ty { kind, node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) })
}

/// ⟨qpath⟩ := < ⟨ty⟩ as ⟨segments⟩> :: ⟨segments⟩
fn parse_qpath(cx: &mut ParseCtxt) -> ParseResult<BaseTy> {
    let lo = cx.lo();
    cx.expect(LAngle)?;
    let qself = parse_type(cx)?;
    cx.expect(Tok::As)?;
    let mut segments = parse_segments(cx)?;
    cx.expect(RAngle)?;
    cx.expect(Tok::PathSep)?;
    segments.extend(parse_segments(cx)?);
    let hi = cx.hi();

    let path =
        Path { segments, refine: vec![], node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) };
    let kind = BaseTyKind::Path(Some(Box::new(qself)), path);
    Ok(BaseTy { kind, span: cx.mk_span(lo, hi) })
}

/// { ⟨refine_param⟩ ⟨,⟨refine_param⟩⟩* . ⟨ty⟩ | ⟨expr⟩ }
fn parse_general_exists(cx: &mut ParseCtxt) -> ParseResult<TyKind> {
    let params = sep1(cx, Comma, |cx| parse_refine_param(cx, false))?;
    cx.expect(Tok::Dot)?;
    let ty = parse_type(cx)?;
    let pred = if cx.advance_if(Tok::Caret) { Some(parse_expr(cx, true)?) } else { None };
    Ok(TyKind::GeneralExists { params, ty: Box::new(ty), pred })
}

///    ⟨bty⟩ [ ⟨refine_arg⟩,* ]
/// |  ⟨bty⟩ { ⟨ident⟩ : ⟨expr⟩ }
/// |  ⟨bty⟩
fn parse_bty_rhs(cx: &mut ParseCtxt, bty: BaseTy) -> ParseResult<Ty> {
    let lo = bty.span.lo();
    if cx.peek(OpenDelim(Bracket)) {
        // ⟨bty⟩ [ ⟨refine_arg⟩,* ]
        let indices = parse_indices(cx)?;
        let hi = cx.hi();
        let kind = TyKind::Indexed { bty, indices };
        Ok(Ty { kind, node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) })
    } else if cx.peek(OpenDelim(Brace)) {
        // ⟨bty⟩ { ⟨ident⟩ : ⟨expr⟩ }
        parse_bty_exists(cx, bty)
    } else {
        // ⟨bty⟩
        let hi = cx.hi();
        let kind = TyKind::Base(bty);
        Ok(Ty { kind, node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) })
    }
}

/// ⟨bty⟩ { ⟨ident⟩ : ⟨expr⟩ }
fn parse_bty_exists(cx: &mut ParseCtxt, bty: BaseTy) -> ParseResult<Ty> {
    let lo = bty.span.lo();
    delimited(cx, Brace, |cx| {
        let bind = parse_ident(cx)?;
        cx.expect(Tok::Colon)?;
        let pred = parse_expr(cx, true)?;
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

fn parse_generic_bounds(cx: &mut ParseCtxt) -> ParseResult<GenericBounds> {
    let path = parse_path(cx)?;
    Ok(vec![TraitRef { path }])
}

fn parse_const_arg(cx: &mut ParseCtxt) -> ParseResult<ConstArg> {
    let lo = cx.lo();
    let kind = if cx.peek(AnyLit) {
        let len = parse_int(cx)?;
        ConstArgKind::Lit(len)
    } else if cx.advance_if(Tok::Underscore) {
        ConstArgKind::Infer
    } else {
        return Err(cx.unexpected_token());
    };
    let hi = cx.hi();
    Ok(ConstArg { kind, span: cx.mk_span(lo, hi) })
}

/// ⟨path⟩ := ⟨segments⟩ ⟨ ( ⟨refine_arg⟩,* ) ⟩?
fn parse_path(cx: &mut ParseCtxt) -> ParseResult<Path> {
    let lo = cx.lo();
    let segments = parse_segments(cx)?;
    let refine =
        if cx.peek(OpenDelim(Parenthesis)) { parens(cx, Comma, parse_refine_arg)? } else { vec![] };
    let hi = cx.hi();
    Ok(Path { segments, refine, node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) })
}

/// ⟨segments⟩ := ⟨segment⟩ ⟨:: ⟨segment⟩ ⟩*
fn parse_segments(cx: &mut ParseCtxt) -> ParseResult<Vec<PathSegment>> {
    sep1(cx, Tok::PathSep, parse_segment)
}

/// ⟨segment⟩ := ⟨ident⟩ ⟨ < ⟨generic_arg⟩,* > ⟩?
fn parse_segment(cx: &mut ParseCtxt) -> ParseResult<PathSegment> {
    let ident = parse_ident(cx)?;
    let args = opt_angle(cx, Comma, parse_generic_arg)?;
    Ok(PathSegment { ident, node_id: cx.next_node_id(), args })
}

/// ⟨generic_arg⟩ := ⟨ty⟩ | ⟨ident⟩ = ⟨ty⟩
fn parse_generic_arg(cx: &mut ParseCtxt) -> ParseResult<GenericArg> {
    let kind = if cx.peek2(AnyIdent, Tok::Eq) {
        let ident = parse_ident(cx)?;
        cx.expect(Tok::Eq)?;
        let ty = parse_type(cx)?;
        GenericArgKind::Constraint(ident, ty)
    } else {
        GenericArgKind::Type(parse_type(cx)?)
    };
    Ok(GenericArg { kind, node_id: cx.next_node_id() })
}

/// ⟨refine_arg⟩ :=  @ ⟨ident⟩
///               |  # ⟨ident⟩
///               |  |⟨⟨refine_parm⟩,*| ⟨expr⟩
///               |  ⟨expr⟩
fn parse_refine_arg(cx: &mut ParseCtxt) -> ParseResult<RefineArg> {
    let lo = cx.lo();
    let arg = if cx.advance_if(Tok::At) {
        // @ ⟨ident⟩
        let bind = parse_ident(cx)?;
        let hi = cx.hi();
        RefineArg::Bind(bind, BindKind::At, cx.mk_span(lo, hi), cx.next_node_id())
    } else if cx.advance_if(Tok::Pound) {
        // # ⟨ident⟩
        let bind = parse_ident(cx)?;
        let hi = cx.hi();
        RefineArg::Bind(bind, BindKind::Pound, cx.mk_span(lo, hi), cx.next_node_id())
    } else if cx.advance_if(Caret) {
        let params = sep_until(cx, Comma, Caret, |cx| parse_refine_param(cx, false))?;
        cx.expect(Caret)?;
        let body = parse_expr(cx, true)?;
        let hi = cx.hi();
        RefineArg::Abs(params, body, cx.mk_span(lo, hi), cx.next_node_id())
    } else {
        // ⟨expr⟩
        RefineArg::Expr(parse_expr(cx, true)?)
    };
    Ok(arg)
}

/// ⟨refine_param⟩ := ⟨mode⟩? ⟨ident⟩ ⟨ : ⟨sort⟩ ⟩?    if !require_sort
///                 | ⟨mode⟩? ⟨ident⟩ : ⟨sort⟩         if require_sort
fn parse_refine_param(cx: &mut ParseCtxt, require_sort: bool) -> ParseResult<RefineParam> {
    let lo = cx.lo();
    let mode = parse_opt_param_mode(cx);
    let ident = parse_ident(cx)?;
    let sort = if require_sort {
        cx.expect(Tok::Colon)?;
        parse_sort(cx)?
    } else if cx.advance_if(Tok::Colon) {
        parse_sort(cx)?
    } else {
        Sort::Infer
    };
    let hi = cx.hi();
    Ok(RefineParam { mode, ident, sort, span: cx.mk_span(lo, hi), node_id: cx.next_node_id() })
}

/// ⟨mode⟩ := hrn | hdl
fn parse_opt_param_mode(cx: &mut ParseCtxt) -> Option<ParamMode> {
    if cx.advance_if(Tok::Hrn) {
        Some(ParamMode::Horn)
    } else if cx.advance_if(Tok::Hdl) {
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
        cx.tokens.advance_by(ntokens);
        if matches!(precedence, Precedence::Iff | Precedence::Implies | Precedence::Compare) {
            if let ExprKind::BinaryOp(op, ..) = &lhs.kind {
                if Precedence::of_binop(op) == precedence {
                    return Err(cx.cannot_be_chained(lo, cx.hi()));
                }
            }
        }
        let rhs = parse_binops(cx, precedence, allow_struct)?;
        let span = lhs.span.to(rhs.span);
        lhs = Expr {
            kind: ExprKind::BinaryOp(op, Box::new([lhs, rhs])),
            node_id: cx.next_node_id(),
            span,
        }
    }
    Ok(lhs)
}

/// ⟨unary_expr⟩ := - ⟨unary_expr⟩ | ! ⟨unary_expr⟩ | ⟨trailer_expr⟩
fn unary_expr(cx: &mut ParseCtxt, allow_struct: bool) -> ParseResult<Expr> {
    let lo = cx.lo();
    let kind = if cx.advance_if(Tok::Minus) {
        ExprKind::UnaryOp(UnOp::Neg, Box::new(unary_expr(cx, allow_struct)?))
    } else if cx.advance_if(Tok::Not) {
        ExprKind::UnaryOp(UnOp::Not, Box::new(unary_expr(cx, allow_struct)?))
    } else {
        return parse_trailer_expr(cx, allow_struct);
    };
    let hi = cx.hi();
    Ok(Expr { kind, node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) })
}

/// ⟨trailer_expr⟩ :=  ⟨epath⟩ . ⟨ident⟩
///                 |  ⟨ident⟩ ( ⟨expr⟩,* )
///                 |  ⟨atom⟩
///                 |  <⟨ty⟩ as ⟨path⟩> :: ⟨ident⟩ ( ⟨expr⟩,* )
fn parse_trailer_expr(cx: &mut ParseCtxt, allow_struct: bool) -> ParseResult<Expr> {
    if cx.advance_if(LAngle) {
        // <⟨ty⟩ as ⟨path⟩> :: ⟨ident⟩ ( ⟨expr⟩,* )
        let lo = cx.lo();
        let qself = parse_type(cx)?;
        cx.expect(Tok::As)?;
        let path = parse_path(cx)?;
        cx.expect(RAngle)?;
        cx.expect(Tok::PathSep)?;
        let name = parse_ident(cx)?;
        let args = parens(cx, Comma, |cx| parse_expr(cx, true))?;
        let kind = ExprKind::Alias(AliasReft { qself: Box::new(qself), path, name }, args);
        let hi = cx.hi();
        return Ok(Expr { kind, node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) });
    }

    let atom = parse_atom(cx, allow_struct)?;
    let lo = cx.lo();
    let kind = if cx.advance_if(Tok::Dot) {
        // ⟨epath⟩ . ⟨ident⟩
        let field = parse_ident(cx)?;
        if let ExprKind::Path(path) = atom.kind {
            ExprKind::Dot(path, field)
        } else {
            return Err(cx.unsupported_proj(atom.span));
        }
    } else if cx.peek(OpenDelim(Parenthesis)) {
        let args = parens(cx, Comma, |cx| parse_expr(cx, true))?;
        if let ExprKind::Path(path) = atom.kind
            && let [segment] = &path.segments[..]
        {
            // ⟨ident⟩ ( ⟨expr⟩,* )
            ExprKind::App(segment.ident, args)
        } else {
            return Err(cx.unsupported_callee(atom.span));
        }
    } else {
        // ⟨atom⟩
        return Ok(atom);
    };
    let hi = cx.hi();
    Ok(Expr { kind, node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) })
}

/// ⟨atom⟩ := ⟨if_expr⟩
///         | ⟨lit⟩
///         | ( ⟨expr⟩ )
///         | ⟨epath⟩
///         | ⟨epath⟩ { ⟨constructor_arg⟩,* }    if allow_struct
///         | { ⟨constructor_arg⟩,* }            if allow_struct
fn parse_atom(cx: &mut ParseCtxt, allow_struct: bool) -> ParseResult<Expr> {
    let lo = cx.lo();
    if cx.peek(Tok::If) {
        // ⟨if_expr⟩
        parse_if_expr(cx)
    } else if cx.peek(AnyLit) {
        // ⟨lit⟩
        parse_lit(cx)
    } else if cx.peek(OpenDelim(Parenthesis)) {
        delimited(cx, Parenthesis, |cx| parse_expr(cx, true))
    } else if cx.peek(AnyIdent) {
        let path = parse_expr_path(cx)?;
        let kind = if allow_struct && cx.peek(Tok::OpenDelim(Brace)) {
            // ⟨epath⟩ { ⟨constructor_arg⟩,* }
            let args = braces(cx, Comma, parse_constructor_arg)?;
            ExprKind::Constructor(Some(path), args)
        } else {
            // ⟨epath⟩
            ExprKind::Path(path)
        };
        let hi = cx.hi();
        Ok(Expr { kind, node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) })
    } else if allow_struct && cx.peek(OpenDelim(Brace)) {
        // { ⟨constructor_arg⟩,* }
        let args = braces(cx, Comma, parse_constructor_arg)?;
        let hi = cx.hi();
        Ok(Expr {
            kind: ExprKind::Constructor(None, args),
            node_id: cx.next_node_id(),
            span: cx.mk_span(lo, hi),
        })
    } else if cx.peek([Tok::Exists, Tok::Forall]) {
        parse_bounded_quantifier(cx)
    } else {
        Err(cx.unexpected_token())
    }
}

fn parse_bounded_quantifier(cx: &mut ParseCtxt) -> ParseResult<Expr> {
    let lo = cx.lo();
    let quant = if cx.advance_if(Tok::Forall) {
        QuantKind::Forall
    } else if cx.advance_if(Tok::Exists) {
        QuantKind::Exists
    } else {
        return Err(cx.unexpected_token());
    };
    let param = parse_refine_param(cx, false)?;
    cx.expect(Tok::In)?;
    let start = parse_int(cx)?;
    cx.expect(Tok::DotDot)?;
    let end = parse_int(cx)?;
    let body = parse_block_expr(cx)?;
    let hi = cx.hi();
    Ok(Expr {
        kind: ExprKind::BoundedQuant(quant, param, start..end, Box::new(body)),
        node_id: cx.next_node_id(),
        span: cx.mk_span(lo, hi),
    })
}

/// ⟨constructor_arg⟩ :=  ⟨ident⟩ : ⟨expr⟩ |  ..
fn parse_constructor_arg(cx: &mut ParseCtxt) -> ParseResult<ConstructorArg> {
    let lo = cx.lo();
    if cx.peek(AnyIdent) {
        let ident = parse_ident(cx)?;
        cx.expect(Tok::Colon)?;
        let expr = parse_expr(cx, true)?;
        let hi = cx.hi();
        Ok(ConstructorArg::FieldExpr(FieldExpr {
            ident,
            expr,
            node_id: cx.next_node_id(),
            span: cx.mk_span(lo, hi),
        }))
    } else if cx.advance_if(Tok::DotDot) {
        let spread = parse_expr(cx, true)?;
        let hi = cx.hi();
        Ok(ConstructorArg::Spread(Spread {
            expr: spread,
            node_id: cx.next_node_id(),
            span: cx.mk_span(lo, hi),
        }))
    } else {
        Err(cx.unexpected_token())
    }
}

/// ⟨lit⟩ := "a Rust literal like an integer or a boolean"
fn parse_lit(cx: &mut ParseCtxt) -> ParseResult<Expr> {
    if let (lo, Tok::Literal(lit), hi) = cx.at(0) {
        cx.advance();
        Ok(Expr {
            kind: ExprKind::Literal(lit),
            node_id: cx.next_node_id(),
            span: cx.mk_span(lo, hi),
        })
    } else {
        Err(cx.unexpected_token())
    }
}

/// ⟨epath⟩ := ⟨ident⟩ ⟨ :: ⟨ident⟩ ⟩*
fn parse_expr_path(cx: &mut ParseCtxt) -> ParseResult<ExprPath> {
    let lo = cx.lo();
    let segments = sep1(cx, Tok::PathSep, parse_expr_path_segment)?;
    let hi = cx.hi();
    Ok(ExprPath { segments, node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) })
}

fn parse_expr_path_segment(cx: &mut ParseCtxt) -> ParseResult<ExprPathSegment> {
    Ok(ExprPathSegment { ident: parse_ident(cx)?, node_id: cx.next_node_id() })
}

/// ⟨if_expr⟩ := if ⟨cond⟩ ⟨block_expr⟩ ⟨ else if ⟨cond⟩ ⟨block_expr⟩ ⟩* else ⟨block_expr⟩
fn parse_if_expr(cx: &mut ParseCtxt) -> ParseResult<Expr> {
    let mut branches = vec![];

    loop {
        let lo = cx.lo();
        cx.expect(Tok::If)?;
        let cond = parse_expr(cx, false)?;
        let then_ = parse_block_expr(cx)?;
        branches.push((lo, cond, then_));
        cx.expect(Tok::Else)?;

        if !cx.peek(Tok::If) {
            break;
        }
    }
    let mut else_ = parse_block_expr(cx)?;

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

/// ⟨block_expr⟩ := { ⟨expr⟩ }
fn parse_block_expr(cx: &mut ParseCtxt) -> ParseResult<Expr> {
    delimited(cx, Brace, |cx| parse_expr(cx, true))
}

fn parse_ident(cx: &mut ParseCtxt) -> ParseResult<Ident> {
    if let (lo, Tok::Ident(name), hi) = cx.at(0) {
        cx.advance();
        Ok(Ident { name, span: cx.mk_span(lo, hi) })
    } else {
        Err(cx.unexpected_token())
    }
}

fn parse_int<T: FromStr>(cx: &mut ParseCtxt) -> ParseResult<T> {
    if let Tok::Literal(lit) = cx.at(0).1 {
        if let LitKind::Integer = lit.kind {
            if let Ok(value) = lit.symbol.as_str().parse::<T>() {
                cx.advance();
                return Ok(value);
            }
        }
    }
    Err(cx.unexpected_token())
}

/// ⟨sort⟩ :=  ⟨base_sort⟩
///         |  ( ⟨base_sort⟩,* ) -> ⟨base_sort⟩
///         |  ⟨base_sort⟩ -> ⟨base_sort⟩
fn parse_sort(cx: &mut ParseCtxt) -> ParseResult<Sort> {
    if cx.peek(OpenDelim(Parenthesis)) {
        // ( ⟨base_sort⟩,* ) -> ⟨base_sort⟩
        let inputs = parens(cx, Comma, parse_base_sort)?;
        cx.expect(Tok::RArrow)?;
        let output = parse_base_sort(cx)?;
        Ok(Sort::Func { inputs, output })
    } else {
        let bsort = parse_base_sort(cx)?;
        if cx.advance_if(Tok::RArrow) {
            // ⟨base_sort⟩ -> ⟨base_sort⟩
            let output = parse_base_sort(cx)?;
            Ok(Sort::Func { inputs: vec![bsort], output })
        } else {
            // ⟨base_sort⟩
            Ok(Sort::Base(bsort))
        }
    }
}

/// ⟨base_sort⟩ := bitvec < ⟨u32⟩ >
///              | ⟨sort_path⟩ < ⟨base_sort⟩,* >
/// ⟨sort_path⟩ := ⟨ident⟩ ⟨ :: ⟨ident⟩ ⟩* < (⟨base_sort⟩,*) >
fn parse_base_sort(cx: &mut ParseCtxt) -> ParseResult<BaseSort> {
    if cx.advance_if(Tok::BitVec) {
        cx.expect(LAngle)?;
        let len = parse_int(cx)?;
        cx.expect(RAngle)?;
        Ok(BaseSort::BitVec(len))
    } else {
        let segments = sep1(cx, Tok::PathSep, parse_ident)?;
        let args = opt_angle(cx, Comma, parse_base_sort)?;
        let path = SortPath { segments, args, node_id: cx.next_node_id() };
        Ok(BaseSort::Path(path))
    }
}

fn opt_angle<R>(
    cx: &mut ParseCtxt,
    sep: Tok,
    parse: impl FnMut(&mut ParseCtxt) -> ParseResult<R>,
) -> ParseResult<Vec<R>> {
    if !cx.peek(LAngle) {
        return Ok(vec![]);
    }
    angle(cx, sep, parse)
}

fn angle<R>(
    cx: &mut ParseCtxt,
    sep: Tok,
    parse: impl FnMut(&mut ParseCtxt) -> ParseResult<R>,
) -> ParseResult<Vec<R>> {
    cx.expect(LAngle)?;
    let items = sep_until(cx, sep, RAngle, parse)?;
    cx.expect(RAngle)?;
    Ok(items)
}

fn delimited<R>(
    cx: &mut ParseCtxt,
    delim: Delimiter,
    parse: impl FnOnce(&mut ParseCtxt) -> ParseResult<R>,
) -> ParseResult<R> {
    cx.expect(OpenDelim(delim))?;
    let r = parse(cx)?;
    cx.expect(CloseDelim(delim))?;
    Ok(r)
}

fn brackets<R>(
    cx: &mut ParseCtxt,
    sep: Tok,
    parse: impl FnMut(&mut ParseCtxt) -> ParseResult<R>,
) -> ParseResult<Vec<R>> {
    Ok(punctuated(cx, Bracket, sep, parse)?.0)
}

fn parens<R>(
    cx: &mut ParseCtxt,
    sep: Tok,
    parse: impl FnMut(&mut ParseCtxt) -> ParseResult<R>,
) -> ParseResult<Vec<R>> {
    Ok(punctuated(cx, Parenthesis, sep, parse)?.0)
}

fn braces<R>(
    cx: &mut ParseCtxt,
    sep: Tok,
    parse: impl FnMut(&mut ParseCtxt) -> ParseResult<R>,
) -> ParseResult<Vec<R>> {
    Ok(punctuated(cx, Brace, sep, parse)?.0)
}

fn punctuated<R>(
    cx: &mut ParseCtxt,
    delim: Delimiter,
    sep: Tok,
    mut parse: impl FnMut(&mut ParseCtxt) -> ParseResult<R>,
) -> ParseResult<(Vec<R>, bool)> {
    cx.expect(OpenDelim(delim))?;
    let mut items = vec![];

    let mut trailing = false;
    while !cx.peek(CloseDelim(delim)) {
        items.push(parse(cx)?);

        trailing = cx.advance_if(sep);
        if !trailing {
            break;
        }
    }
    cx.expect(CloseDelim(delim))?;
    Ok((items, trailing))
}

/// Parses a list of one ore more items separated by the requested token. Parsing continues
/// until no separation token is found.
fn sep1<R>(
    cx: &mut ParseCtxt,
    sep: Tok,
    mut parse: impl FnMut(&mut ParseCtxt) -> ParseResult<R>,
) -> ParseResult<Vec<R>> {
    let mut items = vec![parse(cx)?];
    while cx.advance_if(sep) {
        items.push(parse(cx)?);
    }
    Ok(items)
}

/// Parses a list of zero or more items. Parsing continues until the requested `end` token
/// is reached. This does not consume the end token.
fn until<P: Peek + Copy, R>(
    cx: &mut ParseCtxt,
    end: P,
    mut parse: impl FnMut(&mut ParseCtxt) -> ParseResult<R>,
) -> ParseResult<Vec<R>> {
    let mut items = vec![];
    while !cx.peek(end) {
        items.push(parse(cx)?);
    }
    Ok(items)
}

/// Parses a list of zero or more items separated by a punctuation, with optional trailing
/// punctuation. Parsing continues until the requested `end` token is reached. This does not
/// consume the end token.
fn sep_until<E: Peek + Copy, R>(
    cx: &mut ParseCtxt,
    sep: Tok,
    end: E,
    mut parse: impl FnMut(&mut ParseCtxt) -> ParseResult<R>,
) -> ParseResult<Vec<R>> {
    let mut items = vec![];
    while !cx.peek(end) {
        items.push(parse(cx)?);
        if !cx.advance_if(sep) {
            break;
        }
    }
    Ok(items)
}

// Reference: https://doc.rust-lang.org/reference/expressions.html#expression-precedence
#[derive(Clone, Copy, PartialEq, PartialOrd)]
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
    #[expect(dead_code, reason = "leaving this here for when we support xor")]
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
            BinOp::BitAnd => Precedence::BitAnd,
            BinOp::BitShl | BinOp::BitShr => Precedence::Shift,
            BinOp::Add | BinOp::Sub => Precedence::Sum,
            BinOp::Mul | BinOp::Div | BinOp::Mod => Precedence::Product,
        }
    }
}

impl ParseCtxt<'_> {
    /// Returns the token (and span) at the requested position.
    fn at(&mut self, n: usize) -> (BytePos, Tok, BytePos) {
        self.tokens.at(n)
    }

    /// Looks at the next token in the underlying cursor to determine whether it matches the
    /// requested type of token. Does not advance the position of the cursor.
    fn peek<T: Peek>(&mut self, t: T) -> bool {
        t.peek_at(&mut self.tokens, 0)
    }

    /// Looks at the next two tokens
    fn peek2<T1: Peek, T2: Peek>(&mut self, t1: T1, t2: T2) -> bool {
        t1.peek_at(&mut self.tokens, 0) && t2.peek_at(&mut self.tokens, 1)
    }

    /// Looks at the next three tokens
    fn peek3<T1: Peek, T2: Peek, T3: Peek>(&mut self, t1: T1, t2: T2, t3: T3) -> bool {
        t1.peek_at(&mut self.tokens, 0)
            && t2.peek_at(&mut self.tokens, 1)
            && t3.peek_at(&mut self.tokens, 2)
    }

    /// Looks whether the next token matches a binary operation. In case of a match, returns
    /// the corresponding binary operation and its size in number of tokens. This function
    /// doesn't advance the position of the underlying cursor.
    fn peek_binop(&mut self) -> Option<(BinOp, usize)> {
        let op = match self.at(0).1 {
            Tok::Iff => (BinOp::Iff, 1),
            Tok::FatArrow => (BinOp::Imp, 1),
            Tok::OrOr => (BinOp::Or, 1),
            Tok::AndAnd => (BinOp::And, 1),
            Tok::EqEq => (BinOp::Eq, 1),
            Tok::Ne => (BinOp::Ne, 1),
            Tok::Lt => (BinOp::Lt, 1),
            Tok::Gt => (BinOp::Gt, 1),
            Tok::Le => (BinOp::Le, 1),
            Tok::Ge => (BinOp::Ge, 1),
            Tok::Caret => (BinOp::BitOr, 1),
            Tok::And => (BinOp::BitAnd, 1),
            Tok::LtFollowedByLt => (BinOp::BitShl, 2),
            Tok::GtFollowedByGt => (BinOp::BitShr, 2),
            Tok::Plus => (BinOp::Add, 1),
            Tok::Minus => (BinOp::Sub, 1),
            Tok::Star => (BinOp::Mul, 1),
            Tok::Slash => (BinOp::Div, 1),
            Tok::Percent => (BinOp::Mod, 1),
            _ => return None,
        };
        Some(op)
    }

    /// Advances the underlying cursor to the next token
    fn advance(&mut self) {
        self.tokens.advance();
    }

    /// Advances the underlying cursor by the requested number of tokens
    fn advance_by(&mut self, n: usize) {
        self.tokens.advance_by(n);
    }

    /// Looks at the next token and advances the cursor if it matches the requested type of
    /// token. Returns `true` if there was a match.
    fn advance_if<T: Peek>(&mut self, t: T) -> bool {
        if self.peek(t) {
            self.advance();
            true
        } else {
            false
        }
    }

    /// Looks at the next two tokens advacing the cursor if there's a match on both of them
    fn advance_if2<T1: Peek, T2: Peek>(&mut self, t1: T1, t2: T2) -> bool {
        if self.peek2(t1, t2) {
            self.advance_by(2);
            true
        } else {
            false
        }
    }

    /// If the next token matches the requested type of token advances the cursor, otherwise
    /// returns an `unexpected token` error.
    fn expect<T: Peek>(&mut self, t: T) -> ParseResult {
        if self.advance_if(t) { Ok(()) } else { Err(self.unexpected_token()) }
    }
}

/// A trait for testing whether a single token matches some rule. This is mainly implemented
/// for [`Token`] to test whether a token is equal to a specific token.
trait Peek {
    /// Returns true if the token at the requested position matches this peek rule
    fn peek_at(self, tokens: &mut Cursor, pos: usize) -> bool;
}

impl Peek for Tok {
    fn peek_at(self, tokens: &mut Cursor, pos: usize) -> bool {
        tokens.at(pos).1 == self
    }
}

/// A peekable struct that matches any identifier
struct AnyIdent;
impl Peek for AnyIdent {
    fn peek_at(self, tokens: &mut Cursor, pos: usize) -> bool {
        matches!(tokens.at(pos).1, Tok::Ident(_))
    }
}

/// A peekable struct that matches any literal
struct AnyLit;
impl Peek for AnyLit {
    fn peek_at(self, tokens: &mut Cursor, pos: usize) -> bool {
        matches!(tokens.at(pos).1, Tok::Literal(_))
    }
}

#[derive(Clone, Copy)]
struct LAngle;
impl Peek for LAngle {
    fn peek_at(self, tokens: &mut Cursor, pos: usize) -> bool {
        matches!(tokens.at(pos).1, Tok::LtFollowedByLt | Tok::Lt)
    }
}

#[derive(Clone, Copy)]
struct RAngle;
impl Peek for RAngle {
    fn peek_at(self, tokens: &mut Cursor, pos: usize) -> bool {
        matches!(tokens.at(pos).1, Tok::GtFollowedByGt | Tok::Gt)
    }
}

/// Use a string to match an identifier equal to it
impl Peek for &str {
    fn peek_at(self, tokens: &mut Cursor, pos: usize) -> bool {
        matches!(tokens.at(pos).1, Tok::Ident(sym) if sym.as_str() == self)
    }
}

/// An array can be used to match any token in a set
impl<T: Peek, const N: usize> Peek for [T; N] {
    fn peek_at(self, tokens: &mut Cursor, pos: usize) -> bool {
        self.into_iter().any(|t| t.peek_at(tokens, pos))
    }
}
