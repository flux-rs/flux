pub(crate) mod lookahead;
mod utils;
use std::{collections::HashSet, str::FromStr, vec};

use lookahead::{AnyIdent, AnyLit, LAngle, RAngle};
use utils::{
    angle, braces, brackets, delimited, opt_angle, parens, punctuated_until,
    punctuated_with_trailing, repeat_while, sep1, until,
};

use crate::{
    ParseCtxt, ParseError, ParseResult, Peek as _,
    lexer::{
        Delimiter::*,
        Token::{self as Tok, Caret, CloseDelim, Comma, OpenDelim},
    },
    surface::{
        Async, BaseSort, BaseTy, BaseTyKind, BinOp, BindKind, ConstArg, ConstArgKind,
        ConstructorArg, Ensures, Expr, ExprKind, ExprPath, ExprPathSegment, FieldExpr, FnInput,
        FnOutput, FnRetTy, FnSig, GenericArg, GenericArgKind, GenericBounds, GenericParam,
        GenericParamKind, Generics, Ident, ImplAssocReft, Indices, Item, LetDecl, LitKind,
        Mutability, ParamMode, Path, PathSegment, QualNames, Qualifier, QuantKind, RefineArg,
        RefineParam, RefineParams, Requires, RevealNames, Sort, SortDecl, SortPath, SpecFunc,
        Spread, TraitAssocReft, TraitRef, Ty, TyAlias, TyKind, UnOp, VariantDef, VariantRet,
        WhereBoundPredicate,
    },
};

/// ```text
///   yes ⟨ , reason = ⟨literal⟩ ⟩?
/// | no ⟨ , reason = ⟨literal⟩ ⟩?
/// | reason = ⟨literal⟩
/// ```
pub(crate) fn parse_yes_or_no_with_reason(cx: &mut ParseCtxt) -> ParseResult<bool> {
    let mut lookahead = cx.lookahead1();
    if lookahead.advance_if("yes") {
        if cx.advance_if(Tok::Comma) {
            parse_reason(cx)?;
        }
        Ok(true)
    } else if lookahead.advance_if("no") {
        if cx.advance_if(Tok::Comma) {
            parse_reason(cx)?;
        }
        Ok(false)
    } else if lookahead.peek("reason") {
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
    cx.expect("reason")?;
    cx.expect(Tok::Eq)?;
    cx.expect(AnyLit)
}

/// ```text
/// ⟨ident⟩,*
/// ```
pub(crate) fn parse_qual_names(cx: &mut ParseCtxt) -> ParseResult<QualNames> {
    let names = punctuated_until(cx, Comma, Tok::Eof, parse_ident)?;
    Ok(QualNames { names })
}

pub(crate) fn parse_reveal_names(cx: &mut ParseCtxt) -> ParseResult<RevealNames> {
    let names = punctuated_until(cx, Comma, Tok::Eof, parse_ident)?;
    Ok(RevealNames { names })
}

pub(crate) fn parse_generics(cx: &mut ParseCtxt) -> ParseResult<Generics> {
    let lo = cx.lo();
    let params = punctuated_until(cx, Comma, Tok::Eof, parse_generic_param)?;
    let hi = cx.hi();
    Ok(Generics { params, predicates: None, span: cx.mk_span(lo, hi) })
}

pub(crate) fn parse_flux_items(cx: &mut ParseCtxt) -> ParseResult<Vec<Item>> {
    until(cx, Tok::Eof, parse_flux_item)
}

fn parse_flux_item(cx: &mut ParseCtxt) -> ParseResult<Item> {
    let mut lookahead = cx.lookahead1();
    if lookahead.peek([Tok::Pound, Tok::Fn]) {
        parse_reft_func(cx).map(Item::FuncDef)
    } else if lookahead.peek([Tok::Local, Tok::Qualifier]) {
        parse_qualifier(cx).map(Item::Qualifier)
    } else if lookahead.peek(Tok::Opaque) {
        parse_sort_decl(cx).map(Item::SortDecl)
    } else {
        Err(lookahead.into_error())
    }
}

fn parse_hide_attr(cx: &mut ParseCtxt) -> ParseResult<bool> {
    if !cx.advance_if(Tok::Pound) {
        return Ok(false);
    }
    cx.expect(Tok::OpenDelim(Bracket))?;
    cx.expect("hide")?;
    cx.expect(Tok::CloseDelim(Bracket))?;
    Ok(true)
}

fn parse_reft_func(cx: &mut ParseCtxt) -> ParseResult<SpecFunc> {
    let hide = parse_hide_attr(cx)?;
    cx.expect(Tok::Fn)?;
    let name = parse_ident(cx)?;
    let sort_vars = opt_angle(cx, Comma, parse_ident)?;
    let params = parens(cx, Comma, |cx| parse_refine_param(cx, true))?;
    cx.expect(Tok::RArrow)?;
    let output = parse_sort(cx)?;
    let body = if cx.peek(OpenDelim(Brace)) {
        Some(parse_block(cx)?)
    } else {
        cx.expect(Tok::Semi)?;
        None
    };
    Ok(SpecFunc { name, sort_vars, params, output, body, hide })
}

fn parse_qualifier(cx: &mut ParseCtxt) -> ParseResult<Qualifier> {
    let lo = cx.lo();
    let local = cx.advance_if(Tok::Local);
    cx.expect(Tok::Qualifier)?;
    let name = parse_ident(cx)?;
    let params = parens(cx, Comma, |cx| parse_refine_param(cx, true))?;
    let expr = parse_block(cx)?;
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

/// ```text
/// ⟨trait_assoc_reft⟩ := fn ⟨ident⟩ ( ⟨refine_param⟩,* ) -> ⟨base_sort⟩ ;?
///                     | fn ⟨ident⟩ ( ⟨refine_param⟩,* ) -> ⟨base_sort⟩ ⟨block⟩
/// ```
fn parse_trait_assoc_reft(cx: &mut ParseCtxt) -> ParseResult<TraitAssocReft> {
    let lo = cx.lo();
    cx.expect(Tok::Fn)?;
    let name = parse_ident(cx)?;
    let params = parens(cx, Comma, |cx| parse_refine_param(cx, true))?;
    cx.expect(Tok::RArrow)?;
    let output = parse_base_sort(cx)?;
    let body = if cx.peek(OpenDelim(Brace)) {
        Some(parse_block(cx)?)
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

/// ```text
/// ⟨impl_assoc_reft⟩ := fn ⟨ident⟩ ( ⟨refine_param⟩,* ) -> ⟨base_sort⟩ ⟨block⟩
/// ```
fn parse_impl_assoc_reft(cx: &mut ParseCtxt) -> ParseResult<ImplAssocReft> {
    let lo = cx.lo();
    cx.expect(Tok::Fn)?;
    let name = parse_ident(cx)?;
    let params = parens(cx, Comma, |cx| parse_refine_param(cx, true))?;
    cx.expect(Tok::RArrow)?;
    let output = parse_base_sort(cx)?;
    let body = parse_block(cx)?;
    let hi = cx.hi();
    Ok(ImplAssocReft { name, params, output, body, span: cx.mk_span(lo, hi) })
}

/// ```text
/// ⟨refined_by⟩ := ⟨refine_param⟩,*
/// ```
pub(crate) fn parse_refined_by(cx: &mut ParseCtxt) -> ParseResult<RefineParams> {
    punctuated_until(cx, Comma, Tok::Eof, |cx| parse_refine_param(cx, true))
}

/// ```text
/// ⟨variant⟩ := ⟨fields⟩ -> ⟨variant_ret⟩
///            | ⟨fields⟩
///            | ⟨variant_ret⟩
/// ```
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

/// ```text
/// ⟨fields⟩ := ( ⟨ty⟩,* ) | { ⟨ty⟩,* }
/// ```
fn parse_fields(cx: &mut ParseCtxt) -> ParseResult<Vec<Ty>> {
    let mut lookahead = cx.lookahead1();
    if lookahead.peek(OpenDelim(Parenthesis)) {
        parens(cx, Comma, parse_type)
    } else if lookahead.peek(OpenDelim(Brace)) {
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
        let mut lookahead = cx.lookahead1();
        if lookahead.advance_if("type") {
            kind = GenericParamKind::Type;
        } else if lookahead.advance_if("base") {
            kind = GenericParamKind::Base;
        } else {
            return Err(lookahead.into_error());
        }
    };
    Ok(GenericParam { name, kind, node_id: cx.next_node_id() })
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
    // 2. Walk over inputs and transform
    let mut res = vec![];
    for input in inputs.into_iter() {
        if let FnInput::Ty(Some(ident), _, _) = &input
            && locs.contains(&ident)
        {
            // a known location: better be a mut or else, error!
            let FnInput::Ty(Some(ident), ty, id) = input else {
                return Err(invalid_ident_err(&ident)); //panic!("Expected a mutable reference to a type")
            };
            let TyKind::Ref(Mutability::Mut, inner_ty) = ty.kind else {
                return Err(invalid_ident_err(&ident)); //panic!("Expected a mutable reference to a type")
            };
            res.push(FnInput::StrgRef(ident, *inner_ty, id));
        } else {
            // not a known location, leave unchanged
            res.push(input)
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
    let inputs = parens(cx, Comma, parse_fn_input)?;
    let returns = parse_fn_ret(cx)?;
    let requires = parse_opt_requires(cx)?;
    let ensures = parse_opt_ensures(cx)?;
    let inputs = mut_as_strg(inputs, &ensures)?;
    generics.predicates = parse_opt_where(cx)?;
    cx.expect(Tok::Eof)?;
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
    if !cx.advance_if(Tok::Requires) {
        return Ok(vec![]);
    }
    punctuated_until(cx, Comma, [Tok::Ensures, Tok::Where, Tok::Eof], parse_requires_clause)
}

/// ```text
/// ⟨requires_clause⟩ := ⟨ forall ⟨refine_param⟩,+ . ⟩? ⟨expr⟩
/// ```
fn parse_requires_clause(cx: &mut ParseCtxt) -> ParseResult<Requires> {
    let mut params = vec![];
    if cx.advance_if(Tok::Forall) {
        params = sep1(cx, Comma, |cx| parse_refine_param(cx, false))?;
        cx.expect(Tok::Dot)?;
    }
    let pred = parse_expr(cx, true)?;
    Ok(Requires { params, pred })
}

/// ```text
/// ⟨ensures⟩ := ⟨ensures ⟨ensures_clause⟩,*⟩?
/// ```
fn parse_opt_ensures(cx: &mut ParseCtxt) -> ParseResult<Vec<Ensures>> {
    if !cx.advance_if(Tok::Ensures) {
        return Ok(vec![]);
    }
    punctuated_until(cx, Comma, [Tok::Where, Tok::Eof], parse_ensures_clause)
}

/// ```text
/// ⟨ensures_clause⟩ :=  ⟨ident⟩ : ⟨ty⟩
///                   |  ⟨expr⟩
/// ```
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
    Ok(Some(punctuated_until(cx, Comma, Tok::Eof, parse_where_bound)?))
}

fn parse_where_bound(cx: &mut ParseCtxt) -> ParseResult<WhereBoundPredicate> {
    let lo = cx.lo();
    let bounded_ty = parse_type(cx)?;
    cx.expect(Tok::Colon)?;
    let bounds = parse_generic_bounds(cx)?;
    let hi = cx.hi();
    Ok(WhereBoundPredicate { span: cx.mk_span(lo, hi), bounded_ty, bounds })
}

/// ```text
/// ⟨fn_ret⟩ := ⟨ -> ⟨ty⟩ ⟩?
/// ```
fn parse_fn_ret(cx: &mut ParseCtxt) -> ParseResult<FnRetTy> {
    if cx.advance_if(Tok::RArrow) {
        Ok(FnRetTy::Ty(parse_type(cx)?))
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
    if cx.peek2(AnyIdent, Tok::Colon) {
        let bind = parse_ident(cx)?;
        cx.expect(Tok::Colon)?;
        if cx.advance_if2(Tok::And, Tok::Strg) {
            // ⟨ident⟩ : &strg ⟨ty⟩
            Ok(FnInput::StrgRef(bind, parse_type(cx)?, cx.next_node_id()))
        } else if cx.peek(AnyIdent) {
            let path = parse_path(cx)?;
            if cx.peek3(OpenDelim(Brace), AnyIdent, Tok::Colon) {
                // ⟨ident⟩ : ⟨path⟩ { ⟨ident⟩ : ⟨expr⟩ }
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
            let ty = parse_type(cx)?;
            Ok(FnInput::Ty(Some(bind), ty, cx.next_node_id()))
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
    if cx.advance_if(Tok::Async) {
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
    let kind = if lookahead.advance_if(Tok::Underscore) {
        TyKind::Hole
    } else if lookahead.advance_if(OpenDelim(Parenthesis)) {
        // ( ⟨ty⟩,* )
        let (mut tys, trailing) =
            punctuated_with_trailing(cx, Comma, CloseDelim(Parenthesis), parse_type)?;
        cx.expect(CloseDelim(Parenthesis))?;
        if tys.len() == 1 && !trailing {
            return Ok(tys.remove(0));
        } else {
            TyKind::Tuple(tys)
        }
    } else if lookahead.peek(OpenDelim(Brace)) {
        delimited(cx, Brace, |cx| {
            if cx.peek2(AnyIdent, [Tok::Comma, Tok::Dot, Tok::Colon]) {
                // { ⟨refine_param⟩ ⟨,⟨refine_param⟩⟩* . ⟨ty⟩ | ⟨block_expr⟩ }
                parse_general_exists(cx)
            } else {
                // { ⟨ty⟩ | ⟨block_expr⟩ }
                let ty = parse_type(cx)?;
                cx.expect(Tok::Caret)?;
                let pred = parse_block_expr(cx)?;
                Ok(TyKind::Constr(pred, Box::new(ty)))
            }
        })?
    } else if lookahead.advance_if(Tok::And) {
        //  & mut? ⟨ty⟩
        let mutbl = if cx.advance_if(Tok::Mut) { Mutability::Mut } else { Mutability::Not };
        TyKind::Ref(mutbl, Box::new(parse_type(cx)?))
    } else if lookahead.advance_if(OpenDelim(Bracket)) {
        let ty = parse_type(cx)?;
        if cx.advance_if(Tok::Semi) {
            // [ ⟨ty⟩ ; ⟨const_arg⟩ ]
            let len = parse_const_arg(cx)?;
            cx.expect(CloseDelim(Bracket))?;
            TyKind::Array(Box::new(ty), len)
        } else {
            // [ ⟨ty⟩ ] ...
            cx.expect(CloseDelim(Bracket))?;
            let span = cx.mk_span(lo, cx.hi());
            let kind = BaseTyKind::Slice(Box::new(ty));
            return parse_bty_rhs(cx, BaseTy { kind, span });
        }
    } else if lookahead.advance_if(Tok::Impl) {
        // impl ⟨bounds⟩
        TyKind::ImplTrait(cx.next_node_id(), parse_generic_bounds(cx)?)
    } else if lookahead.peek(AnyIdent) {
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
    cx.expect(Tok::As)?;
    let mut segments = parse_segments(cx)?;
    cx.expect(RAngle)?;
    cx.expect(Tok::PathSep)?;
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
    let params = sep1(cx, Comma, |cx| parse_refine_param(cx, false))?;
    cx.expect(Tok::Dot)?;
    let ty = parse_type(cx)?;
    let pred = if cx.advance_if(Tok::Caret) { Some(parse_block_expr(cx)?) } else { None };
    Ok(TyKind::GeneralExists { params, ty: Box::new(ty), pred })
}

/// ```text
///    ⟨bty⟩ [ ⟨refine_arg⟩,* ]
/// |  ⟨bty⟩ { ⟨ident⟩ : ⟨block_expr⟩ }
/// |  ⟨bty⟩
/// ```
fn parse_bty_rhs(cx: &mut ParseCtxt, bty: BaseTy) -> ParseResult<Ty> {
    let lo = bty.span.lo();
    if cx.peek(OpenDelim(Bracket)) {
        // ⟨bty⟩ [ ⟨refine_arg⟩,* ]
        let indices = parse_indices(cx)?;
        let hi = cx.hi();
        let kind = TyKind::Indexed { bty, indices };
        Ok(Ty { kind, node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) })
    } else if cx.peek(OpenDelim(Brace)) {
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
        cx.expect(Tok::Colon)?;
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

fn parse_generic_bounds(cx: &mut ParseCtxt) -> ParseResult<GenericBounds> {
    let path = parse_path(cx)?;
    Ok(vec![TraitRef { path }])
}

fn parse_const_arg(cx: &mut ParseCtxt) -> ParseResult<ConstArg> {
    let lo = cx.lo();
    let mut lookahead = cx.lookahead1();
    let kind = if lookahead.peek(AnyLit) {
        let len = parse_int(cx)?;
        ConstArgKind::Lit(len)
    } else if lookahead.advance_if(Tok::Underscore) {
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
        if cx.peek(OpenDelim(Parenthesis)) { parens(cx, Comma, parse_refine_arg)? } else { vec![] };
    let hi = cx.hi();
    Ok(Path { segments, refine, node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) })
}

/// ```text
/// ⟨segments⟩ := ⟨segment⟩ ⟨:: ⟨segment⟩ ⟩*
/// ```
fn parse_segments(cx: &mut ParseCtxt) -> ParseResult<Vec<PathSegment>> {
    sep1(cx, Tok::PathSep, parse_segment)
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

/// ```text
/// ⟨refine_arg⟩ :=  @ ⟨ident⟩
///               |  # ⟨ident⟩
///               |  |⟨⟨refine_parm⟩,*| ⟨expr⟩
///               |  ⟨expr⟩
/// ```
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
        let params = punctuated_until(cx, Comma, Caret, |cx| parse_refine_param(cx, false))?;
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

/// ```text
/// ⟨refine_param⟩ := ⟨mode⟩? ⟨ident⟩ ⟨ : ⟨sort⟩ ⟩?    if !require_sort
///                 | ⟨mode⟩? ⟨ident⟩ : ⟨sort⟩         if require_sort
/// ```
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

/// ```text
/// ⟨mode⟩ := ⟨ hrn | hdl ⟩?
/// ```
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
        cx.advance_by(ntokens);
        let next = match precedence.associativity() {
            Associativity::Right => precedence,
            Associativity::Left => precedence.next(),
            Associativity::None => {
                if let ExprKind::BinaryOp(op, ..) = &lhs.kind {
                    if Precedence::of_binop(op) == precedence {
                        return Err(cx.cannot_be_chained(lo, cx.hi()));
                    }
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

/// ```text
/// ⟨trailer_expr⟩ :=  ⟨trailer⟩ . ⟨ident⟩
///                 |  ⟨trailer⟩ ( ⟨expr⟩,* )
///                 |  ⟨atom⟩
/// ```
fn parse_trailer_expr(cx: &mut ParseCtxt, allow_struct: bool) -> ParseResult<Expr> {
    let lo = cx.lo();
    let mut e = parse_atom(cx, allow_struct)?;
    loop {
        let kind = if cx.advance_if(Tok::Dot) {
            // ⟨trailer⟩ . ⟨ident⟩
            let field = parse_ident(cx)?;
            ExprKind::Dot(Box::new(e), field)
        } else if cx.peek(OpenDelim(Parenthesis)) {
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
///         | ⟨epath⟩ { ⟨constructor_arg⟩,* }    if allow_struct
///         | { ⟨constructor_arg⟩,* }            if allow_struct
/// ```
fn parse_atom(cx: &mut ParseCtxt, allow_struct: bool) -> ParseResult<Expr> {
    let lo = cx.lo();
    let mut lookahead = cx.lookahead1();
    if lookahead.peek(Tok::If) {
        // ⟨if_expr⟩
        parse_if_expr(cx)
    } else if lookahead.peek(AnyLit) {
        // ⟨lit⟩
        parse_lit(cx)
    } else if lookahead.peek(OpenDelim(Parenthesis)) {
        delimited(cx, Parenthesis, |cx| parse_expr(cx, true))
    } else if lookahead.peek(AnyIdent) {
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
    } else if allow_struct && lookahead.peek(OpenDelim(Brace)) {
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
        cx.expect(Tok::As)?;
        let path = parse_path(cx)?;
        cx.expect(RAngle)?;
        cx.expect(Tok::PathSep)?;
        let name = parse_ident(cx)?;
        let hi = cx.hi();
        let kind = ExprKind::AssocReft(Box::new(qself), path, name);
        return Ok(Expr { kind, node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) });
    } else if lookahead.peek([Tok::Exists, Tok::Forall]) {
        parse_bounded_quantifier(cx)
    } else {
        Err(lookahead.into_error())
    }
}

/// ```text
/// ⟨bounded_quant⟩ := forall ⟨refine_param⟩ in ⟨int⟩..⟨int⟩ ⟨block⟩
///                  | exists ⟨refine_param⟩ in ⟨int⟩..⟨int⟩ ⟨block⟩
/// ```
fn parse_bounded_quantifier(cx: &mut ParseCtxt) -> ParseResult<Expr> {
    let lo = cx.lo();
    let mut lookahead = cx.lookahead1();
    let quant = if lookahead.advance_if(Tok::Forall) {
        QuantKind::Forall
    } else if lookahead.advance_if(Tok::Exists) {
        QuantKind::Exists
    } else {
        return Err(lookahead.into_error());
    };
    let param = parse_refine_param(cx, false)?;
    cx.expect(Tok::In)?;
    let start = parse_int(cx)?;
    cx.expect(Tok::DotDot)?;
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
    if lookahead.peek(AnyIdent) {
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
    } else if lookahead.advance_if(Tok::DotDot) {
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
    let segments = sep1(cx, Tok::PathSep, parse_expr_path_segment)?;
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
        cx.expect(Tok::If)?;
        let cond = parse_expr(cx, false)?;
        let then_ = parse_block(cx)?;
        branches.push((lo, cond, then_));
        cx.expect(Tok::Else)?;

        if !cx.peek(Tok::If) {
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

/// `⟨block_expr⟩ = ⟨let_decl⟩* ⟨expr⟩`
fn parse_block_expr(cx: &mut ParseCtxt) -> ParseResult<Expr> {
    let lo = cx.lo();
    let decls = repeat_while(cx, Tok::Let, parse_let_decl)?;
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
    cx.expect(Tok::Let)?;
    let param = parse_refine_param(cx, false)?;
    cx.expect(Tok::Eq)?;
    let init = parse_expr(cx, true)?;
    cx.expect(Tok::Semi)?;
    Ok(LetDecl { param, init })
}

/// `⟨block⟩ := { ⟨let_decls⟩ ⟨expr⟩ }`
fn parse_block(cx: &mut ParseCtxt) -> ParseResult<Expr> {
    delimited(cx, Brace, parse_block_expr)
}

/// ```text
/// ⟨lit⟩ := "a Rust literal like an integer or a boolean"
/// ```
fn parse_lit(cx: &mut ParseCtxt) -> ParseResult<Expr> {
    if let (lo, Tok::Literal(lit), hi) = cx.at(0) {
        cx.advance();
        Ok(Expr {
            kind: ExprKind::Literal(lit),
            node_id: cx.next_node_id(),
            span: cx.mk_span(lo, hi),
        })
    } else {
        Err(cx.unexpected_token(AnyLit.display().collect()))
    }
}

fn parse_ident(cx: &mut ParseCtxt) -> ParseResult<Ident> {
    if let (lo, Tok::Ident(name), hi) = cx.at(0) {
        cx.advance();
        Ok(Ident { name, span: cx.mk_span(lo, hi) })
    } else {
        Err(cx.unexpected_token(AnyIdent.display().collect()))
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
    Err(cx.unexpected_token(vec![std::any::type_name::<T>()]))
}

/// ```text
/// ⟨sort⟩ :=  ⟨base_sort⟩
///         |  ( ⟨base_sort⟩,* ) -> ⟨base_sort⟩
///         |  ⟨base_sort⟩ -> ⟨base_sort⟩
/// ```
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

/// ```text
/// ⟨base_sort⟩ := bitvec < ⟨u32⟩ >
///              | ⟨sort_path⟩ < ⟨base_sort⟩,* >
///              | < ⟨ty⟩ as ⟨path⟩ > :: ⟨segment⟩
/// ⟨sort_path⟩ := ⟨ident⟩ ⟨ :: ⟨ident⟩ ⟩* < (⟨base_sort⟩,*) >
/// ```
fn parse_base_sort(cx: &mut ParseCtxt) -> ParseResult<BaseSort> {
    if cx.advance_if(Tok::BitVec) {
        // bitvec < ⟨u32⟩ >
        cx.expect(LAngle)?;
        let len = parse_int(cx)?;
        cx.expect(RAngle)?;
        Ok(BaseSort::BitVec(len))
    } else if cx.advance_if(LAngle) {
        // < ⟨ty⟩ as ⟨path⟩ > :: ⟨segment⟩
        let qself = parse_type(cx)?;
        cx.expect(Tok::As)?;
        let mut path = parse_path(cx)?;
        cx.expect(RAngle)?;
        cx.expect(Tok::PathSep)?;
        path.segments.push(parse_segment(cx)?);
        Ok(BaseSort::SortOf(Box::new(qself), path))
    } else {
        // ⟨sort_path⟩ < ⟨base_sort⟩,* >
        let segments = sep1(cx, Tok::PathSep, parse_ident)?;
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
