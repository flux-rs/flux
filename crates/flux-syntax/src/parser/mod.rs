pub(crate) mod lookahead;
mod utils;
use std::{collections::HashSet, str::FromStr, vec};

use lookahead::{AnyIdent, AnyLit, LAngle, RAngle};
use rustc_span::sym::Output;
use utils::{
    angle, braces, brackets, delimited, opt_angle, parens, punctuated_until,
    punctuated_with_trailing, repeat_while, sep1, until,
};

use crate::{
    ParseCtxt, ParseError, ParseResult,
    lexer::{
        Delimiter::*,
        Token,
        TokenKind::{Caret, Comma},
        token,
    },
    parser::lookahead::PeekDescr as _,
    surface::{
        Async, BaseSort, BaseTy, BaseTyKind, BinOp, BindKind, ConstArg, ConstArgKind,
        ConstructorArg, Ensures, Expr, ExprKind, ExprPath, ExprPathSegment, FieldExpr, FnInput,
        FnOutput, FnRetTy, FnSig, GenericArg, GenericArgKind, GenericBounds, GenericParam,
        Generics, Ident, ImplAssocReft, Indices, Item, LetDecl, LitKind, Mutability, ParamMode,
        Path, PathSegment, PrimOpProp, QualNames, Qualifier, QuantKind, RefineArg, RefineParam,
        RefineParams, Requires, RevealNames, Sort, SortDecl, SortPath, SpecFunc, Spread,
        TraitAssocReft, TraitRef, Ty, TyAlias, TyKind, UnOp, VariantDef, VariantRet,
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
        if cx.advance_if(token::Comma) {
            parse_reason(cx)?;
        }
        Ok(true)
    } else if lookahead.advance_if("no") {
        if cx.advance_if(token::Comma) {
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
    cx.expect(token::Eq)?;
    cx.expect(AnyLit)
}

/// ```text
/// ⟨ident⟩,*
/// ```
pub(crate) fn parse_qual_names(cx: &mut ParseCtxt) -> ParseResult<QualNames> {
    let names = punctuated_until(cx, Comma, token::Eof, parse_ident)?;
    Ok(QualNames { names })
}

pub(crate) fn parse_reveal_names(cx: &mut ParseCtxt) -> ParseResult<RevealNames> {
    let names = punctuated_until(cx, Comma, token::Eof, parse_ident)?;
    Ok(RevealNames { names })
}

pub(crate) fn parse_flux_items(cx: &mut ParseCtxt) -> ParseResult<Vec<Item>> {
    until(cx, token::Eof, parse_flux_item)
}

fn parse_flux_item(cx: &mut ParseCtxt) -> ParseResult<Item> {
    let mut lookahead = cx.lookahead1();
    if lookahead.peek(token::Pound) || lookahead.peek(token::Fn) {
        parse_reft_func(cx).map(Item::FuncDef)
    } else if lookahead.peek(token::Local) || lookahead.peek(token::Qualifier) {
        parse_qualifier(cx).map(Item::Qualifier)
    } else if lookahead.peek(token::Opaque) {
        parse_sort_decl(cx).map(Item::SortDecl)
    } else if lookahead.peek(token::Property) {
        parse_prim_property(cx).map(Item::PrimProp)
    } else {
        Err(lookahead.into_error())
    }
}

fn parse_hide_attr(cx: &mut ParseCtxt) -> ParseResult<bool> {
    if !cx.advance_if(token::Pound) {
        return Ok(false);
    }
    cx.expect(token::OpenBracket)?;
    cx.expect("hide")?;
    cx.expect(token::CloseBracket)?;
    Ok(true)
}

fn parse_reft_func(cx: &mut ParseCtxt) -> ParseResult<SpecFunc> {
    let hide = parse_hide_attr(cx)?;
    cx.expect(token::Fn)?;
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

fn parse_qualifier(cx: &mut ParseCtxt) -> ParseResult<Qualifier> {
    let lo = cx.lo();
    let local = cx.advance_if(token::Local);
    cx.expect(token::Qualifier)?;
    let name = parse_ident(cx)?;
    let params = parens(cx, Comma, |cx| parse_refine_param(cx, RequireSort::Yes))?;
    let expr = parse_block(cx)?;
    let hi = cx.hi();
    Ok(Qualifier { global: !local, name, params, expr, span: cx.mk_span(lo, hi) })
}

fn parse_sort_decl(cx: &mut ParseCtxt) -> ParseResult<SortDecl> {
    cx.expect(token::Opaque)?;
    cx.expect(token::Sort)?;
    let name = parse_ident(cx)?;
    cx.expect(token::Semi)?;
    Ok(SortDecl { name })
}

fn parse_binop(cx: &mut ParseCtxt) -> ParseResult<BinOp> {
    let (op, ntokens) = cx
        .peek_binop()
        .ok_or_else(|| cx.unexpected_token(vec!["binary operator"]))?;
    cx.advance_by(ntokens);
    Ok(op)
}

fn parse_prim_property(cx: &mut ParseCtxt) -> ParseResult<PrimOpProp> {
    let lo = cx.lo();
    cx.expect(token::Property)?;

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
    let final_ = cx.advance_if("final");
    cx.expect(token::Fn)?;
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
    cx.expect(token::Fn)?;
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
pub(crate) fn parse_variant(cx: &mut ParseCtxt) -> ParseResult<VariantDef> {
    let lo = cx.lo();
    let mut fields = vec![];
    let mut ret = None;
    if cx.peek(token::OpenParen) || cx.peek(token::OpenBrace) {
        fields = parse_fields(cx)?;
        if cx.advance_if(token::RArrow) {
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
    cx.expect(token::Type)?;
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
pub(crate) fn parse_fn_sig(cx: &mut ParseCtxt) -> ParseResult<FnSig> {
    let lo = cx.lo();
    let asyncness = parse_asyncness(cx);
    cx.expect(token::Fn)?;
    let ident = if cx.peek(AnyIdent) { Some(parse_ident(cx)?) } else { None };
    let mut generics = parse_opt_generics(cx)?;
    let params = if cx.peek(token::OpenBracket) {
        brackets(cx, Comma, |cx| parse_refine_param(cx, RequireSort::Opt))?
    } else {
        vec![]
    };
    let inputs = parens(cx, Comma, parse_fn_input)?;
    let returns = parse_fn_ret(cx)?;
    let requires = parse_opt_requires(cx)?;
    let ensures = parse_opt_ensures(cx)?;
    let inputs = mut_as_strg(inputs, &ensures)?;
    generics.predicates = parse_opt_where(cx)?;
    cx.expect(token::Eof)?;
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
    if !cx.advance_if(token::Requires) {
        return Ok(vec![]);
    }
    punctuated_until(cx, Comma, [token::Ensures, token::Where, token::Eof], parse_requires_clause)
}

/// ```text
/// ⟨requires_clause⟩ := ⟨ forall ⟨refine_param⟩,+ . ⟩? ⟨expr⟩
/// ```
fn parse_requires_clause(cx: &mut ParseCtxt) -> ParseResult<Requires> {
    let mut params = vec![];
    if cx.advance_if(token::Forall) {
        params = sep1(cx, Comma, |cx| parse_refine_param(cx, RequireSort::Opt))?;
        cx.expect(token::Dot)?;
    }
    let pred = parse_expr(cx, true)?;
    Ok(Requires { params, pred })
}

/// ```text
/// ⟨ensures⟩ := ⟨ensures ⟨ensures_clause⟩,*⟩?
/// ```
fn parse_opt_ensures(cx: &mut ParseCtxt) -> ParseResult<Vec<Ensures>> {
    if !cx.advance_if(token::Ensures) {
        return Ok(vec![]);
    }
    punctuated_until(cx, Comma, [token::Where, token::Eof], parse_ensures_clause)
}

/// ```text
/// ⟨ensures_clause⟩ :=  ⟨ident⟩ : ⟨ty⟩
///                   |  ⟨expr⟩
/// ```
fn parse_ensures_clause(cx: &mut ParseCtxt) -> ParseResult<Ensures> {
    if cx.peek2(AnyIdent, token::Colon) {
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
    if !cx.advance_if(token::Where) {
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
    if cx.peek2(AnyIdent, token::Colon) {
        let bind = parse_ident(cx)?;
        cx.expect(token::Colon)?;
        if cx.advance_if2(token::And, token::Strg) {
            // ⟨ident⟩ : &strg ⟨ty⟩
            Ok(FnInput::StrgRef(bind, parse_type(cx)?, cx.next_node_id()))
        } else if cx.peek(AnyIdent) {
            let path = parse_path(cx)?;
            if cx.peek3(token::OpenBrace, AnyIdent, token::Colon) {
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
    if cx.advance_if(token::Async) {
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
    let kind = if lookahead.advance_if(token::Underscore) {
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
            if cx.peek2(AnyIdent, [token::Comma, token::Dot, token::Colon]) {
                // { ⟨refine_param⟩ ⟨,⟨refine_param⟩⟩* . ⟨ty⟩ | ⟨block_expr⟩ }
                parse_general_exists(cx)
            } else {
                // { ⟨ty⟩ | ⟨block_expr⟩ }
                let ty = parse_type(cx)?;
                cx.expect(token::Caret)?;
                let pred = parse_block_expr(cx)?;
                Ok(TyKind::Constr(pred, Box::new(ty)))
            }
        })?
    } else if lookahead.advance_if(token::And) {
        //  & mut? ⟨ty⟩
        let mutbl = if cx.advance_if(token::Mut) { Mutability::Mut } else { Mutability::Not };
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
    } else if lookahead.advance_if(token::Impl) {
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
    cx.expect(token::As)?;
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
    let params = sep1(cx, Comma, |cx| parse_refine_param(cx, RequireSort::Opt))?;
    cx.expect(token::Dot)?;
    let ty = parse_type(cx)?;
    let pred = if cx.advance_if(token::Caret) { Some(parse_block_expr(cx)?) } else { None };
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
    let is_fn = cx.peek(["FnOnce", "FnMut", "Fn"]);
    let path = if is_fn { parse_fn_bound_path(cx)? } else { parse_path(cx)? };
    Ok(vec![TraitRef { path, node_id: cx.next_node_id() }])
}

fn parse_const_arg(cx: &mut ParseCtxt) -> ParseResult<ConstArg> {
    let lo = cx.lo();
    let mut lookahead = cx.lookahead1();
    let kind = if lookahead.peek(AnyLit) {
        let len = parse_int(cx)?;
        ConstArgKind::Lit(len)
    } else if lookahead.advance_if(token::Underscore) {
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
    let kind = if cx.peek2(AnyIdent, token::Eq) {
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
    } else if cx.advance_if(token::Pound) {
        // # ⟨ident⟩
        let bind = parse_ident(cx)?;
        let hi = cx.hi();
        RefineArg::Bind(bind, BindKind::Pound, cx.mk_span(lo, hi), cx.next_node_id())
    } else if cx.advance_if(Caret) {
        let params =
            punctuated_until(cx, Comma, Caret, |cx| parse_refine_param(cx, RequireSort::Opt))?;
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

enum RequireSort {
    /// definitely require a sort
    Yes,
    /// don't require it, can use `Infer`
    Opt,
    /// definitely do not want a sort!
    No,
}

fn parse_sort_if_required(cx: &mut ParseCtxt, require_sort: RequireSort) -> ParseResult<Sort> {
    match require_sort {
        RequireSort::No => Ok(Sort::Infer),
        RequireSort::Opt => {
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
/// ⟨refine_param⟩ := ⟨mode⟩? ⟨ident⟩ ⟨ : ⟨sort⟩ ⟩?    if require_sort is Opt
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
    if cx.advance_if(token::Hrn) {
        Some(ParamMode::Horn)
    } else if cx.advance_if(token::Hdl) {
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
/// ```
fn parse_atom(cx: &mut ParseCtxt, allow_struct: bool) -> ParseResult<Expr> {
    let lo = cx.lo();
    let mut lookahead = cx.lookahead1();
    if lookahead.peek(token::If) {
        // ⟨if_expr⟩
        parse_if_expr(cx)
    } else if lookahead.peek(AnyLit) {
        // ⟨lit⟩
        parse_lit(cx)
    } else if lookahead.peek(token::OpenParen) {
        delimited(cx, Parenthesis, |cx| parse_expr(cx, true))
    } else if lookahead.peek(AnyIdent) {
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
        cx.expect(token::As)?;
        let path = parse_path(cx)?;
        cx.expect(RAngle)?;
        cx.expect(token::PathSep)?;
        let name = parse_ident(cx)?;
        let hi = cx.hi();
        let kind = ExprKind::AssocReft(Box::new(qself), path, name);
        Ok(Expr { kind, node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) })
    } else if lookahead.peek(token::OpenBracket) {
        parse_prim_uif(cx)
    } else if lookahead.peek(token::Exists) || lookahead.peek(token::Forall) {
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
    let quant = if lookahead.advance_if(token::Forall) {
        QuantKind::Forall
    } else if lookahead.advance_if(token::Exists) {
        QuantKind::Exists
    } else {
        return Err(lookahead.into_error());
    };
    let param = parse_refine_param(cx, RequireSort::Opt)?;
    cx.expect(token::In)?;
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
    if lookahead.peek(AnyIdent) {
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
        cx.expect(token::If)?;
        let cond = parse_expr(cx, false)?;
        let then_ = parse_block(cx)?;
        branches.push((lo, cond, then_));
        cx.expect(token::Else)?;

        if !cx.peek(token::If) {
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
    let decls = repeat_while(cx, token::Let, parse_let_decl)?;
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
    cx.expect(token::Let)?;
    let param = parse_refine_param(cx, RequireSort::Opt)?;
    cx.expect(token::Eq)?;
    let init = parse_expr(cx, true)?;
    cx.expect(token::Semi)?;
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
    if let Token { kind: token::Literal(lit), lo, hi } = cx.at(0) {
        cx.advance();
        Ok(Expr {
            kind: ExprKind::Literal(lit),
            node_id: cx.next_node_id(),
            span: cx.mk_span(lo, hi),
        })
    } else {
        Err(cx.unexpected_token(vec![AnyLit.descr()]))
    }
}

fn parse_ident(cx: &mut ParseCtxt) -> ParseResult<Ident> {
    if let Token { kind: token::Ident(name), lo, hi } = cx.at(0) {
        cx.advance();
        Ok(Ident { name, span: cx.mk_span(lo, hi) })
    } else {
        Err(cx.unexpected_token(vec![AnyIdent.descr()]))
    }
}

fn parse_int<T: FromStr>(cx: &mut ParseCtxt) -> ParseResult<T> {
    if let token::Literal(lit) = cx.at(0).kind
        && let LitKind::Integer = lit.kind
        && let Ok(value) = lit.symbol.as_str().parse::<T>()
    {
        cx.advance();
        return Ok(value);
    }

    Err(cx.unexpected_token(vec![std::any::type_name::<T>()]))
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
    if cx.advance_if(token::BitVec) {
        // bitvec < ⟨u32⟩ >
        cx.expect(LAngle)?;
        let len = parse_int(cx)?;
        cx.expect(RAngle)?;
        Ok(BaseSort::BitVec(len))
    } else if cx.advance_if(LAngle) {
        // < ⟨ty⟩ as ⟨path⟩ > :: ⟨segment⟩
        let qself = parse_type(cx)?;
        cx.expect(token::As)?;
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
