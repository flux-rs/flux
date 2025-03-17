use std::str::FromStr;

use crate::{
    ParseCtxt, ParseError,
    lexer::{
        Delimiter::{self, *},
        Token::{self as Tok, Caret, CloseDelim, Comma, OpenDelim},
    },
    surface::{
        AliasReft, Async, BaseSort, BaseTy, BaseTyKind, BinOp, BindKind, ConstArg, ConstArgKind,
        ConstructorArg, Ensures, Expr, ExprKind, ExprPath, ExprPathSegment, FieldExpr, FnInput,
        FnOutput, FnRetTy, FnSig, GenericArg, GenericArgKind, GenericBounds, GenericParam,
        GenericParamKind, Generics, Ident, ImplAssocReft, Indices, Item, LitKind, Mutability,
        ParamMode, Path, PathSegment, QualNames, Qualifier, RefineArg, RefineParam, RefineParams,
        Requires, Sort, SortDecl, SortPath, SpecFunc, Spread, TraitAssocReft, TraitRef, Ty,
        TyAlias, TyKind, UnOp, VariantDef, VariantRet, WhereBoundPredicate,
    },
};

macro_rules! advance_if {
    ($cx:expr, $($pat:pat),+) => {{
        let tokens = &mut $cx.cursor;
        let mut idx = 0;
        let mut res = true;
        #[allow(unused_assignments)]
        {$(
            res &= matches!(tokens.at(idx), $pat);
            idx += 1;
        )+}
        if res {
            tokens.advance_by(idx);
        }
        res
    }};
}

macro_rules! expect {
    ($cx:expr, $pat:pat $(if $guard:expr)?) => {{
        expect!($cx, $pat $(if $guard)? => ())
    }};
    ($cx:expr, $pat:pat $(if $guard:expr)? => $arm:expr) => {{
        let tokens = &mut $cx.cursor;
        let tok = tokens.next();
        match tok {
            $pat $(if $guard)? => Ok($arm),
            _ => todo!("unexpected token {}", tokens.debug(10))
        }
    }};
}

#[macro_export]
macro_rules! peek {
    ($cx:expr, $($pat:pat),+) => {{
        let tokens = &mut $cx.cursor;
        let mut idx = 0;
        let mut res = true;
        #[allow(unused_assignments)]
        {$(
            res &= matches!(tokens.at(idx), $pat);
            idx += 1;
        )+}
        res
    }};
}

type Result<T = ()> = std::result::Result<T, ParseError>;

pub(crate) fn parse_yes_or_no_with_reason(cx: &mut ParseCtxt) -> Result<bool> {
    let ident = expect!(cx, Tok::Ident(ident) => ident)?;
    let yes = match ident.as_str() {
        s @ ("yes" | "no") => {
            if advance_if!(cx, Tok::Comma) {
                expect!(cx, Tok::Ident(sym) if sym.as_str() == "reason")?;
                expect!(cx, Tok::Eq)?;
                expect!(cx, Tok::Literal(_))?;
            }
            s == "yes"
        }
        "reason" => {
            expect!(cx, Tok::Eq)?;
            expect!(cx, Tok::Literal(_))?;
            true
        }
        _ => todo!("unexpected token"),
    };
    Ok(yes)
}

pub(crate) fn parse_qual_names(cx: &mut ParseCtxt) -> Result<QualNames> {
    let names = terminated(cx, Comma, Tok::Eof, parse_ident)?;
    Ok(QualNames { names })
}

pub(crate) fn parse_generics(cx: &mut ParseCtxt) -> Result<Generics> {
    let lo = cx.lo();
    let params = terminated(cx, Comma, Tok::Eof, parse_generic_param)?;
    let hi = cx.hi();
    Ok(Generics { params, predicates: None, span: cx.mk_span(lo, hi) })
}

pub(crate) fn parse_flux_items(cx: &mut ParseCtxt) -> Result<Vec<Item>> {
    let mut items = vec![];
    while !peek!(cx, Tok::Eof) {
        items.push(parse_flux_item(cx)?);
    }
    expect!(cx, Tok::Eof)?;
    Ok(items)
}
fn parse_flux_item(cx: &mut ParseCtxt) -> Result<Item> {
    if peek!(cx, Tok::Fn) {
        parse_reft_func(cx).map(Item::FuncDef)
    } else if peek!(cx, Tok::Local | Tok::Qualifier) {
        parse_qualifier(cx).map(Item::Qualifier)
    } else if peek!(cx, Tok::Opaque) {
        parse_sort_decl(cx).map(Item::SortDecl)
    } else {
        todo!("unexpected token")
    }
}

fn parse_reft_func(cx: &mut ParseCtxt) -> Result<SpecFunc> {
    expect!(cx, Tok::Fn)?;
    let name = parse_ident(cx)?;
    let sort_vars = opt_angle_brackets(cx, parse_ident)?;
    let params = parens(cx, Comma, |cx| parse_refine_param(cx, true))?;
    expect!(cx, Tok::RArrow)?;
    let output = parse_sort(cx)?;
    let body = if peek!(cx, OpenDelim(Brace)) {
        Some(parse_block_expr(cx)?)
    } else {
        expect!(cx, Tok::Semi)?;
        None
    };
    Ok(SpecFunc { name, sort_vars, params, output, body })
}

fn parse_qualifier(cx: &mut ParseCtxt) -> Result<Qualifier> {
    let lo = cx.lo();
    let local = advance_if!(cx, Tok::Local);
    expect!(cx, Tok::Qualifier)?;
    let name = parse_ident(cx)?;
    let params = parens(cx, Comma, |cx| parse_refine_param(cx, true))?;
    let expr = parse_block_expr(cx)?;
    let hi = cx.hi();
    Ok(Qualifier { global: !local, name, params, expr, span: cx.mk_span(lo, hi) })
}

fn parse_sort_decl(cx: &mut ParseCtxt) -> Result<SortDecl> {
    expect!(cx, Tok::Opaque)?;
    expect!(cx, Tok::Sort)?;
    let name = parse_ident(cx)?;
    expect!(cx, Tok::Semi)?;
    Ok(SortDecl { name })
}

pub(crate) fn parse_trait_assoc_refts(cx: &mut ParseCtxt) -> Result<Vec<TraitAssocReft>> {
    let mut assoc_refts = vec![];
    while !peek!(cx, Tok::Eof) {
        assoc_refts.push(parse_trait_assoc_reft(cx)?);
    }
    expect!(cx, Tok::Eof)?;
    Ok(assoc_refts)
}

/// ⟨trait_assoc_reft⟩ := fn ⟨ident⟩ ( ⟨refine_param⟩,* ) -> ⟨base_sort⟩ ;?
///                     | fn ⟨ident⟩ ( ⟨refine_param⟩,* ) -> ⟨base_sort⟩ ⟨block_expr⟩
fn parse_trait_assoc_reft(cx: &mut ParseCtxt) -> Result<TraitAssocReft> {
    let lo = cx.lo();
    expect!(cx, Tok::Fn)?;
    let name = parse_ident(cx)?;
    let params = parens(cx, Comma, |cx| parse_refine_param(cx, true))?;
    expect!(cx, Tok::RArrow)?;
    let output = parse_base_sort(cx)?;
    let body = if peek!(cx, OpenDelim(Brace)) {
        Some(parse_block_expr(cx)?)
    } else {
        advance_if!(cx, Tok::Semi);
        None
    };
    let hi = cx.hi();
    Ok(TraitAssocReft { name, params, output, body, span: cx.mk_span(lo, hi) })
}

pub(crate) fn parse_impl_assoc_refts(cx: &mut ParseCtxt) -> Result<Vec<ImplAssocReft>> {
    let mut assoc_refts = vec![];
    while !peek!(cx, Tok::Eof) {
        assoc_refts.push(parse_impl_assoc_reft(cx)?);
    }
    expect!(cx, Tok::Eof)?;
    Ok(assoc_refts)
}

/// ⟨impl_assoc_reft⟩ := fn ⟨ident⟩ ( ⟨refine_param⟩,* ) -> ⟨base_sort⟩ ⟨block_expr⟩
fn parse_impl_assoc_reft(cx: &mut ParseCtxt) -> Result<ImplAssocReft> {
    let lo = cx.lo();
    expect!(cx, Tok::Fn)?;
    let name = parse_ident(cx)?;
    let params = parens(cx, Comma, |cx| parse_refine_param(cx, true))?;
    expect!(cx, Tok::RArrow)?;
    let output = parse_base_sort(cx)?;
    let body = parse_block_expr(cx)?;
    let hi = cx.hi();
    Ok(ImplAssocReft { name, params, output, body, span: cx.mk_span(lo, hi) })
}

pub(crate) fn parse_refined_by(cx: &mut ParseCtxt) -> Result<RefineParams> {
    let mut params = vec![];
    while !peek!(cx, Tok::Eof) {
        params.push(parse_refine_param(cx, true)?);
        if !advance_if!(cx, Tok::Comma) {
            break;
        }
    }
    expect!(cx, Tok::Eof)?;
    Ok(params)
}

/// ⟨variant⟩ := ⟨fields⟩ -> ⟨variant_ret⟩
///            | ⟨fields⟩
///            | ⟨variant_ret⟩
pub(crate) fn parse_variant(cx: &mut ParseCtxt) -> Result<VariantDef> {
    let lo = cx.lo();
    let mut fields = vec![];
    let mut ret = None;
    if peek!(cx, OpenDelim(Parenthesis | Brace)) {
        fields = parse_fields(cx)?;
        if advance_if!(cx, Tok::RArrow) {
            ret = Some(parse_variant_ret(cx)?);
        }
    } else {
        ret = Some(parse_variant_ret(cx)?);
    };
    let hi = cx.hi();
    Ok(VariantDef { fields, ret, node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) })
}

/// ⟨fields⟩ := ( ⟨ty⟩,* ) | { ⟨ty⟩,* }
fn parse_fields(cx: &mut ParseCtxt) -> Result<Vec<Ty>> {
    if peek!(cx, OpenDelim(Parenthesis)) {
        parens(cx, Comma, parse_type)
    } else if peek!(cx, OpenDelim(Brace)) {
        braces(cx, Comma, parse_type)
    } else {
        todo!("unexpected")
    }
}

/// ⟨variant_ret⟩ := ⟨path⟩ ⟨ [ ⟨refine_arg⟩,? ] ⟩?
fn parse_variant_ret(cx: &mut ParseCtxt) -> Result<VariantRet> {
    let path = parse_path(cx)?;
    let indices = if peek!(cx, OpenDelim(Bracket)) {
        parse_indices(cx)?
    } else {
        let hi = cx.hi();
        Indices { indices: vec![], span: cx.mk_span(hi, hi) }
    };
    Ok(VariantRet { path, indices })
}

pub(crate) fn parse_type_alias(cx: &mut ParseCtxt) -> Result<TyAlias> {
    let lo = cx.lo();
    expect!(cx, Tok::Type)?;
    let ident = parse_ident(cx)?;
    let generics = parse_opt_generics(cx)?;
    let params = if peek!(cx, OpenDelim(Parenthesis)) {
        parens(cx, Comma, |cx| parse_refine_param(cx, true))?
    } else {
        vec![]
    };
    let index = if peek!(cx, OpenDelim(Bracket)) {
        Some(delimited(cx, Bracket, |cx| parse_refine_param(cx, true))?)
    } else {
        None
    };
    expect!(cx, Tok::Eq)?;
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

fn parse_opt_generics(cx: &mut ParseCtxt) -> Result<Generics> {
    if !peek!(cx, Tok::Lt) {
        let hi = cx.hi();
        return Ok(Generics { params: vec![], predicates: None, span: cx.mk_span(hi, hi) });
    }
    let lo = cx.lo();
    let params = angle_brackets(cx, parse_generic_param)?;
    let hi = cx.hi();
    Ok(Generics { params, predicates: None, span: cx.mk_span(lo, hi) })
}

fn parse_generic_param(cx: &mut ParseCtxt) -> Result<GenericParam> {
    let name = parse_ident(cx)?;
    let mut kind = GenericParamKind::Type;
    if advance_if!(cx, Tok::As) {
        kind = match expect!(cx, Tok::Ident(sym) => sym)?.as_str() {
            "type" => GenericParamKind::Type,
            "base" => GenericParamKind::Base,
            _ => todo!("report unexpected token"),
        };
    }
    Ok(GenericParam { name, kind, node_id: cx.next_node_id() })
}

/// ⟨fn_sig⟩ := ⟨asyncness⟩ fn ⟨ident⟩?
///             ⟨ [ ⟨refine_param⟩,* ] ⟩?
///             ( ⟨fn_inputs⟩,* )
///             ⟨-> ⟨ty⟩⟩?
///             ⟨requires⟩ ⟨ensures⟩ ⟨where⟩
pub(crate) fn parse_fn_sig(cx: &mut ParseCtxt) -> Result<FnSig> {
    let lo = cx.lo();
    let asyncness = parse_asyncness(cx);
    expect!(cx, Tok::Fn)?;
    let ident = if peek!(cx, Tok::Ident(_)) { Some(parse_ident(cx)?) } else { None };
    let mut generics = parse_opt_generics(cx)?;
    let params = if peek!(cx, OpenDelim(Bracket)) {
        brackets(cx, Comma, |cx| parse_refine_param(cx, false))?
    } else {
        vec![]
    };
    let (inputs, _) = punctuated(cx, Parenthesis, Comma, |cx| parse_fn_input(cx))?;
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
fn parse_opt_requires(cx: &mut ParseCtxt) -> Result<Vec<Requires>> {
    let mut requires = vec![];

    if !advance_if!(cx, Tok::Requires) {
        return Ok(requires);
    }

    while !peek!(cx, Tok::Ensures | Tok::Where | Tok::Eof) {
        requires.push(parse_requires_clause(cx)?);
        if !advance_if!(cx, Comma) {
            break;
        }
    }
    Ok(requires)
}

/// ⟨requires_clause⟩ := ⟨ forall ⟨refine_param⟩,+ . ⟩? ⟨expr⟩
fn parse_requires_clause(cx: &mut ParseCtxt) -> Result<Requires> {
    let mut params = vec![];
    if advance_if!(cx, Tok::Forall) {
        params = sep1(cx, Comma, |cx| parse_refine_param(cx, false))?;
        expect!(cx, Tok::Dot)?;
    }
    let pred = parse_expr(cx, true)?;
    Ok(Requires { params, pred })
}

/// ⟨ensures⟩ := ⟨ensures ⟨ensures_clause⟩,*⟩?
fn parse_opt_ensures(cx: &mut ParseCtxt) -> Result<Vec<Ensures>> {
    let mut ensures = vec![];

    if !advance_if!(cx, Tok::Ensures) {
        return Ok(ensures);
    }

    while !peek!(cx, Tok::Where | Tok::Eof) {
        ensures.push(parse_ensures_clause(cx)?);
        if !advance_if!(cx, Comma) {
            break;
        }
    }
    Ok(ensures)
}

/// ⟨ensures_clause⟩ :=  ⟨ident⟩ : ⟨ty⟩
///                   |  ⟨expr⟩
fn parse_ensures_clause(cx: &mut ParseCtxt) -> Result<Ensures> {
    if peek!(cx, Tok::Ident(_), Tok::Colon) {
        // ⟨ident⟩ : ⟨ty⟩
        let ident = parse_ident(cx)?;
        expect!(cx, Tok::Colon)?;
        let ty = parse_type(cx)?;
        Ok(Ensures::Type(ident, ty, cx.next_node_id()))
    } else {
        // ⟨expr⟩
        Ok(Ensures::Pred(parse_expr(cx, true)?))
    }
}

fn parse_opt_where(cx: &mut ParseCtxt) -> Result<Option<Vec<WhereBoundPredicate>>> {
    if !advance_if!(cx, Tok::Where) {
        return Ok(None);
    }
    let mut predicates = vec![];
    while !peek!(cx, Tok::Eof) {
        predicates.push(parse_where_bound(cx)?);
        if !advance_if!(cx, Comma) {
            break;
        }
    }
    Ok(Some(predicates))
}

fn parse_where_bound(cx: &mut ParseCtxt) -> Result<WhereBoundPredicate> {
    let lo = cx.lo();
    let bounded_ty = parse_type(cx)?;
    expect!(cx, Tok::Colon)?;
    let bounds = parse_generic_bounds(cx)?;
    let hi = cx.hi();
    Ok(WhereBoundPredicate { span: cx.mk_span(lo, hi), bounded_ty, bounds })
}

/// ⟨fn_ret⟩ := ⟨ -> ⟨ty⟩ ⟩?
fn parse_fn_ret(cx: &mut ParseCtxt) -> Result<FnRetTy> {
    if advance_if!(cx, Tok::RArrow) {
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
fn parse_fn_input(cx: &mut ParseCtxt) -> Result<FnInput> {
    if peek!(cx, Tok::Ident(_), Tok::Colon) {
        let bind = parse_ident(cx)?;
        expect!(cx, Tok::Colon)?;
        if advance_if!(cx, Tok::And, Tok::Strg) {
            // ⟨ident⟩ : &strg ⟨ty⟩
            Ok(FnInput::StrgRef(bind, parse_type(cx)?, cx.next_node_id()))
        } else if peek!(cx, Tok::Ident(_)) {
            let path = parse_path(cx)?;
            if peek!(cx, OpenDelim(Brace), Tok::Ident(_), Tok::Colon) {
                // ⟨ident⟩ : ⟨ty⟩
                let bty = path_to_bty(path);
                let ty = parse_bty_exists(cx, bty)?;
                Ok(FnInput::Ty(Some(bind), ty, cx.next_node_id()))
            } else if peek!(cx, OpenDelim(Brace)) {
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
    if advance_if!(cx, Tok::Async) {
        Async::Yes { node_id: cx.next_node_id(), span: cx.mk_span(lo, cx.hi()) }
    } else {
        Async::No
    }
}

/// ⟨ty⟩ := _
///       | { ⟨ident⟩ ⟨,⟨ident⟩⟩* . ⟨ty⟩ | ⟨expr⟩ }
///       | ( ⟨ty⟩,* )
///       | { ⟨ty⟩ | ⟨expr⟩ }
///       | & mut? ⟨ty⟩
///       | [ ⟨ty⟩ ; ⟨const_arg⟩ ]
///       | impl ⟨path⟩
///       | ⟨bty⟩
///       | ⟨bty⟩ [ ⟨refine_arg⟩,* ]
///       | ⟨bty⟩ { ⟨ident⟩ : ⟨expr⟩ }
///
/// ⟨bty⟩ := ⟨path⟩ | ⟨qpath⟩ | [ ⟨ty⟩ ]
pub(crate) fn parse_type(cx: &mut ParseCtxt) -> Result<Ty> {
    let lo = cx.lo();
    let kind = if advance_if!(cx, Tok::Underscore) {
        TyKind::Hole
    } else if peek!(cx, OpenDelim(Parenthesis)) {
        // ( ⟨ty⟩,* )
        let (mut tys, trailing) = punctuated(cx, Parenthesis, Comma, parse_type)?;
        if tys.len() == 1 && !trailing {
            return Ok(tys.remove(0));
        } else {
            TyKind::Tuple(tys)
        }
    } else if peek!(cx, OpenDelim(Brace)) {
        delimited(cx, Brace, |cx| {
            if peek!(cx, Tok::Ident(_), Tok::Comma | Tok::Dot | Tok::Colon) {
                // { ⟨ident⟩ ⟨,⟨ident⟩⟩* . ⟨ty⟩ | ⟨expr⟩ }
                parse_general_exists(cx)
            } else {
                // { ⟨ty⟩ | ⟨expr⟩ }
                let ty = parse_type(cx)?;
                expect!(cx, Tok::Caret)?;
                let pred = parse_expr(cx, true)?;
                Ok(TyKind::Constr(pred, Box::new(ty)))
            }
        })?
    } else if advance_if!(cx, Tok::And) {
        //  & mut? ⟨ty⟩
        let mutbl = if advance_if!(cx, Tok::Mut) { Mutability::Mut } else { Mutability::Not };
        TyKind::Ref(mutbl, Box::new(parse_type(cx)?))
    } else if advance_if!(cx, OpenDelim(Bracket)) {
        let ty = parse_type(cx)?;
        if advance_if!(cx, Tok::Semi) {
            // [ ⟨ty⟩ ; ⟨const_arg⟩ ]
            let len = parse_const_arg(cx)?;
            expect!(cx, CloseDelim(Bracket))?;
            TyKind::Array(Box::new(ty), len)
        } else {
            // [ ⟨ty⟩ ] ⟨[ ⟨refine_arg⟩,* ]⟩
            expect!(cx, CloseDelim(Bracket))?;
            let hi = cx.hi();
            let kind = BaseTyKind::Slice(Box::new(ty));
            let bty = BaseTy { kind, span: cx.mk_span(lo, hi) };
            return parse_bty_rhs(cx, bty);
        }
    } else if advance_if!(cx, Tok::Impl) {
        // impl ⟨bounds⟩
        TyKind::ImplTrait(cx.next_node_id(), parse_generic_bounds(cx)?)
    } else if peek!(cx, Tok::Ident(_)) {
        let path = parse_path(cx)?;
        let bty = path_to_bty(path);
        return parse_bty_rhs(cx, bty);
    } else if peek!(cx, Tok::Lt) {
        let bty = parse_qpath(cx)?;
        return parse_bty_rhs(cx, bty);
    } else {
        todo!("unexpected token")
    };
    let hi = cx.hi();
    Ok(Ty { kind, node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) })
}

/// ⟨qpath⟩ := < ⟨ty⟩ as ⟨segments⟩> :: ⟨segments⟩
fn parse_qpath(cx: &mut ParseCtxt) -> Result<BaseTy> {
    let lo = cx.lo();
    expect!(cx, Tok::Lt)?;
    let qself = parse_type(cx)?;
    expect!(cx, Tok::As)?;
    let mut segments = parse_segments(cx)?;
    expect!(cx, Tok::GtFollowedByGt | Tok::Gt)?;
    expect!(cx, Tok::PathSep)?;
    segments.extend(parse_segments(cx)?);
    let hi = cx.hi();

    let path =
        Path { segments, refine: vec![], node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) };
    let kind = BaseTyKind::Path(Some(Box::new(qself)), path);
    Ok(BaseTy { kind, span: cx.mk_span(lo, hi) })
}

fn parse_general_exists(cx: &mut ParseCtxt) -> Result<TyKind> {
    let params = sep1(cx, Comma, |cx| parse_refine_param(cx, false))?;
    expect!(cx, Tok::Dot)?;
    let ty = parse_type(cx)?;
    let pred = if advance_if!(cx, Tok::Caret) { Some(parse_expr(cx, true)?) } else { None };
    Ok(TyKind::GeneralExists { params, ty: Box::new(ty), pred })
}

///    ⟨bty⟩ [ ⟨refine_arg⟩,* ]
/// |  ⟨bty⟩ { ⟨ident⟩ : ⟨expr⟩ }
/// |  ⟨bty⟩
fn parse_bty_rhs(cx: &mut ParseCtxt, bty: BaseTy) -> Result<Ty> {
    let lo = bty.span.lo();
    if peek!(cx, OpenDelim(Bracket)) {
        // ⟨bty⟩ [ ⟨refine_arg⟩,* ]
        let indices = parse_indices(cx)?;
        let hi = cx.hi();
        let kind = TyKind::Indexed { bty, indices };
        Ok(Ty { kind, node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) })
    } else if peek!(cx, OpenDelim(Brace)) {
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
fn parse_bty_exists(cx: &mut ParseCtxt, bty: BaseTy) -> Result<Ty> {
    let lo = bty.span.lo();
    delimited(cx, Brace, |cx| {
        let bind = parse_ident(cx)?;
        expect!(cx, Tok::Colon)?;
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

fn parse_indices(cx: &mut ParseCtxt) -> Result<Indices> {
    let lo = cx.lo();
    let indices = brackets(cx, Comma, parse_refine_arg)?;
    let hi = cx.hi();
    Ok(Indices { indices, span: cx.mk_span(lo, hi) })
}

fn parse_generic_bounds(cx: &mut ParseCtxt) -> Result<GenericBounds> {
    let path = parse_path(cx)?;
    Ok(vec![TraitRef { path }])
}

fn parse_const_arg(cx: &mut ParseCtxt) -> Result<ConstArg> {
    let lo = cx.lo();
    let kind = if peek!(cx, Tok::Literal(_)) {
        let len = parse_int(cx)?;
        ConstArgKind::Lit(len)
    } else if advance_if!(cx, Tok::Underscore) {
        ConstArgKind::Infer
    } else {
        todo!("unexpected token")
    };
    let hi = cx.hi();
    Ok(ConstArg { kind, span: cx.mk_span(lo, hi) })
}

/// ⟨path⟩ := ⟨segments⟩ ⟨ ( ⟨refine_arg⟩,* ) ⟩?
fn parse_path(cx: &mut ParseCtxt) -> Result<Path> {
    let lo = cx.lo();
    let segments = parse_segments(cx)?;
    let refine = if peek!(cx, OpenDelim(Parenthesis)) {
        parens(cx, Comma, parse_refine_arg)?
    } else {
        vec![]
    };
    let hi = cx.hi();
    Ok(Path { segments, refine, node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) })
}

/// ⟨segments⟩ := ⟨segment⟩ ⟨:: ⟨segment⟩ ⟩*
fn parse_segments(cx: &mut ParseCtxt) -> Result<Vec<PathSegment>> {
    sep1(cx, Tok::PathSep, parse_segment)
}

/// ⟨segment⟩ := ⟨ident⟩ ⟨ < ⟨generic_arg⟩,* > ⟩?
fn parse_segment(cx: &mut ParseCtxt) -> Result<PathSegment> {
    let ident = parse_ident(cx)?;
    let args = opt_angle_brackets(cx, parse_generic_arg)?;
    Ok(PathSegment { ident, node_id: cx.next_node_id(), args })
}

/// ⟨generic_arg⟩ := ⟨ty⟩ | ⟨ident⟩ = ⟨ty⟩
fn parse_generic_arg(cx: &mut ParseCtxt) -> Result<GenericArg> {
    let kind = if peek!(cx, Tok::Ident(_), Tok::Eq) {
        let ident = parse_ident(cx)?;
        expect!(cx, Tok::Eq)?;
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
fn parse_refine_arg(cx: &mut ParseCtxt) -> Result<RefineArg> {
    let lo = cx.lo();
    let arg = if advance_if!(cx, Tok::At) {
        // @ ⟨ident⟩
        let bind = parse_ident(cx)?;
        let hi = cx.hi();
        RefineArg::Bind(bind, BindKind::At, cx.mk_span(lo, hi), cx.next_node_id())
    } else if advance_if!(cx, Tok::Pound) {
        // # ⟨ident⟩
        let bind = parse_ident(cx)?;
        let hi = cx.hi();
        RefineArg::Bind(bind, BindKind::Pound, cx.mk_span(lo, hi), cx.next_node_id())
    } else if advance_if!(cx, Caret) {
        let params = terminated(cx, Comma, Caret, |cx| parse_refine_param(cx, false))?;
        let body = parse_expr(cx, true)?;
        let hi = cx.hi();
        RefineArg::Abs(params, body, cx.mk_span(lo, hi), cx.next_node_id())
    } else {
        // ⟨expr⟩
        RefineArg::Expr(parse_expr(cx, true)?)
    };
    Ok(arg)
}

/// ⟨refine_param⟩ := ⟨mode⟩? ⟨ident⟩ ⟨ : ⟨sort⟩ ⟩?
fn parse_refine_param(cx: &mut ParseCtxt, require_sort: bool) -> Result<RefineParam> {
    let lo = cx.lo();
    let mode = parse_param_mode(cx);
    let ident = parse_ident(cx)?;
    let sort = if require_sort {
        expect!(cx, Tok::Colon)?;
        parse_sort(cx)?
    } else if advance_if!(cx, Tok::Colon) {
        parse_sort(cx)?
    } else {
        Sort::Infer
    };
    let hi = cx.hi();
    Ok(RefineParam { mode, ident, sort, span: cx.mk_span(lo, hi), node_id: cx.next_node_id() })
}

/// ⟨mode⟩ := hrn | hdl
fn parse_param_mode(cx: &mut ParseCtxt) -> Option<ParamMode> {
    if advance_if!(cx, Tok::Hrn) {
        Some(ParamMode::Horn)
    } else if advance_if!(cx, Tok::Hdl) {
        Some(ParamMode::Hindley)
    } else {
        None
    }
}

pub(crate) fn parse_expr(cx: &mut ParseCtxt, allow_struct: bool) -> Result<Expr> {
    parse_binops(cx, Precedence::MIN, allow_struct)
}

fn parse_binops(cx: &mut ParseCtxt, base: Precedence, allow_struct: bool) -> Result<Expr> {
    let mut lhs = expr_unary(cx, allow_struct)?;
    loop {
        let Some((op, ntokens)) = peek_binop(cx) else { break };
        let precedence = Precedence::of_binop(&op);
        if precedence < base {
            break;
        }
        if matches!(precedence, Precedence::Iff | Precedence::Implies | Precedence::Compare) {
            if let ExprKind::BinaryOp(op, ..) = &lhs.kind {
                if Precedence::of_binop(&op) == precedence {
                    todo!("comparison operators cannot be chained");
                }
            }
        }
        cx.cursor.advance_by(ntokens);
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

fn peek_binop(cx: &mut ParseCtxt) -> Option<(BinOp, usize)> {
    let op = match cx.cursor.at(0) {
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
        Tok::Shl => (BinOp::BitShl, 1),
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

fn expr_unary(cx: &mut ParseCtxt, allow_struct: bool) -> Result<Expr> {
    let lo = cx.lo();
    let kind = if advance_if!(cx, Tok::Minus) {
        ExprKind::UnaryOp(UnOp::Neg, Box::new(expr_unary(cx, allow_struct)?))
    } else if advance_if!(cx, Tok::Not) {
        ExprKind::UnaryOp(UnOp::Not, Box::new(expr_unary(cx, allow_struct)?))
    } else {
        return parse_trailer_expr(cx, allow_struct);
    };
    let hi = cx.hi();
    Ok(Expr { kind, node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) })
}

/// ⟨trailer⟩ := ⟨epath⟩ . ⟨ident⟩
///            | ⟨ident⟩ ( ⟨expr⟩,* )
///            | ⟨atom⟩
///            | <⟨ty⟩ as ⟨path⟩> :: ⟨ident⟩ ( ⟨expr⟩,* )
fn parse_trailer_expr(cx: &mut ParseCtxt, allow_struct: bool) -> Result<Expr> {
    if advance_if!(cx, Tok::Lt) {
        // <⟨ty⟩ as ⟨path⟩> :: ⟨ident⟩ ( ⟨expr⟩,* )
        let lo = cx.lo();
        let qself = parse_type(cx)?;
        expect!(cx, Tok::As)?;
        let path = parse_path(cx)?;
        expect!(cx, Tok::GtFollowedByGt | Tok::Gt)?;
        expect!(cx, Tok::PathSep)?;
        let name = parse_ident(cx)?;
        let args = parens(cx, Comma, |cx| parse_expr(cx, true))?;
        let kind = ExprKind::Alias(AliasReft { qself: Box::new(qself), path, name }, args);
        let hi = cx.hi();
        return Ok(Expr { kind, node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) });
    }

    let atom = parse_atom(cx, allow_struct)?;
    let lo = cx.lo();
    let kind = if advance_if!(cx, Tok::Dot) {
        // ⟨epath⟩ . ⟨ident⟩
        let field = parse_ident(cx)?;
        let ExprKind::Path(path) = atom.kind else { todo!() };
        ExprKind::Dot(path, field)
    } else if peek!(cx, OpenDelim(Parenthesis)) {
        let args = parens(cx, Comma, |cx| parse_expr(cx, true))?;
        if let ExprKind::Path(path) = atom.kind
            && let [segment] = &path.segments[..]
        {
            // ⟨ident⟩ ( ⟨expr⟩,* )
            ExprKind::App(segment.ident, args)
        } else {
            todo!("report error")
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
///         | ⟨epath⟩ { ⟨constructor_arg⟩,* }
///         | { ⟨constructor_arg⟩,* }
fn parse_atom(cx: &mut ParseCtxt, allow_struct: bool) -> Result<Expr> {
    let lo = cx.lo();
    if peek!(cx, Tok::If) {
        // ⟨if_expr⟩
        parse_if_expr(cx)
    } else if peek!(cx, Tok::Literal(_)) {
        // ⟨lit⟩
        parse_lit(cx)
    } else if peek!(cx, OpenDelim(Parenthesis)) {
        delimited(cx, Parenthesis, |cx| parse_expr(cx, true))
    } else if peek!(cx, Tok::Ident(_)) {
        let path = parse_expr_path(cx)?;
        let kind = if allow_struct && peek!(cx, Tok::OpenDelim(Brace)) {
            // ⟨epath⟩ { ⟨constructor_arg⟩,* }
            let args = braces(cx, Comma, parse_constructor_arg)?;
            ExprKind::Constructor(Some(path), args)
        } else {
            // ⟨epath⟩
            ExprKind::Path(path)
        };
        let hi = cx.hi();
        Ok(Expr { kind, node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) })
    } else if allow_struct && peek!(cx, OpenDelim(Brace)) {
        // { ⟨constructor_arg⟩,* }
        let args = braces(cx, Comma, parse_constructor_arg)?;
        let hi = cx.hi();
        Ok(Expr {
            kind: ExprKind::Constructor(None, args),
            node_id: cx.next_node_id(),
            span: cx.mk_span(lo, hi),
        })
    } else {
        todo!("unexpected token {}", cx.cursor.debug(10));
    }
}

/// ⟨constructor_arg⟩ :=  ⟨ident⟩ : ⟨expr⟩ |  ..
fn parse_constructor_arg(cx: &mut ParseCtxt) -> Result<ConstructorArg> {
    let lo = cx.lo();
    if peek!(cx, Tok::Ident(_)) {
        let ident = parse_ident(cx)?;
        expect!(cx, Tok::Colon)?;
        let expr = parse_expr(cx, true)?;
        let hi = cx.hi();
        Ok(ConstructorArg::FieldExpr(FieldExpr {
            ident,
            expr,
            node_id: cx.next_node_id(),
            span: cx.mk_span(lo, hi),
        }))
    } else if advance_if!(cx, Tok::DotDot) {
        let spread = parse_expr(cx, true)?;
        let hi = cx.hi();
        Ok(ConstructorArg::Spread(Spread {
            expr: spread,
            node_id: cx.next_node_id(),
            span: cx.mk_span(lo, hi),
        }))
    } else {
        todo!("unexpected token")
    }
}

/// ⟨lit⟩ := "a Rust literal like an integer or a boolean"
fn parse_lit(cx: &mut ParseCtxt) -> Result<Expr> {
    let lo = cx.lo();
    let lit = expect!(cx, Tok::Literal(lit) => lit)?;
    let hi = cx.hi();
    Ok(Expr { kind: ExprKind::Literal(lit), node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) })
}

/// ⟨epath⟩ := ⟨ident⟩ ⟨ :: ⟨ident⟩ ⟩*
fn parse_expr_path(cx: &mut ParseCtxt) -> Result<ExprPath> {
    let lo = cx.lo();
    let mut segments = vec![parse_expr_path_segment(cx)?];
    while advance_if!(cx, Tok::PathSep) {
        segments.push(parse_expr_path_segment(cx)?);
    }
    let hi = cx.hi();
    let span = cx.mk_span(lo, hi);
    Ok(ExprPath { segments, node_id: cx.next_node_id(), span })
}

fn parse_expr_path_segment(cx: &mut ParseCtxt) -> Result<ExprPathSegment> {
    Ok(ExprPathSegment { ident: parse_ident(cx)?, node_id: cx.next_node_id() })
}

fn parse_if_expr(cx: &mut ParseCtxt) -> Result<Expr> {
    let mut branches = vec![];

    loop {
        let lo = cx.lo();
        expect!(cx, Tok::If)?;
        let cond = parse_expr(cx, false)?;
        let then_ = parse_block_expr(cx)?;
        branches.push((lo, cond, then_));
        expect!(cx, Tok::Else)?;

        if !peek!(cx, Tok::If) {
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
fn parse_block_expr(cx: &mut ParseCtxt) -> Result<Expr> {
    delimited(cx, Brace, |cx| parse_expr(cx, true))
}

fn parse_ident(cx: &mut ParseCtxt) -> Result<Ident> {
    let lo = cx.lo();
    let name = expect!(cx, Tok::Ident(name) => name)?;
    let hi = cx.hi();
    Ok(Ident { name, span: cx.mk_span(lo, hi) })
}

fn parse_int<T: FromStr>(cx: &mut ParseCtxt) -> Result<T> {
    let lit = expect!(cx, Tok::Literal(lit) => lit)?;
    if let LitKind::Integer = lit.kind {
        if let Ok(value) = lit.symbol.as_str().parse::<T>() {
            return Ok(value);
        }
    }
    todo!("unexpected token")
}

/// ⟨sort⟩ :=  ⟨base_sort⟩
///         |  ( ⟨base_sort⟩,* ) -> ⟨base_sort⟩
///         |  ⟨base_sort⟩ -> ⟨base_sort⟩
fn parse_sort(cx: &mut ParseCtxt) -> Result<Sort> {
    if peek!(cx, OpenDelim(Parenthesis)) {
        // ( ⟨base_sort⟩,* ) -> ⟨base_sort⟩
        let inputs = parens(cx, Comma, parse_base_sort)?;
        expect!(cx, Tok::RArrow)?;
        let output = parse_base_sort(cx)?;
        Ok(Sort::Func { inputs, output })
    } else {
        let bsort = parse_base_sort(cx)?;
        if advance_if!(cx, Tok::RArrow) {
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
fn parse_base_sort(cx: &mut ParseCtxt) -> Result<BaseSort> {
    if advance_if!(cx, Tok::BitVec) {
        expect!(cx, Tok::Lt)?;
        let len = parse_int(cx)?;
        expect!(cx, Tok::Gt | Tok::GtFollowedByGt)?;
        Ok(BaseSort::BitVec(len))
    } else {
        let segments = sep1(cx, Tok::PathSep, parse_ident)?;
        let args = opt_angle_brackets(cx, parse_base_sort)?;
        let path = SortPath { segments, args, node_id: cx.next_node_id() };
        Ok(BaseSort::Path(path))
    }
}

fn opt_angle_brackets<T>(
    cx: &mut ParseCtxt,
    parse: impl FnMut(&mut ParseCtxt) -> Result<T>,
) -> Result<Vec<T>> {
    if !peek!(cx, Tok::Lt) {
        return Ok(vec![]);
    }
    angle_brackets(cx, parse)
}

fn angle_brackets<T>(
    cx: &mut ParseCtxt,
    mut parse: impl FnMut(&mut ParseCtxt) -> Result<T>,
) -> Result<Vec<T>> {
    expect!(cx, Tok::Lt)?;
    let mut items = vec![];
    while !peek!(cx, Tok::Gt | Tok::GtFollowedByGt) {
        items.push(parse(cx)?);

        if !cx.cursor.advance_if(Comma) {
            break;
        }
    }
    expect!(cx, Tok::Gt | Tok::GtFollowedByGt)?;
    Ok(items)
}

#[track_caller]
fn delimited<T>(
    cx: &mut ParseCtxt,
    delim: Delimiter,
    parse: impl FnOnce(&mut ParseCtxt) -> Result<T>,
) -> Result<T> {
    expect!(cx, OpenDelim(d) if d == delim)?;
    let r = parse(cx)?;
    expect!(cx, CloseDelim(d) if d == delim)?;
    Ok(r)
}

fn brackets<T>(
    cx: &mut ParseCtxt,
    sep: Tok,
    parse: impl FnMut(&mut ParseCtxt) -> Result<T>,
) -> Result<Vec<T>> {
    Ok(punctuated(cx, Bracket, sep, parse)?.0)
}

fn parens<T>(
    cx: &mut ParseCtxt,
    sep: Tok,
    parse: impl FnMut(&mut ParseCtxt) -> Result<T>,
) -> Result<Vec<T>> {
    Ok(punctuated(cx, Parenthesis, sep, parse)?.0)
}

fn braces<T>(
    cx: &mut ParseCtxt,
    sep: Tok,
    parse: impl FnMut(&mut ParseCtxt) -> Result<T>,
) -> Result<Vec<T>> {
    Ok(punctuated(cx, Brace, sep, parse)?.0)
}

#[track_caller]
fn punctuated<T>(
    cx: &mut ParseCtxt,
    delim: Delimiter,
    sep: Tok,
    mut parse: impl FnMut(&mut ParseCtxt) -> Result<T>,
) -> Result<(Vec<T>, bool)> {
    expect!(cx, OpenDelim(d) if delim == d)?;
    let mut items = vec![];

    let mut trailing = false;
    while cx.cursor.at(0) != CloseDelim(delim) {
        items.push(parse(cx)?);

        trailing = cx.cursor.advance_if(sep);
        if !trailing {
            break;
        }
    }
    expect!(cx, CloseDelim(d) if d == delim)?;
    Ok((items, trailing))
}

fn sep1<T>(
    cx: &mut ParseCtxt,
    sep: Tok,
    mut parse: impl FnMut(&mut ParseCtxt) -> Result<T>,
) -> Result<Vec<T>> {
    let mut items = vec![parse(cx)?];
    while cx.cursor.advance_if(sep) {
        items.push(parse(cx)?);
    }
    Ok(items)
}

fn terminated<T>(
    cx: &mut ParseCtxt,
    sep: Tok,
    end: Tok,
    mut parse: impl FnMut(&mut ParseCtxt) -> Result<T>,
) -> Result<Vec<T>> {
    let mut items = vec![];
    while cx.cursor.at(0) != end {
        items.push(parse(cx)?);
        if !cx.cursor.advance_if(sep) {
            break;
        }
    }
    expect!(cx, t if t == end)?;
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
    #[expect(
        dead_code,
        reason = "we don't support xor yet but keeping this here so we don't have to find the precedence once we add it"
    )]
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
