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

impl ParseCtxt<'_> {
    pub(crate) fn parse_yes_or_no_with_reason(&mut self) -> Result<bool> {
        let ident = expect!(self, Tok::Ident(ident) => ident)?;
        let yes = match ident.as_str() {
            s @ ("yes" | "no") => {
                if advance_if!(self, Tok::Comma) {
                    expect!(self, Tok::Ident(sym) if sym.as_str() == "reason")?;
                    expect!(self, Tok::Eq)?;
                    expect!(self, Tok::Literal(_))?;
                }
                s == "yes"
            }
            "reason" => {
                expect!(self, Tok::Eq)?;
                expect!(self, Tok::Literal(_))?;
                true
            }
            _ => todo!("unexpected token"),
        };
        Ok(yes)
    }

    pub(crate) fn parse_qual_names(&mut self) -> Result<QualNames> {
        let names = terminated(self, Comma, Tok::Eof, |cx| cx.parse_ident())?;
        Ok(QualNames { names })
    }

    pub(crate) fn parse_generics(&mut self) -> Result<Generics> {
        let lo = self.lo();
        let params = terminated(self, Comma, Tok::Eof, |cx| cx.parse_generic_param())?;
        let hi = self.hi();
        Ok(Generics { params, predicates: None, span: self.mk_span(lo, hi) })
    }

    pub(crate) fn parse_flux_items(&mut self) -> Result<Vec<Item>> {
        let mut items = vec![];
        while !peek!(self, Tok::Eof) {
            items.push(self.parse_flux_item()?);
        }
        expect!(self, Tok::Eof)?;
        Ok(items)
    }
    fn parse_flux_item(&mut self) -> Result<Item> {
        if peek!(self, Tok::Fn) {
            self.parse_reft_func().map(Item::FuncDef)
        } else if peek!(self, Tok::Local | Tok::Qualifier) {
            self.parse_qualifier().map(Item::Qualifier)
        } else if peek!(self, Tok::Opaque) {
            self.parse_sort_decl().map(Item::SortDecl)
        } else {
            todo!("unexpected token")
        }
    }

    fn parse_reft_func(&mut self) -> Result<SpecFunc> {
        expect!(self, Tok::Fn)?;
        let name = self.parse_ident()?;
        let sort_vars = opt_angle_brackets(self, |cx| cx.parse_ident())?;
        let params = parens(self, Comma, |cx| cx.parse_refine_param(true))?;
        expect!(self, Tok::RArrow)?;
        let output = self.parse_sort()?;
        let body = if peek!(self, OpenDelim(Brace)) {
            Some(self.parse_block_expr()?)
        } else {
            expect!(self, Tok::Semi)?;
            None
        };
        Ok(SpecFunc { name, sort_vars, params, output, body })
    }

    fn parse_qualifier(&mut self) -> Result<Qualifier> {
        let lo = self.lo();
        let local = advance_if!(self, Tok::Local);
        expect!(self, Tok::Qualifier)?;
        let name = self.parse_ident()?;
        let params = parens(self, Comma, |cx| cx.parse_refine_param(true))?;
        let expr = self.parse_block_expr()?;
        let hi = self.hi();
        Ok(Qualifier { global: !local, name, params, expr, span: self.mk_span(lo, hi) })
    }

    fn parse_sort_decl(&mut self) -> Result<SortDecl> {
        expect!(self, Tok::Opaque)?;
        expect!(self, Tok::Sort)?;
        let name = self.parse_ident()?;
        expect!(self, Tok::Semi)?;
        Ok(SortDecl { name })
    }

    pub(crate) fn parse_trait_assoc_refts(&mut self) -> Result<Vec<TraitAssocReft>> {
        let mut assoc_refts = vec![];
        while !peek!(self, Tok::Eof) {
            assoc_refts.push(self.parse_trait_assoc_reft()?);
        }
        expect!(self, Tok::Eof)?;
        Ok(assoc_refts)
    }

    /// ⟨trait_assoc_reft⟩ := fn ⟨ident⟩ ( ⟨refine_param⟩,* ) -> ⟨base_sort⟩ ;?
    ///                     | fn ⟨ident⟩ ( ⟨refine_param⟩,* ) -> ⟨base_sort⟩ ⟨block_expr⟩
    fn parse_trait_assoc_reft(&mut self) -> Result<TraitAssocReft> {
        let lo = self.lo();
        expect!(self, Tok::Fn)?;
        let name = self.parse_ident()?;
        let params = parens(self, Comma, |cx| cx.parse_refine_param(true))?;
        expect!(self, Tok::RArrow)?;
        let output = self.parse_base_sort()?;
        let body = if peek!(self, OpenDelim(Brace)) {
            Some(self.parse_block_expr()?)
        } else {
            advance_if!(self, Tok::Semi);
            None
        };
        let hi = self.hi();
        Ok(TraitAssocReft { name, params, output, body, span: self.mk_span(lo, hi) })
    }

    pub(crate) fn parse_impl_assoc_refts(&mut self) -> Result<Vec<ImplAssocReft>> {
        let mut assoc_refts = vec![];
        while !peek!(self, Tok::Eof) {
            assoc_refts.push(self.parse_impl_assoc_reft()?);
        }
        expect!(self, Tok::Eof)?;
        Ok(assoc_refts)
    }

    /// ⟨impl_assoc_reft⟩ := fn ⟨ident⟩ ( ⟨refine_param⟩,* ) -> ⟨base_sort⟩ ⟨block_expr⟩
    fn parse_impl_assoc_reft(&mut self) -> Result<ImplAssocReft> {
        let lo = self.lo();
        expect!(self, Tok::Fn)?;
        let name = self.parse_ident()?;
        let params = parens(self, Comma, |cx| cx.parse_refine_param(true))?;
        expect!(self, Tok::RArrow)?;
        let output = self.parse_base_sort()?;
        let body = self.parse_block_expr()?;
        let hi = self.hi();
        Ok(ImplAssocReft { name, params, output, body, span: self.mk_span(lo, hi) })
    }

    pub(crate) fn parse_refined_by(&mut self) -> Result<RefineParams> {
        let mut params = vec![];
        while !peek!(self, Tok::Eof) {
            params.push(self.parse_refine_param(true)?);
            if !advance_if!(self, Tok::Comma) {
                break;
            }
        }
        expect!(self, Tok::Eof)?;
        Ok(params)
    }

    /// ⟨variant⟩ := ⟨fields⟩ -> ⟨variant_ret⟩
    ///            | ⟨fields⟩
    ///            | ⟨variant_ret⟩
    pub(crate) fn parse_variant(&mut self) -> Result<VariantDef> {
        let lo = self.lo();
        let mut fields = vec![];
        let mut ret = None;
        if peek!(self, OpenDelim(Parenthesis | Brace)) {
            fields = self.parse_fields()?;
            if advance_if!(self, Tok::RArrow) {
                ret = Some(self.parse_variant_ret()?);
            }
        } else {
            ret = Some(self.parse_variant_ret()?);
        };
        let hi = self.hi();
        Ok(VariantDef { fields, ret, node_id: self.next_node_id(), span: self.mk_span(lo, hi) })
    }

    /// ⟨fields⟩ := ( ⟨ty⟩,* ) | { ⟨ty⟩,* }
    fn parse_fields(&mut self) -> Result<Vec<Ty>> {
        if peek!(self, OpenDelim(Parenthesis)) {
            parens(self, Comma, |cx| cx.parse_type())
        } else if peek!(self, OpenDelim(Brace)) {
            braces(self, Comma, |cx| cx.parse_type())
        } else {
            todo!("unexpected")
        }
    }

    /// ⟨variant_ret⟩ := ⟨path⟩ ⟨ [ ⟨refine_arg⟩,? ] ⟩?
    fn parse_variant_ret(&mut self) -> Result<VariantRet> {
        let path = self.parse_path()?;
        let indices = if peek!(self, OpenDelim(Bracket)) {
            self.parse_indices()?
        } else {
            let hi = self.hi();
            Indices { indices: vec![], span: self.mk_span(hi, hi) }
        };
        Ok(VariantRet { path, indices })
    }

    pub(crate) fn parse_type_alias(&mut self) -> Result<TyAlias> {
        let lo = self.lo();
        expect!(self, Tok::Type)?;
        let ident = self.parse_ident()?;
        let generics = self.parse_opt_generics()?;
        let params = if peek!(self, OpenDelim(Parenthesis)) {
            parens(self, Comma, |cx| cx.parse_refine_param(true))?
        } else {
            vec![]
        };
        let index = if peek!(self, OpenDelim(Bracket)) {
            Some(delimited(self, Bracket, |cx| cx.parse_refine_param(true))?)
        } else {
            None
        };
        expect!(self, Tok::Eq)?;
        let ty = self.parse_type()?;
        let hi = self.hi();
        Ok(TyAlias {
            ident,
            generics,
            params,
            index,
            ty,
            node_id: self.next_node_id(),
            span: self.mk_span(lo, hi),
        })
    }

    fn parse_opt_generics(&mut self) -> Result<Generics> {
        if !peek!(self, Tok::Lt) {
            let hi = self.hi();
            return Ok(Generics { params: vec![], predicates: None, span: self.mk_span(hi, hi) });
        }
        let lo = self.lo();
        let params = angle_brackets(self, |cx| cx.parse_generic_param())?;
        let hi = self.hi();
        Ok(Generics { params, predicates: None, span: self.mk_span(lo, hi) })
    }

    fn parse_generic_param(&mut self) -> Result<GenericParam> {
        let name = self.parse_ident()?;
        let mut kind = GenericParamKind::Type;
        if advance_if!(self, Tok::As) {
            kind = match expect!(self, Tok::Ident(sym) => sym)?.as_str() {
                "type" => GenericParamKind::Type,
                "base" => GenericParamKind::Base,
                _ => todo!("report unexpected token"),
            };
        }
        Ok(GenericParam { name, kind, node_id: self.next_node_id() })
    }

    /// ⟨fn_sig⟩ := ⟨asyncness⟩ fn ⟨ident⟩?
    ///             ⟨ [ ⟨refine_param⟩,* ] ⟩?
    ///             ( ⟨fn_inputs⟩,* )
    ///             ⟨-> ⟨ty⟩⟩?
    ///             ⟨requires⟩ ⟨ensures⟩ ⟨where⟩
    pub(crate) fn parse_fn_sig(&mut self) -> Result<FnSig> {
        let lo = self.lo();
        let asyncness = self.parse_asyncness();
        expect!(self, Tok::Fn)?;
        let ident = if peek!(self, Tok::Ident(_)) { Some(self.parse_ident()?) } else { None };
        let mut generics = self.parse_opt_generics()?;
        let params = if peek!(self, OpenDelim(Bracket)) {
            brackets(self, Comma, |cx| cx.parse_refine_param(false))?
        } else {
            vec![]
        };
        let (inputs, _) = punctuated(self, Parenthesis, Comma, |cx| cx.parse_fn_input())?;
        let returns = self.parse_fn_ret()?;
        let requires = self.parse_opt_requires()?;
        let ensures = self.parse_opt_ensures()?;
        generics.predicates = self.parse_opt_where()?;
        let hi = self.hi();
        Ok(FnSig {
            asyncness,
            generics,
            params,
            ident,
            inputs,
            requires,
            output: FnOutput { returns, ensures, node_id: self.next_node_id() },
            node_id: self.next_node_id(),
            span: self.mk_span(lo, hi),
        })
    }

    /// ⟨requires⟩ := ⟨ requires ⟨requires_clause⟩,* ⟩?
    fn parse_opt_requires(&mut self) -> Result<Vec<Requires>> {
        let mut requires = vec![];

        if !advance_if!(self, Tok::Requires) {
            return Ok(requires);
        }

        while !peek!(self, Tok::Ensures | Tok::Where | Tok::Eof) {
            requires.push(self.parse_requires_clause()?);
            if !advance_if!(self, Comma) {
                break;
            }
        }
        Ok(requires)
    }

    /// ⟨requires_clause⟩ := ⟨ forall ⟨refine_param⟩,+ . ⟩? ⟨expr⟩
    fn parse_requires_clause(&mut self) -> Result<Requires> {
        let mut params = vec![];
        if advance_if!(self, Tok::Forall) {
            params = sep1(self, Comma, |cx| cx.parse_refine_param(false))?;
            expect!(self, Tok::Dot)?;
        }
        let pred = self.parse_expr(true)?;
        Ok(Requires { params, pred })
    }

    /// ⟨ensures⟩ := ⟨ensures ⟨ensures_clause⟩,*⟩?
    fn parse_opt_ensures(&mut self) -> Result<Vec<Ensures>> {
        let mut ensures = vec![];

        if !advance_if!(self, Tok::Ensures) {
            return Ok(ensures);
        }

        while !peek!(self, Tok::Where | Tok::Eof) {
            ensures.push(self.parse_ensures_clause()?);
            if !advance_if!(self, Comma) {
                break;
            }
        }
        Ok(ensures)
    }

    /// ⟨ensures_clause⟩ :=  ⟨ident⟩ : ⟨ty⟩
    ///                   |  ⟨expr⟩
    fn parse_ensures_clause(&mut self) -> Result<Ensures> {
        if peek!(self, Tok::Ident(_), Tok::Colon) {
            // ⟨ident⟩ : ⟨ty⟩
            let ident = self.parse_ident()?;
            expect!(self, Tok::Colon)?;
            let ty = self.parse_type()?;
            Ok(Ensures::Type(ident, ty, self.next_node_id()))
        } else {
            // ⟨expr⟩
            Ok(Ensures::Pred(self.parse_expr(true)?))
        }
    }

    fn parse_opt_where(&mut self) -> Result<Option<Vec<WhereBoundPredicate>>> {
        if !advance_if!(self, Tok::Where) {
            return Ok(None);
        }
        let mut predicates = vec![];
        while !peek!(self, Tok::Eof) {
            predicates.push(self.parse_where_bound()?);
            if !advance_if!(self, Comma) {
                break;
            }
        }
        Ok(Some(predicates))
    }

    fn parse_where_bound(&mut self) -> Result<WhereBoundPredicate> {
        let lo = self.lo();
        let bounded_ty = self.parse_type()?;
        expect!(self, Tok::Colon)?;
        let bounds = self.parse_generic_bounds()?;
        let hi = self.hi();
        Ok(WhereBoundPredicate { span: self.mk_span(lo, hi), bounded_ty, bounds })
    }

    /// ⟨fn_ret⟩ := ⟨ -> ⟨ty⟩ ⟩?
    fn parse_fn_ret(&mut self) -> Result<FnRetTy> {
        if advance_if!(self, Tok::RArrow) {
            Ok(FnRetTy::Ty(self.parse_type()?))
        } else {
            let hi = self.hi();
            Ok(FnRetTy::Default(self.mk_span(hi, hi)))
        }
    }

    /// ⟨fn_input⟩ := ⟨ident⟩ : &strg ⟨ty⟩
    ///             | ⟨ident⟩ : ⟨path⟩ { ⟨expr⟩ }
    ///             | ⟨ident⟩ : ⟨ty⟩
    ///             | ⟨ty⟩
    fn parse_fn_input(&mut self) -> Result<FnInput> {
        if peek!(self, Tok::Ident(_), Tok::Colon) {
            let bind = self.parse_ident()?;
            expect!(self, Tok::Colon)?;
            if advance_if!(self, Tok::And, Tok::Strg) {
                // ⟨ident⟩ : &strg ⟨ty⟩
                Ok(FnInput::StrgRef(bind, self.parse_type()?, self.next_node_id()))
            } else if peek!(self, Tok::Ident(_)) {
                let path = self.parse_path()?;
                if peek!(self, OpenDelim(Brace), Tok::Ident(_), Tok::Colon) {
                    // ⟨ident⟩ : ⟨ty⟩
                    let bty = self.path_to_bty(path);
                    let ty = self.parse_bty_exists(bty)?;
                    Ok(FnInput::Ty(Some(bind), ty, self.next_node_id()))
                } else if peek!(self, OpenDelim(Brace)) {
                    // ⟨ident⟩ : ⟨path⟩ { ⟨expr⟩ }
                    delimited(self, Brace, |cx| {
                        let pred = cx.parse_expr(true)?;
                        Ok(FnInput::Constr(bind, path, pred, cx.next_node_id()))
                    })
                } else {
                    // ⟨ident⟩ : ⟨ty⟩
                    let bty = self.path_to_bty(path);
                    let ty = self.parse_bty_rhs(bty)?;
                    Ok(FnInput::Ty(Some(bind), ty, self.next_node_id()))
                }
            } else {
                // ⟨ident⟩ : ⟨ty⟩
                Ok(FnInput::Ty(Some(bind), self.parse_type()?, self.next_node_id()))
            }
        } else {
            // ⟨ty⟩
            Ok(FnInput::Ty(None, self.parse_type()?, self.next_node_id()))
        }
    }

    /// ⟨asyncness⟩ := async?
    fn parse_asyncness(&mut self) -> Async {
        let lo = self.lo();
        if advance_if!(self, Tok::Async) {
            Async::Yes { node_id: self.next_node_id(), span: self.mk_span(lo, self.hi()) }
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
    pub(crate) fn parse_type(&mut self) -> Result<Ty> {
        let lo = self.lo();
        let kind = if advance_if!(self, Tok::Underscore) {
            TyKind::Hole
        } else if peek!(self, OpenDelim(Parenthesis)) {
            // ( ⟨ty⟩,* )
            let (mut tys, trailing) = punctuated(self, Parenthesis, Comma, |cx| cx.parse_type())?;
            if tys.len() == 1 && !trailing {
                return Ok(tys.remove(0));
            } else {
                TyKind::Tuple(tys)
            }
        } else if peek!(self, OpenDelim(Brace)) {
            delimited(self, Brace, |cx| {
                if peek!(cx, Tok::Ident(_), Tok::Comma | Tok::Dot | Tok::Colon) {
                    // { ⟨ident⟩ ⟨,⟨ident⟩⟩* . ⟨ty⟩ | ⟨expr⟩ }
                    cx.parse_general_exists()
                } else {
                    // { ⟨ty⟩ | ⟨expr⟩ }
                    let ty = cx.parse_type()?;
                    expect!(cx, Tok::Caret)?;
                    let pred = cx.parse_expr(true)?;
                    Ok(TyKind::Constr(pred, Box::new(ty)))
                }
            })?
        } else if advance_if!(self, Tok::And) {
            //  & mut? ⟨ty⟩
            let mutbl = if advance_if!(self, Tok::Mut) { Mutability::Mut } else { Mutability::Not };
            TyKind::Ref(mutbl, Box::new(self.parse_type()?))
        } else if advance_if!(self, OpenDelim(Bracket)) {
            let ty = self.parse_type()?;
            if advance_if!(self, Tok::Semi) {
                // [ ⟨ty⟩ ; ⟨const_arg⟩ ]
                let len = self.parse_const_arg()?;
                expect!(self, CloseDelim(Bracket))?;
                TyKind::Array(Box::new(ty), len)
            } else {
                // [ ⟨ty⟩ ] ⟨[ ⟨refine_arg⟩,* ]⟩
                expect!(self, CloseDelim(Bracket))?;
                let hi = self.hi();
                let kind = BaseTyKind::Slice(Box::new(ty));
                let bty = BaseTy { kind, span: self.mk_span(lo, hi) };
                return self.parse_bty_rhs(bty);
            }
        } else if advance_if!(self, Tok::Impl) {
            // impl ⟨bounds⟩
            TyKind::ImplTrait(self.next_node_id(), self.parse_generic_bounds()?)
        } else if peek!(self, Tok::Ident(_)) {
            let path = self.parse_path()?;
            let bty = self.path_to_bty(path);
            return self.parse_bty_rhs(bty);
        } else if peek!(self, Tok::Lt) {
            let bty = self.parse_qpath()?;
            return self.parse_bty_rhs(bty);
        } else {
            todo!("unexpected token")
        };
        let hi = self.hi();
        Ok(Ty { kind, node_id: self.next_node_id(), span: self.mk_span(lo, hi) })
    }

    /// ⟨qpath⟩ := < ⟨ty⟩ as ⟨segments⟩> :: ⟨segments⟩
    fn parse_qpath(&mut self) -> Result<BaseTy> {
        let lo = self.lo();
        expect!(self, Tok::Lt)?;
        let qself = self.parse_type()?;
        expect!(self, Tok::As)?;
        let mut segments = self.parse_segments()?;
        expect!(self, Tok::GtFollowedByGt | Tok::Gt)?;
        expect!(self, Tok::PathSep)?;
        segments.extend(self.parse_segments()?);
        let hi = self.hi();

        let path = Path {
            segments,
            refine: vec![],
            node_id: self.next_node_id(),
            span: self.mk_span(lo, hi),
        };
        let kind = BaseTyKind::Path(Some(Box::new(qself)), path);
        Ok(BaseTy { kind, span: self.mk_span(lo, hi) })
    }

    fn parse_general_exists(&mut self) -> Result<TyKind> {
        let params = sep1(self, Comma, |cx| cx.parse_refine_param(false))?;
        expect!(self, Tok::Dot)?;
        let ty = self.parse_type()?;
        let pred = if advance_if!(self, Tok::Caret) { Some(self.parse_expr(true)?) } else { None };
        Ok(TyKind::GeneralExists { params, ty: Box::new(ty), pred })
    }

    ///    ⟨bty⟩ [ ⟨refine_arg⟩,* ]
    /// |  ⟨bty⟩ { ⟨ident⟩ : ⟨expr⟩ }
    /// |  ⟨bty⟩
    fn parse_bty_rhs(&mut self, bty: BaseTy) -> Result<Ty> {
        let lo = bty.span.lo();
        if peek!(self, OpenDelim(Bracket)) {
            // ⟨bty⟩ [ ⟨refine_arg⟩,* ]
            let indices = self.parse_indices()?;
            let hi = self.hi();
            let kind = TyKind::Indexed { bty, indices };
            Ok(Ty { kind, node_id: self.next_node_id(), span: self.mk_span(lo, hi) })
        } else if peek!(self, OpenDelim(Brace)) {
            // ⟨bty⟩ { ⟨ident⟩ : ⟨expr⟩ }
            self.parse_bty_exists(bty)
        } else {
            // ⟨bty⟩
            let hi = self.hi();
            let kind = TyKind::Base(bty);
            Ok(Ty { kind, node_id: self.next_node_id(), span: self.mk_span(lo, hi) })
        }
    }

    /// ⟨bty⟩ { ⟨ident⟩ : ⟨expr⟩ }
    fn parse_bty_exists(&mut self, bty: BaseTy) -> Result<Ty> {
        let lo = bty.span.lo();
        delimited(self, Brace, |cx| {
            let bind = cx.parse_ident()?;
            expect!(cx, Tok::Colon)?;
            let pred = cx.parse_expr(true)?;
            let hi = cx.hi();
            let kind = TyKind::Exists { bind, bty, pred };
            Ok(Ty { kind, node_id: cx.next_node_id(), span: cx.mk_span(lo, hi) })
        })
    }

    fn path_to_bty(&mut self, path: Path) -> BaseTy {
        let span = path.span;
        BaseTy { kind: BaseTyKind::Path(None, path), span }
    }

    fn parse_indices(&mut self) -> Result<Indices> {
        let lo = self.lo();
        let indices = brackets(self, Comma, |cx| cx.parse_refine_arg())?;
        let hi = self.hi();
        Ok(Indices { indices, span: self.mk_span(lo, hi) })
    }

    fn parse_generic_bounds(&mut self) -> Result<GenericBounds> {
        let path = self.parse_path()?;
        Ok(vec![TraitRef { path }])
    }

    fn parse_const_arg(&mut self) -> Result<ConstArg> {
        let lo = self.lo();
        let kind = if peek!(self, Tok::Literal(_)) {
            let len = self.parse_int()?;
            ConstArgKind::Lit(len)
        } else if advance_if!(self, Tok::Underscore) {
            ConstArgKind::Infer
        } else {
            todo!("unexpected token")
        };
        let hi = self.hi();
        Ok(ConstArg { kind, span: self.mk_span(lo, hi) })
    }

    /// ⟨path⟩ := ⟨segments⟩ ⟨ ( ⟨refine_arg⟩,* ) ⟩?
    fn parse_path(&mut self) -> Result<Path> {
        let lo = self.lo();
        let segments = self.parse_segments()?;
        let refine = if peek!(self, OpenDelim(Parenthesis)) {
            parens(self, Comma, |cx| cx.parse_refine_arg())?
        } else {
            vec![]
        };
        let hi = self.hi();
        Ok(Path { segments, refine, node_id: self.next_node_id(), span: self.mk_span(lo, hi) })
    }

    /// ⟨segments⟩ := ⟨segment⟩ ⟨:: ⟨segment⟩ ⟩*
    fn parse_segments(&mut self) -> Result<Vec<PathSegment>> {
        sep1(self, Tok::PathSep, |cx| cx.parse_segment())
    }

    /// ⟨segment⟩ := ⟨ident⟩ ⟨ < ⟨generic_arg⟩,* > ⟩?
    fn parse_segment(&mut self) -> Result<PathSegment> {
        let ident = self.parse_ident()?;
        let args = opt_angle_brackets(self, |cx| cx.parse_generic_arg())?;
        Ok(PathSegment { ident, node_id: self.next_node_id(), args })
    }

    /// ⟨generic_arg⟩ := ⟨ty⟩ | ⟨ident⟩ = ⟨ty⟩
    fn parse_generic_arg(&mut self) -> Result<GenericArg> {
        let kind = if peek!(self, Tok::Ident(_), Tok::Eq) {
            let ident = self.parse_ident()?;
            expect!(self, Tok::Eq)?;
            let ty = self.parse_type()?;
            GenericArgKind::Constraint(ident, ty)
        } else {
            GenericArgKind::Type(self.parse_type()?)
        };
        Ok(GenericArg { kind, node_id: self.next_node_id() })
    }
}

impl ParseCtxt<'_> {
    /// ⟨refine_arg⟩ :=  @ ⟨ident⟩
    ///               |  # ⟨ident⟩
    ///               |  |⟨⟨refine_parm⟩,*| ⟨expr⟩
    ///               |  ⟨expr⟩
    fn parse_refine_arg(&mut self) -> Result<RefineArg> {
        let lo = self.lo();
        let arg = if advance_if!(self, Tok::At) {
            // @ ⟨ident⟩
            let bind = self.parse_ident()?;
            let hi = self.hi();
            RefineArg::Bind(bind, BindKind::At, self.mk_span(lo, hi), self.next_node_id())
        } else if advance_if!(self, Tok::Pound) {
            // # ⟨ident⟩
            let bind = self.parse_ident()?;
            let hi = self.hi();
            RefineArg::Bind(bind, BindKind::Pound, self.mk_span(lo, hi), self.next_node_id())
        } else if advance_if!(self, Caret) {
            let params = terminated(self, Comma, Caret, |cx| cx.parse_refine_param(false))?;
            let body = self.parse_expr(true)?;
            let hi = self.hi();
            RefineArg::Abs(params, body, self.mk_span(lo, hi), self.next_node_id())
        } else {
            // ⟨expr⟩
            RefineArg::Expr(self.parse_expr(true)?)
        };
        Ok(arg)
    }

    /// ⟨refine_param⟩ := ⟨mode⟩? ⟨ident⟩ ⟨ : ⟨sort⟩ ⟩?
    fn parse_refine_param(&mut self, require_sort: bool) -> Result<RefineParam> {
        let lo = self.lo();
        let mode = self.parse_param_mode();
        let ident = self.parse_ident()?;
        let sort = if require_sort {
            expect!(self, Tok::Colon)?;
            self.parse_sort()?
        } else if advance_if!(self, Tok::Colon) {
            self.parse_sort()?
        } else {
            Sort::Infer
        };
        let hi = self.hi();
        Ok(RefineParam {
            mode,
            ident,
            sort,
            span: self.mk_span(lo, hi),
            node_id: self.next_node_id(),
        })
    }

    /// ⟨mode⟩ := hrn | hdl
    fn parse_param_mode(&mut self) -> Option<ParamMode> {
        if advance_if!(self, Tok::Hrn) {
            Some(ParamMode::Horn)
        } else if advance_if!(self, Tok::Hdl) {
            Some(ParamMode::Hindley)
        } else {
            None
        }
    }

    pub(crate) fn parse_expr(&mut self, allow_struct: bool) -> Result<Expr> {
        self.parse_binops(Precedence::MIN, allow_struct)
    }

    fn parse_binops(&mut self, base: Precedence, allow_struct: bool) -> Result<Expr> {
        let mut lhs = self.expr_unary(allow_struct)?;
        loop {
            let Some((op, ntokens)) = self.peek_binop() else { break };
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
            self.cursor.advance_by(ntokens);
            let rhs = self.parse_binops(precedence, allow_struct)?;
            let span = lhs.span.to(rhs.span);
            lhs = Expr {
                kind: ExprKind::BinaryOp(op, Box::new([lhs, rhs])),
                node_id: self.next_node_id(),
                span,
            }
        }
        Ok(lhs)
    }

    fn peek_binop(&mut self) -> Option<(BinOp, usize)> {
        let op = match self.cursor.at(0) {
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

    fn expr_unary(&mut self, allow_struct: bool) -> Result<Expr> {
        let lo = self.lo();
        let kind = if advance_if!(self, Tok::Minus) {
            ExprKind::UnaryOp(UnOp::Neg, Box::new(self.expr_unary(allow_struct)?))
        } else if advance_if!(self, Tok::Not) {
            ExprKind::UnaryOp(UnOp::Not, Box::new(self.expr_unary(allow_struct)?))
        } else {
            return self.parse_trailer_expr(allow_struct);
        };
        let hi = self.hi();
        Ok(Expr { kind, node_id: self.next_node_id(), span: self.mk_span(lo, hi) })
    }

    /// ⟨trailer⟩ := ⟨epath⟩ . ⟨ident⟩
    ///            | ⟨ident⟩ ( ⟨expr⟩,* )
    ///            | ⟨atom⟩
    ///            | <⟨ty⟩ as ⟨path⟩> :: ⟨ident⟩ ( ⟨expr⟩,* )
    fn parse_trailer_expr(&mut self, allow_struct: bool) -> Result<Expr> {
        if advance_if!(self, Tok::Lt) {
            // <⟨ty⟩ as ⟨path⟩> :: ⟨ident⟩ ( ⟨expr⟩,* )
            let lo = self.lo();
            let qself = self.parse_type()?;
            expect!(self, Tok::As)?;
            let path = self.parse_path()?;
            expect!(self, Tok::GtFollowedByGt | Tok::Gt)?;
            expect!(self, Tok::PathSep)?;
            let name = self.parse_ident()?;
            let args = parens(self, Comma, |cx| cx.parse_expr(true))?;
            let kind = ExprKind::Alias(AliasReft { qself: Box::new(qself), path, name }, args);
            let hi = self.hi();
            return Ok(Expr { kind, node_id: self.next_node_id(), span: self.mk_span(lo, hi) });
        }

        let atom = self.parse_atom(allow_struct)?;
        let lo = self.lo();
        let kind = if advance_if!(self, Tok::Dot) {
            // ⟨epath⟩ . ⟨ident⟩
            let field = self.parse_ident()?;
            let ExprKind::Path(path) = atom.kind else { todo!() };
            ExprKind::Dot(path, field)
        } else if peek!(self, OpenDelim(Parenthesis)) {
            let args = parens(self, Comma, |cx| cx.parse_expr(true))?;
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
        let hi = self.hi();
        Ok(Expr { kind, node_id: self.next_node_id(), span: self.mk_span(lo, hi) })
    }

    /// ⟨atom⟩ := ⟨if_expr⟩
    ///         | ⟨lit⟩
    ///         | ( ⟨expr⟩ )
    ///         | ⟨epath⟩
    ///         | ⟨epath⟩ { ⟨constructor_arg⟩,* }
    ///         | { ⟨constructor_arg⟩,* }
    fn parse_atom(&mut self, allow_struct: bool) -> Result<Expr> {
        let lo = self.lo();
        if peek!(self, Tok::If) {
            // ⟨if_expr⟩
            self.parse_if_expr()
        } else if peek!(self, Tok::Literal(_)) {
            // ⟨lit⟩
            self.parse_lit()
        } else if peek!(self, OpenDelim(Parenthesis)) {
            delimited(self, Parenthesis, |cx| cx.parse_expr(true))
        } else if peek!(self, Tok::Ident(_)) {
            let path = self.parse_expr_path()?;
            let kind = if allow_struct && peek!(self, Tok::OpenDelim(Brace)) {
                // ⟨epath⟩ { ⟨constructor_arg⟩,* }
                let args = braces(self, Comma, |cx| cx.parse_constructor_arg())?;
                ExprKind::Constructor(Some(path), args)
            } else {
                // ⟨epath⟩
                ExprKind::Path(path)
            };
            let hi = self.hi();
            Ok(Expr { kind, node_id: self.next_node_id(), span: self.mk_span(lo, hi) })
        } else if allow_struct && peek!(self, OpenDelim(Brace)) {
            // { ⟨constructor_arg⟩,* }
            let args = braces(self, Comma, |cx| cx.parse_constructor_arg())?;
            let hi = self.hi();
            Ok(Expr {
                kind: ExprKind::Constructor(None, args),
                node_id: self.next_node_id(),
                span: self.mk_span(lo, hi),
            })
        } else {
            todo!("unexpected token {}", self.cursor.debug(10));
        }
    }

    /// ⟨constructor_arg⟩ :=  ⟨ident⟩ : ⟨expr⟩ |  ..
    fn parse_constructor_arg(&mut self) -> Result<ConstructorArg> {
        let lo = self.lo();
        if peek!(self, Tok::Ident(_)) {
            let ident = self.parse_ident()?;
            expect!(self, Tok::Colon)?;
            let expr = self.parse_expr(true)?;
            let hi = self.hi();
            Ok(ConstructorArg::FieldExpr(FieldExpr {
                ident,
                expr,
                node_id: self.next_node_id(),
                span: self.mk_span(lo, hi),
            }))
        } else if advance_if!(self, Tok::DotDot) {
            let spread = self.parse_expr(true)?;
            let hi = self.hi();
            Ok(ConstructorArg::Spread(Spread {
                expr: spread,
                node_id: self.next_node_id(),
                span: self.mk_span(lo, hi),
            }))
        } else {
            todo!("unexpected token")
        }
    }

    /// ⟨lit⟩ := "a Rust literal like an integer or a boolean"
    fn parse_lit(&mut self) -> Result<Expr> {
        let lo = self.lo();
        let lit = expect!(self, Tok::Literal(lit) => lit)?;
        let hi = self.hi();
        Ok(Expr {
            kind: ExprKind::Literal(lit),
            node_id: self.next_node_id(),
            span: self.mk_span(lo, hi),
        })
    }

    /// ⟨epath⟩ := ⟨ident⟩ ⟨ :: ⟨ident⟩ ⟩*
    fn parse_expr_path(&mut self) -> Result<ExprPath> {
        let lo = self.lo();
        let mut segments = vec![self.parse_expr_path_segment()?];
        while advance_if!(self, Tok::PathSep) {
            segments.push(self.parse_expr_path_segment()?);
        }
        let hi = self.hi();
        let span = self.mk_span(lo, hi);
        Ok(ExprPath { segments, node_id: self.next_node_id(), span })
    }

    fn parse_expr_path_segment(&mut self) -> Result<ExprPathSegment> {
        Ok(ExprPathSegment { ident: self.parse_ident()?, node_id: self.next_node_id() })
    }

    fn parse_if_expr(&mut self) -> Result<Expr> {
        let mut branches = vec![];

        loop {
            let lo = self.lo();
            expect!(self, Tok::If)?;
            let cond = self.parse_expr(false)?;
            let then_ = self.parse_block_expr()?;
            branches.push((lo, cond, then_));
            expect!(self, Tok::Else)?;

            if !peek!(self, Tok::If) {
                break;
            }
        }
        let mut else_ = self.parse_block_expr()?;

        let hi = self.hi();
        while let Some((lo, cond, then_)) = branches.pop() {
            else_ = Expr {
                kind: ExprKind::IfThenElse(Box::new([cond, then_, else_])),
                node_id: self.next_node_id(),
                span: self.mk_span(lo, hi),
            };
        }
        Ok(else_)
    }

    /// ⟨block_expr⟩ := { ⟨expr⟩ }
    fn parse_block_expr(&mut self) -> Result<Expr> {
        delimited(self, Brace, |cx| cx.parse_expr(true))
    }

    fn parse_ident(&mut self) -> Result<Ident> {
        let lo = self.lo();
        let name = expect!(self, Tok::Ident(name) => name)?;
        let hi = self.hi();
        Ok(Ident { name, span: self.mk_span(lo, hi) })
    }

    fn parse_int<T: FromStr>(&mut self) -> Result<T> {
        let lit = expect!(self, Tok::Literal(lit) => lit)?;
        if let LitKind::Integer = lit.kind {
            if let Ok(value) = lit.symbol.as_str().parse::<T>() {
                return Ok(value);
            }
        }
        todo!("unexpected token")
    }
}

impl ParseCtxt<'_> {
    /// ⟨sort⟩ :=  ⟨base_sort⟩
    ///         |  ( ⟨base_sort⟩,* ) -> ⟨base_sort⟩
    ///         |  ⟨base_sort⟩ -> ⟨base_sort⟩
    fn parse_sort(&mut self) -> Result<Sort> {
        if peek!(self, OpenDelim(Parenthesis)) {
            // ( ⟨base_sort⟩,* ) -> ⟨base_sort⟩
            let inputs = parens(self, Comma, |cx| cx.parse_base_sort())?;
            expect!(self, Tok::RArrow)?;
            let output = self.parse_base_sort()?;
            Ok(Sort::Func { inputs, output })
        } else {
            let bsort = self.parse_base_sort()?;
            if advance_if!(self, Tok::RArrow) {
                // ⟨base_sort⟩ -> ⟨base_sort⟩
                let output = self.parse_base_sort()?;
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
    fn parse_base_sort(&mut self) -> Result<BaseSort> {
        if advance_if!(self, Tok::BitVec) {
            expect!(self, Tok::Lt)?;
            let len = self.parse_int()?;
            expect!(self, Tok::Gt | Tok::GtFollowedByGt)?;
            Ok(BaseSort::BitVec(len))
        } else {
            let segments = sep1(self, Tok::PathSep, |cx| cx.parse_ident())?;
            let args = opt_angle_brackets(self, |cx| cx.parse_base_sort())?;
            let path = SortPath { segments, args, node_id: self.next_node_id() };
            Ok(BaseSort::Path(path))
        }
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
