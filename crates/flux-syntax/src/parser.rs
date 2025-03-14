use std::str::FromStr;

use crate::{
    ParseCtxt, ParseError,
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
        ParamMode, Path, PathSegment, QualNames, Qualifier, RefineArg, RefineParam, RefineParams,
        Requires, Sort, SortDecl, SortPath, SpecFunc, Spread, TraitAssocReft, TraitRef, Ty,
        TyAlias, TyKind, UnOp, VariantDef, VariantRet, WhereBoundPredicate,
    },
};

macro_rules! advance_if {
    ($tokens:expr, $($pat:pat),+) => {{
        let tokens = &mut *$tokens;
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
    ($tokens:expr, $pat:pat $(if $guard:expr)?) => {{
        expect!($tokens, $pat $(if $guard)? => ())
    }};
    ($tokens:expr, $pat:pat $(if $guard:expr)? => $arm:expr) => {{
        let tokens = &mut *$tokens;
        let tok = tokens.next();
        match tok {
            $pat $(if $guard)? => Ok($arm),
            _ => todo!("unexpected token {}", tokens.debug(10))
        }
    }};
}

#[macro_export]
macro_rules! peek {
    ($tokens:expr, $($pat:pat),+) => {{
        let tokens = &mut *$tokens;
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
    pub(crate) fn parse_yes_or_no_with_reason(&mut self, tokens: &mut Cursor) -> Result<bool> {
        let ident = expect!(tokens, Tok::Ident(ident) => ident)?;
        let yes = match ident.as_str() {
            s @ ("yes" | "no") => {
                if advance_if!(tokens, Tok::Comma) {
                    expect!(tokens, Tok::Ident(sym) if sym.as_str() == "reason")?;
                    expect!(tokens, Tok::Eq)?;
                    expect!(tokens, Tok::Literal(_))?;
                }
                s == "yes"
            }
            "reason" => {
                expect!(tokens, Tok::Eq)?;
                expect!(tokens, Tok::Literal(_))?;
                true
            }
            _ => todo!("unexpected token"),
        };
        Ok(yes)
    }

    pub(crate) fn parse_qual_names(&mut self, tokens: &mut Cursor) -> Result<QualNames> {
        let names = terminated(tokens, Comma, Tok::Eof, |tokens| self.parse_ident(tokens))?;
        Ok(QualNames { names })
    }

    pub(crate) fn parse_generics(&mut self, tokens: &mut Cursor) -> Result<Generics> {
        let lo = tokens.lo();
        let params =
            terminated(tokens, Comma, Tok::Eof, |tokens| self.parse_generic_param(tokens))?;
        let hi = tokens.hi();
        Ok(Generics { params, predicates: None, span: self.mk_span(lo, hi) })
    }

    pub(crate) fn parse_flux_items(&mut self, tokens: &mut Cursor) -> Result<Vec<Item>> {
        let mut items = vec![];
        while !peek!(tokens, Tok::Eof) {
            items.push(self.parse_flux_item(tokens)?);
        }
        expect!(tokens, Tok::Eof)?;
        Ok(items)
    }
    fn parse_flux_item(&mut self, tokens: &mut Cursor) -> Result<Item> {
        if peek!(tokens, Tok::Fn) {
            self.parse_reft_func(tokens).map(Item::FuncDef)
        } else if peek!(tokens, Tok::Local | Tok::Qualifier) {
            self.parse_qualifier(tokens).map(Item::Qualifier)
        } else if peek!(tokens, Tok::Opaque) {
            self.parse_sort_decl(tokens).map(Item::SortDecl)
        } else {
            todo!("unexpected token")
        }
    }

    fn parse_reft_func(&mut self, tokens: &mut Cursor) -> Result<SpecFunc> {
        expect!(tokens, Tok::Fn)?;
        let name = self.parse_ident(tokens)?;
        let sort_vars = opt_angle_brackets(tokens, |tokens| self.parse_ident(tokens))?;
        let params = parens(tokens, Comma, |tokens| self.parse_refine_param(tokens, true))?;
        expect!(tokens, Tok::RArrow)?;
        let output = self.parse_sort(tokens)?;
        let body = if peek!(tokens, OpenDelim(Brace)) {
            Some(self.parse_block_expr(tokens)?)
        } else {
            expect!(tokens, Tok::Semi)?;
            None
        };
        Ok(SpecFunc { name, sort_vars, params, output, body })
    }

    fn parse_qualifier(&mut self, tokens: &mut Cursor) -> Result<Qualifier> {
        let lo = tokens.lo();
        let local = advance_if!(tokens, Tok::Local);
        expect!(tokens, Tok::Qualifier)?;
        let name = self.parse_ident(tokens)?;
        let params = parens(tokens, Comma, |tokens| self.parse_refine_param(tokens, true))?;
        let expr = self.parse_block_expr(tokens)?;
        let hi = tokens.hi();
        Ok(Qualifier { global: !local, name, params, expr, span: self.mk_span(lo, hi) })
    }

    fn parse_sort_decl(&mut self, tokens: &mut Cursor) -> Result<SortDecl> {
        expect!(tokens, Tok::Opaque)?;
        expect!(tokens, Tok::Sort)?;
        let name = self.parse_ident(tokens)?;
        expect!(tokens, Tok::Semi)?;
        Ok(SortDecl { name })
    }

    pub(crate) fn parse_trait_assoc_refts(
        &mut self,
        tokens: &mut Cursor,
    ) -> Result<Vec<TraitAssocReft>> {
        let mut assoc_refts = vec![];
        while !peek!(tokens, Tok::Eof) {
            assoc_refts.push(self.parse_trait_assoc_reft(tokens)?);
        }
        expect!(tokens, Tok::Eof)?;
        Ok(assoc_refts)
    }

    /// ⟨trait_assoc_reft⟩ := fn ⟨ident⟩ ( ⟨refine_param⟩,* ) -> ⟨base_sort⟩ ;?
    ///                     | fn ⟨ident⟩ ( ⟨refine_param⟩,* ) -> ⟨base_sort⟩ ⟨block_expr⟩
    fn parse_trait_assoc_reft(&mut self, tokens: &mut Cursor) -> Result<TraitAssocReft> {
        let lo = tokens.lo();
        expect!(tokens, Tok::Fn)?;
        let name = self.parse_ident(tokens)?;
        let params = parens(tokens, Comma, |tokens| self.parse_refine_param(tokens, true))?;
        expect!(tokens, Tok::RArrow)?;
        let output = self.parse_base_sort(tokens)?;
        let body = if peek!(tokens, OpenDelim(Brace)) {
            Some(self.parse_block_expr(tokens)?)
        } else {
            advance_if!(tokens, Tok::Semi);
            None
        };
        let hi = tokens.hi();
        Ok(TraitAssocReft { name, params, output, body, span: self.mk_span(lo, hi) })
    }

    pub(crate) fn parse_impl_assoc_refts(
        &mut self,
        tokens: &mut Cursor,
    ) -> Result<Vec<ImplAssocReft>> {
        let mut assoc_refts = vec![];
        while !peek!(tokens, Tok::Eof) {
            assoc_refts.push(self.parse_impl_assoc_reft(tokens)?);
        }
        expect!(tokens, Tok::Eof)?;
        Ok(assoc_refts)
    }

    /// ⟨impl_assoc_reft⟩ := fn ⟨ident⟩ ( ⟨refine_param⟩,* ) -> ⟨base_sort⟩ ⟨block_expr⟩
    fn parse_impl_assoc_reft(&mut self, tokens: &mut Cursor) -> Result<ImplAssocReft> {
        let lo = tokens.lo();
        expect!(tokens, Tok::Fn)?;
        let name = self.parse_ident(tokens)?;
        let params = parens(tokens, Comma, |tokens| self.parse_refine_param(tokens, true))?;
        expect!(tokens, Tok::RArrow)?;
        let output = self.parse_base_sort(tokens)?;
        let body = self.parse_block_expr(tokens)?;
        let hi = tokens.hi();
        Ok(ImplAssocReft { name, params, output, body, span: self.mk_span(lo, hi) })
    }

    pub(crate) fn parse_refined_by(&mut self, tokens: &mut Cursor) -> Result<RefineParams> {
        let mut params = vec![];
        while !peek!(tokens, Tok::Eof) {
            params.push(self.parse_refine_param(tokens, true)?);
            if !advance_if!(tokens, Tok::Comma) {
                break;
            }
        }
        expect!(tokens, Tok::Eof)?;
        Ok(params)
    }

    /// ⟨variant⟩ := ⟨fields⟩ -> ⟨variant_ret⟩
    ///            | ⟨fields⟩
    ///            | ⟨variant_ret⟩
    pub(crate) fn parse_variant(&mut self, tokens: &mut Cursor) -> Result<VariantDef> {
        let lo = tokens.lo();
        let mut fields = vec![];
        let mut ret = None;
        if peek!(tokens, OpenDelim(Parenthesis | Brace)) {
            fields = self.parse_fields(tokens)?;
            if advance_if!(tokens, Tok::RArrow) {
                ret = Some(self.parse_variant_ret(tokens)?);
            }
        } else {
            ret = Some(self.parse_variant_ret(tokens)?);
        };
        let hi = tokens.hi();
        Ok(VariantDef { fields, ret, node_id: self.next_node_id(), span: self.mk_span(lo, hi) })
    }

    /// ⟨fields⟩ := ( ⟨ty⟩,* ) | { ⟨ty⟩,* }
    fn parse_fields(&mut self, tokens: &mut Cursor) -> Result<Vec<Ty>> {
        if peek!(tokens, OpenDelim(Parenthesis)) {
            parens(tokens, Comma, |tokens| self.parse_type(tokens))
        } else if peek!(tokens, OpenDelim(Brace)) {
            braces(tokens, Comma, |tokens| self.parse_type(tokens))
        } else {
            todo!("unexpected")
        }
    }

    /// ⟨variant_ret⟩ := ⟨path⟩ ⟨ [ ⟨refine_arg⟩,? ] ⟩?
    fn parse_variant_ret(&mut self, tokens: &mut Cursor) -> Result<VariantRet> {
        let path = self.parse_path(tokens)?;
        let indices = if peek!(tokens, OpenDelim(Bracket)) {
            self.parse_indices(tokens)?
        } else {
            let hi = tokens.hi();
            Indices { indices: vec![], span: self.mk_span(hi, hi) }
        };
        Ok(VariantRet { path, indices })
    }

    pub(crate) fn parse_type_alias(&mut self, tokens: &mut Cursor) -> Result<TyAlias> {
        let lo = tokens.lo();
        expect!(tokens, Tok::Type)?;
        let ident = self.parse_ident(tokens)?;
        let generics = self.parse_opt_generics(tokens)?;
        let params = if peek!(tokens, OpenDelim(Parenthesis)) {
            parens(tokens, Comma, |tokens| self.parse_refine_param(tokens, true))?
        } else {
            vec![]
        };
        let index = if peek!(tokens, OpenDelim(Bracket)) {
            Some(delimited(tokens, Bracket, |tokens| self.parse_refine_param(tokens, true))?)
        } else {
            None
        };
        expect!(tokens, Tok::Eq)?;
        let ty = self.parse_type(tokens)?;
        let hi = tokens.hi();
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

    fn parse_opt_generics(&mut self, tokens: &mut Cursor) -> Result<Generics> {
        if !peek!(tokens, Tok::Lt) {
            let hi = tokens.hi();
            return Ok(Generics { params: vec![], predicates: None, span: self.mk_span(hi, hi) });
        }
        let lo = tokens.lo();
        let params = angle_brackets(tokens, |tokens| self.parse_generic_param(tokens))?;
        let hi = tokens.hi();
        Ok(Generics { params, predicates: None, span: self.mk_span(lo, hi) })
    }

    fn parse_generic_param(&mut self, tokens: &mut Cursor) -> Result<GenericParam> {
        let name = self.parse_ident(tokens)?;
        let mut kind = GenericParamKind::Type;
        if advance_if!(tokens, Tok::As) {
            kind = match expect!(tokens, Tok::Ident(sym) => sym)?.as_str() {
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
    pub(crate) fn parse_fn_sig(&mut self, tokens: &mut Cursor) -> Result<FnSig> {
        let lo = tokens.lo();
        let asyncness = self.parse_asyncness(tokens);
        expect!(tokens, Tok::Fn)?;
        let ident =
            if peek!(tokens, Tok::Ident(_)) { Some(self.parse_ident(tokens)?) } else { None };
        let mut generics = self.parse_opt_generics(tokens)?;
        let params = if peek!(tokens, OpenDelim(Bracket)) {
            brackets(tokens, Comma, |tokens| self.parse_refine_param(tokens, false))?
        } else {
            vec![]
        };
        let (inputs, _) =
            punctuated(tokens, Parenthesis, Comma, |tokens| self.parse_fn_input(tokens))?;
        let returns = self.parse_fn_ret(tokens)?;
        let requires = self.parse_opt_requires(tokens)?;
        let ensures = self.parse_opt_ensures(tokens)?;
        generics.predicates = self.parse_opt_where(tokens)?;
        let hi = tokens.hi();
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
    fn parse_opt_requires(&mut self, tokens: &mut Cursor) -> Result<Vec<Requires>> {
        let mut requires = vec![];

        if !tokens.advance_if(Tok::Requires) {
            return Ok(requires);
        }

        while !peek!(tokens, Tok::Ensures | Tok::Where | Tok::Eof) {
            requires.push(self.parse_requires_clause(tokens)?);
            if !tokens.advance_if(Comma) {
                break;
            }
        }
        Ok(requires)
    }

    /// ⟨requires_clause⟩ := ⟨ forall ⟨refine_param⟩,+ . ⟩? ⟨expr⟩
    fn parse_requires_clause(&mut self, tokens: &mut Cursor) -> Result<Requires> {
        let mut params = vec![];
        if advance_if!(tokens, Tok::Forall) {
            params = sep1(tokens, Comma, |tokens| self.parse_refine_param(tokens, false))?;
            expect!(tokens, Tok::Dot)?;
        }
        let pred = self.parse_expr(tokens, true)?;
        Ok(Requires { params, pred })
    }

    /// ⟨ensures⟩ := ⟨ensures ⟨ensures_clause⟩,*⟩?
    fn parse_opt_ensures(&mut self, tokens: &mut Cursor) -> Result<Vec<Ensures>> {
        let mut ensures = vec![];

        if !advance_if!(tokens, Tok::Ensures) {
            return Ok(ensures);
        }

        while !peek!(tokens, Tok::Where | Tok::Eof) {
            ensures.push(self.parse_ensures_clause(tokens)?);
            if !tokens.advance_if(Comma) {
                break;
            }
        }
        Ok(ensures)
    }

    /// ⟨ensures_clause⟩ :=  ⟨ident⟩ : ⟨ty⟩
    ///                   |  ⟨expr⟩
    fn parse_ensures_clause(&mut self, tokens: &mut Cursor) -> Result<Ensures> {
        if peek!(tokens, Tok::Ident(_), Tok::Colon) {
            // ⟨ident⟩ : ⟨ty⟩
            let ident = self.parse_ident(tokens)?;
            expect!(tokens, Tok::Colon)?;
            let ty = self.parse_type(tokens)?;
            Ok(Ensures::Type(ident, ty, self.next_node_id()))
        } else {
            // ⟨expr⟩
            Ok(Ensures::Pred(self.parse_expr(tokens, true)?))
        }
    }

    fn parse_opt_where(&mut self, tokens: &mut Cursor) -> Result<Option<Vec<WhereBoundPredicate>>> {
        if !advance_if!(tokens, Tok::Where) {
            return Ok(None);
        }
        let mut predicates = vec![];
        while !peek!(tokens, Tok::Eof) {
            predicates.push(self.parse_where_bound(tokens)?);
            if !advance_if!(tokens, Comma) {
                break;
            }
        }
        Ok(Some(predicates))
    }

    fn parse_where_bound(&mut self, tokens: &mut Cursor) -> Result<WhereBoundPredicate> {
        let lo = tokens.lo();
        let bounded_ty = self.parse_type(tokens)?;
        expect!(tokens, Tok::Colon)?;
        let bounds = self.parse_generic_bounds(tokens)?;
        let hi = tokens.hi();
        Ok(WhereBoundPredicate { span: self.mk_span(lo, hi), bounded_ty, bounds })
    }

    /// ⟨fn_ret⟩ := ⟨ -> ⟨ty⟩ ⟩?
    fn parse_fn_ret(&mut self, tokens: &mut Cursor) -> Result<FnRetTy> {
        if tokens.advance_if(Tok::RArrow) {
            Ok(FnRetTy::Ty(self.parse_type(tokens)?))
        } else {
            let hi = tokens.hi();
            Ok(FnRetTy::Default(self.mk_span(hi, hi)))
        }
    }

    /// ⟨fn_input⟩ := ⟨ident⟩ : &strg ⟨ty⟩
    ///             | ⟨ident⟩ : ⟨path⟩ { ⟨expr⟩ }
    ///             | ⟨ident⟩ : ⟨ty⟩
    ///             | ⟨ty⟩
    fn parse_fn_input(&mut self, tokens: &mut Cursor) -> Result<FnInput> {
        if peek!(tokens, Tok::Ident(_), Tok::Colon) {
            let bind = self.parse_ident(tokens)?;
            expect!(tokens, Tok::Colon)?;
            if advance_if!(tokens, Tok::And, Tok::Strg) {
                // ⟨ident⟩ : &strg ⟨ty⟩
                Ok(FnInput::StrgRef(bind, self.parse_type(tokens)?, self.next_node_id()))
            } else if peek!(tokens, Tok::Ident(_)) {
                let path = self.parse_path(tokens)?;
                if peek!(tokens, OpenDelim(Brace), Tok::Ident(_), Tok::Colon) {
                    // ⟨ident⟩ : ⟨ty⟩
                    let bty = self.path_to_bty(path);
                    let ty = self.parse_bty_exists(bty, tokens)?;
                    Ok(FnInput::Ty(Some(bind), ty, self.next_node_id()))
                } else if peek!(tokens, OpenDelim(Brace)) {
                    // ⟨ident⟩ : ⟨path⟩ { ⟨expr⟩ }
                    delimited(tokens, Brace, |tokens| {
                        let pred = self.parse_expr(tokens, true)?;
                        Ok(FnInput::Constr(bind, path, pred, self.next_node_id()))
                    })
                } else {
                    // ⟨ident⟩ : ⟨ty⟩
                    let bty = self.path_to_bty(path);
                    let ty = self.parse_bty_rhs(bty, tokens)?;
                    Ok(FnInput::Ty(Some(bind), ty, self.next_node_id()))
                }
            } else {
                // ⟨ident⟩ : ⟨ty⟩
                Ok(FnInput::Ty(Some(bind), self.parse_type(tokens)?, self.next_node_id()))
            }
        } else {
            // ⟨ty⟩
            Ok(FnInput::Ty(None, self.parse_type(tokens)?, self.next_node_id()))
        }
    }

    /// ⟨asyncness⟩ := async?
    fn parse_asyncness(&mut self, tokens: &mut Cursor) -> Async {
        let lo = tokens.lo();
        if tokens.advance_if(Tok::Async) {
            Async::Yes { node_id: self.next_node_id(), span: self.mk_span(lo, tokens.hi()) }
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
    pub(crate) fn parse_type(&mut self, tokens: &mut Cursor) -> Result<Ty> {
        let lo = tokens.lo();
        let kind = if advance_if!(tokens, Tok::Underscore) {
            TyKind::Hole
        } else if peek!(tokens, OpenDelim(Parenthesis)) {
            // ( ⟨ty⟩,* )
            let (mut tys, trailing) =
                punctuated(tokens, Parenthesis, Comma, |tokens| self.parse_type(tokens))?;
            if tys.len() == 1 && !trailing {
                return Ok(tys.remove(0));
            } else {
                TyKind::Tuple(tys)
            }
        } else if peek!(tokens, OpenDelim(Brace)) {
            delimited(tokens, Brace, |tokens| {
                if peek!(tokens, Tok::Ident(_), Tok::Comma | Tok::Dot | Tok::Colon) {
                    // { ⟨ident⟩ ⟨,⟨ident⟩⟩* . ⟨ty⟩ | ⟨expr⟩ }
                    self.parse_general_exists(tokens)
                } else {
                    // { ⟨ty⟩ | ⟨expr⟩ }
                    let ty = self.parse_type(tokens)?;
                    expect!(tokens, Tok::Caret)?;
                    let pred = self.parse_expr(tokens, true)?;
                    Ok(TyKind::Constr(pred, Box::new(ty)))
                }
            })?
        } else if advance_if!(tokens, Tok::And) {
            //  & mut? ⟨ty⟩
            let mutbl = if tokens.advance_if(Tok::Mut) { Mutability::Mut } else { Mutability::Not };
            TyKind::Ref(mutbl, Box::new(self.parse_type(tokens)?))
        } else if advance_if!(tokens, OpenDelim(Bracket)) {
            let ty = self.parse_type(tokens)?;
            if advance_if!(tokens, Tok::Semi) {
                // [ ⟨ty⟩ ; ⟨const_arg⟩ ]
                let len = self.parse_const_arg(tokens)?;
                expect!(tokens, CloseDelim(Bracket))?;
                TyKind::Array(Box::new(ty), len)
            } else {
                // [ ⟨ty⟩ ] ⟨[ ⟨refine_arg⟩,* ]⟩
                expect!(tokens, CloseDelim(Bracket))?;
                let hi = tokens.hi();
                let kind = BaseTyKind::Slice(Box::new(ty));
                let bty = BaseTy { kind, span: self.mk_span(lo, hi) };
                return self.parse_bty_rhs(bty, tokens);
            }
        } else if tokens.advance_if(Tok::Impl) {
            // impl ⟨bounds⟩
            TyKind::ImplTrait(self.next_node_id(), self.parse_generic_bounds(tokens)?)
        } else if peek!(tokens, Tok::Ident(_)) {
            let path = self.parse_path(tokens)?;
            let bty = self.path_to_bty(path);
            return self.parse_bty_rhs(bty, tokens);
        } else if peek!(tokens, Tok::Lt) {
            let bty = self.parse_qpath(tokens)?;
            return self.parse_bty_rhs(bty, tokens);
        } else {
            todo!("unexpected token")
        };
        let hi = tokens.hi();
        Ok(Ty { kind, node_id: self.next_node_id(), span: self.mk_span(lo, hi) })
    }

    /// ⟨qpath⟩ := < ⟨ty⟩ as ⟨segments⟩> :: ⟨segments⟩
    fn parse_qpath(&mut self, tokens: &mut Cursor) -> Result<BaseTy> {
        let lo = tokens.lo();
        expect!(tokens, Tok::Lt)?;
        let qself = self.parse_type(tokens)?;
        expect!(tokens, Tok::As)?;
        let mut segments = self.parse_segments(tokens)?;
        expect!(tokens, Tok::GtFollowedByGt | Tok::Gt)?;
        expect!(tokens, Tok::PathSep)?;
        segments.extend(self.parse_segments(tokens)?);
        let hi = tokens.hi();

        let path = Path {
            segments,
            refine: vec![],
            node_id: self.next_node_id(),
            span: self.mk_span(lo, hi),
        };
        let kind = BaseTyKind::Path(Some(Box::new(qself)), path);
        Ok(BaseTy { kind, span: self.mk_span(lo, hi) })
    }

    fn parse_general_exists(&mut self, tokens: &mut Cursor) -> Result<TyKind> {
        let params = sep1(tokens, Comma, |tokens| self.parse_refine_param(tokens, false))?;
        expect!(tokens, Tok::Dot)?;
        let ty = self.parse_type(tokens)?;
        let pred = if advance_if!(tokens, Tok::Caret) {
            Some(self.parse_expr(tokens, true)?)
        } else {
            None
        };
        Ok(TyKind::GeneralExists { params, ty: Box::new(ty), pred })
    }

    ///    ⟨bty⟩ [ ⟨refine_arg⟩,* ]
    /// |  ⟨bty⟩ { ⟨ident⟩ : ⟨expr⟩ }
    /// |  ⟨bty⟩
    fn parse_bty_rhs(&mut self, bty: BaseTy, tokens: &mut Cursor) -> Result<Ty> {
        let lo = bty.span.lo();
        if peek!(tokens, OpenDelim(Bracket)) {
            // ⟨bty⟩ [ ⟨refine_arg⟩,* ]
            let indices = self.parse_indices(tokens)?;
            let hi = tokens.hi();
            let kind = TyKind::Indexed { bty, indices };
            Ok(Ty { kind, node_id: self.next_node_id(), span: self.mk_span(lo, hi) })
        } else if peek!(tokens, OpenDelim(Brace)) {
            // ⟨bty⟩ { ⟨ident⟩ : ⟨expr⟩ }
            self.parse_bty_exists(bty, tokens)
        } else {
            // ⟨bty⟩
            let hi = tokens.hi();
            let kind = TyKind::Base(bty);
            Ok(Ty { kind, node_id: self.next_node_id(), span: self.mk_span(lo, hi) })
        }
    }

    /// ⟨bty⟩ { ⟨ident⟩ : ⟨expr⟩ }
    fn parse_bty_exists(&mut self, bty: BaseTy, tokens: &mut Cursor) -> Result<Ty> {
        let lo = bty.span.lo();
        delimited(tokens, Brace, |tokens| {
            let bind = self.parse_ident(tokens)?;
            expect!(tokens, Tok::Colon)?;
            let pred = self.parse_expr(tokens, true)?;
            let hi = tokens.hi();
            let kind = TyKind::Exists { bind, bty, pred };
            Ok(Ty { kind, node_id: self.next_node_id(), span: self.mk_span(lo, hi) })
        })
    }

    fn path_to_bty(&mut self, path: Path) -> BaseTy {
        let span = path.span;
        BaseTy { kind: BaseTyKind::Path(None, path), span }
    }

    fn parse_indices(&mut self, tokens: &mut Cursor) -> Result<Indices> {
        let lo = tokens.lo();
        let indices = brackets(tokens, Comma, |tokens| self.parse_refine_arg(tokens))?;
        let hi = tokens.hi();
        Ok(Indices { indices, span: self.mk_span(lo, hi) })
    }

    fn parse_generic_bounds(&mut self, tokens: &mut Cursor) -> Result<GenericBounds> {
        let path = self.parse_path(tokens)?;
        Ok(vec![TraitRef { path }])
    }

    fn parse_const_arg(&mut self, tokens: &mut Cursor) -> Result<ConstArg> {
        let lo = tokens.lo();
        let kind = if peek!(tokens, Tok::Literal(_)) {
            let len = self.parse_int(tokens)?;
            ConstArgKind::Lit(len)
        } else if advance_if!(tokens, Tok::Underscore) {
            ConstArgKind::Infer
        } else {
            todo!("unexpected token")
        };
        let hi = tokens.hi();
        Ok(ConstArg { kind, span: self.mk_span(lo, hi) })
    }

    /// ⟨path⟩ := ⟨segments⟩ ⟨ ( ⟨refine_arg⟩,* ) ⟩?
    fn parse_path(&mut self, tokens: &mut Cursor) -> Result<Path> {
        let lo = tokens.lo();
        let segments = self.parse_segments(tokens)?;
        let refine = if peek!(tokens, OpenDelim(Parenthesis)) {
            parens(tokens, Comma, |tokens| self.parse_refine_arg(tokens))?
        } else {
            vec![]
        };
        let hi = tokens.hi();
        Ok(Path { segments, refine, node_id: self.next_node_id(), span: self.mk_span(lo, hi) })
    }

    /// ⟨segments⟩ := ⟨segment⟩ ⟨:: ⟨segment⟩ ⟩*
    fn parse_segments(&mut self, tokens: &mut Cursor) -> Result<Vec<PathSegment>> {
        sep1(tokens, Tok::PathSep, |tokens| self.parse_segment(tokens))
    }

    /// ⟨segment⟩ := ⟨ident⟩ ⟨ < ⟨generic_arg⟩,* > ⟩?
    fn parse_segment(&mut self, tokens: &mut Cursor) -> Result<PathSegment> {
        let ident = self.parse_ident(tokens)?;
        let args = opt_angle_brackets(tokens, |tokens| self.parse_generic_arg(tokens))?;
        Ok(PathSegment { ident, node_id: self.next_node_id(), args })
    }

    /// ⟨generic_arg⟩ := ⟨ty⟩ | ⟨ident⟩ = ⟨ty⟩
    fn parse_generic_arg(&mut self, tokens: &mut Cursor) -> Result<GenericArg> {
        let kind = if peek!(tokens, Tok::Ident(_), Tok::Eq) {
            let ident = self.parse_ident(tokens)?;
            expect!(tokens, Tok::Eq)?;
            let ty = self.parse_type(tokens)?;
            GenericArgKind::Constraint(ident, ty)
        } else {
            GenericArgKind::Type(self.parse_type(tokens)?)
        };
        Ok(GenericArg { kind, node_id: self.next_node_id() })
    }
}

impl ParseCtxt<'_> {
    /// ⟨refine_arg⟩ :=  @ ⟨ident⟩
    ///               |  # ⟨ident⟩
    ///               |  |⟨⟨refine_parm⟩,*| ⟨expr⟩
    ///               |  ⟨expr⟩
    fn parse_refine_arg(&mut self, tokens: &mut Cursor) -> Result<RefineArg> {
        let lo = tokens.lo();
        let arg = if tokens.advance_if(Tok::At) {
            // @ ⟨ident⟩
            let bind = self.parse_ident(tokens)?;
            let hi = tokens.hi();
            RefineArg::Bind(bind, BindKind::At, self.mk_span(lo, hi), self.next_node_id())
        } else if tokens.advance_if(Tok::Pound) {
            // # ⟨ident⟩
            let bind = self.parse_ident(tokens)?;
            let hi = tokens.hi();
            RefineArg::Bind(bind, BindKind::Pound, self.mk_span(lo, hi), self.next_node_id())
        } else if advance_if!(tokens, Caret) {
            let params =
                terminated(tokens, Comma, Caret, |tokens| self.parse_refine_param(tokens, false))?;
            let body = self.parse_expr(tokens, true)?;
            let hi = tokens.hi();
            RefineArg::Abs(params, body, self.mk_span(lo, hi), self.next_node_id())
        } else {
            // ⟨expr⟩
            RefineArg::Expr(self.parse_expr(tokens, true)?)
        };
        Ok(arg)
    }

    /// ⟨refine_param⟩ := ⟨mode⟩? ⟨ident⟩ ⟨ : ⟨sort⟩ ⟩?
    fn parse_refine_param(
        &mut self,
        tokens: &mut Cursor,
        require_sort: bool,
    ) -> Result<RefineParam> {
        let lo = tokens.lo();
        let mode = self.parse_param_mode(tokens);
        let ident = self.parse_ident(tokens)?;
        let sort = if require_sort {
            expect!(tokens, Tok::Colon)?;
            self.parse_sort(tokens)?
        } else if tokens.advance_if(Tok::Colon) {
            self.parse_sort(tokens)?
        } else {
            Sort::Infer
        };
        let hi = tokens.hi();
        Ok(RefineParam {
            mode,
            ident,
            sort,
            span: self.mk_span(lo, hi),
            node_id: self.next_node_id(),
        })
    }

    /// ⟨mode⟩ := hrn | hdl
    fn parse_param_mode(&mut self, tokens: &mut Cursor) -> Option<ParamMode> {
        if tokens.advance_if(Tok::Hrn) {
            Some(ParamMode::Horn)
        } else if tokens.advance_if(Tok::Hdl) {
            Some(ParamMode::Hindley)
        } else {
            None
        }
    }

    pub(crate) fn parse_expr(&mut self, tokens: &mut Cursor, allow_struct: bool) -> Result<Expr> {
        self.parse_binops(tokens, Precedence::MIN, allow_struct)
    }

    fn parse_binops(
        &mut self,
        tokens: &mut Cursor,
        base: Precedence,
        allow_struct: bool,
    ) -> Result<Expr> {
        let mut lhs = self.expr_unary(tokens, allow_struct)?;
        loop {
            let Some((op, ntokens)) = self.peek_binop(tokens) else { break };
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
            tokens.advance_by(ntokens);
            let rhs = self.parse_binops(tokens, precedence, allow_struct)?;
            let span = lhs.span.to(rhs.span);
            lhs = Expr {
                kind: ExprKind::BinaryOp(op, Box::new([lhs, rhs])),
                node_id: self.next_node_id(),
                span,
            }
        }
        Ok(lhs)
    }

    fn peek_binop(&mut self, tokens: &mut Cursor) -> Option<(BinOp, usize)> {
        let op = match tokens.at(0) {
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

    fn expr_unary(&mut self, tokens: &mut Cursor, allow_struct: bool) -> Result<Expr> {
        let lo = tokens.lo();
        let kind = if tokens.advance_if(Tok::Minus) {
            ExprKind::UnaryOp(UnOp::Neg, Box::new(self.expr_unary(tokens, allow_struct)?))
        } else if tokens.advance_if(Tok::Not) {
            ExprKind::UnaryOp(UnOp::Not, Box::new(self.expr_unary(tokens, allow_struct)?))
        } else {
            return self.parse_trailer_expr(tokens, allow_struct);
        };
        let hi = tokens.hi();
        Ok(Expr { kind, node_id: self.next_node_id(), span: self.mk_span(lo, hi) })
    }

    /// ⟨trailer⟩ := ⟨expr_path⟩ . ⟨ident⟩
    ///            | ⟨ident⟩ ( ⟨expr⟩,* )
    ///            | ⟨atom⟩
    ///            | <⟨ty⟩ as ⟨path⟩> :: ⟨ident⟩ ( ⟨expr⟩,* )
    fn parse_trailer_expr(&mut self, tokens: &mut Cursor, allow_struct: bool) -> Result<Expr> {
        if advance_if!(tokens, Tok::Lt) {
            // <⟨ty⟩ as ⟨path⟩> :: ⟨ident⟩ ( ⟨expr⟩,* )
            let lo = tokens.lo();
            let qself = self.parse_type(tokens)?;
            expect!(tokens, Tok::As)?;
            let path = self.parse_path(tokens)?;
            expect!(tokens, Tok::GtFollowedByGt | Tok::Gt)?;
            expect!(tokens, Tok::PathSep)?;
            let name = self.parse_ident(tokens)?;
            let args = parens(tokens, Comma, |tokens| self.parse_expr(tokens, true))?;
            let kind = ExprKind::Alias(AliasReft { qself: Box::new(qself), path, name }, args);
            let hi = tokens.hi();
            return Ok(Expr { kind, node_id: self.next_node_id(), span: self.mk_span(lo, hi) });
        }

        let atom = self.parse_atom(tokens, allow_struct)?;
        let lo = tokens.lo();
        let kind = if tokens.advance_if(Tok::Dot) {
            // ⟨expr_path⟩ . ⟨ident⟩
            let field = self.parse_ident(tokens)?;
            let ExprKind::Path(path) = atom.kind else { todo!() };
            ExprKind::Dot(path, field)
        } else if peek!(tokens, OpenDelim(Parenthesis)) {
            let args = parens(tokens, Comma, |tokens| self.parse_expr(tokens, true))?;
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
        let hi = tokens.hi();
        Ok(Expr { kind, node_id: self.next_node_id(), span: self.mk_span(lo, hi) })
    }

    /// ⟨atom⟩ := ⟨if_expr⟩
    ///         | ⟨lit⟩
    ///         | ( ⟨expr⟩ )
    ///         | ⟨expr_path⟩
    ///         | ⟨expr_path⟩ { ⟨constructor_arg⟩,* }
    ///         | { ⟨constructor_arg⟩,* }
    fn parse_atom(&mut self, tokens: &mut Cursor, allow_struct: bool) -> Result<Expr> {
        let lo = tokens.lo();
        if peek!(tokens, Tok::If) {
            // ⟨if_expr⟩
            self.parse_if_expr(tokens)
        } else if peek!(tokens, Tok::Literal(_)) {
            // ⟨lit⟩
            self.parse_lit(tokens)
        } else if peek!(tokens, OpenDelim(Parenthesis)) {
            delimited(tokens, Parenthesis, |tokens| self.parse_expr(tokens, true))
        } else if peek!(tokens, Tok::Ident(_)) {
            let path = self.parse_expr_path(tokens)?;
            let kind = if allow_struct && peek!(tokens, Tok::OpenDelim(Brace)) {
                // ⟨expr_path⟩ { ⟨constructor_arg⟩,* }
                let args = braces(tokens, Comma, |tokens| self.parse_constructor_arg(tokens))?;
                ExprKind::Constructor(Some(path), args)
            } else {
                // ⟨expr_path⟩
                ExprKind::Path(path)
            };
            let hi = tokens.hi();
            Ok(Expr { kind, node_id: self.next_node_id(), span: self.mk_span(lo, hi) })
        } else if allow_struct && peek!(tokens, OpenDelim(Brace)) {
            // { ⟨constructor_arg⟩,* }
            let args = braces(tokens, Comma, |tokens| self.parse_constructor_arg(tokens))?;
            let hi = tokens.hi();
            Ok(Expr {
                kind: ExprKind::Constructor(None, args),
                node_id: self.next_node_id(),
                span: self.mk_span(lo, hi),
            })
        } else {
            todo!("unexpected token {}", tokens.debug(10));
        }
    }

    /// ⟨constructor_arg⟩ :=  ⟨ident⟩ : ⟨expr⟩ |  ..
    fn parse_constructor_arg(&mut self, tokens: &mut Cursor) -> Result<ConstructorArg> {
        let lo = tokens.lo();
        if peek!(tokens, Tok::Ident(_)) {
            let ident = self.parse_ident(tokens)?;
            expect!(tokens, Tok::Colon)?;
            let expr = self.parse_expr(tokens, true)?;
            let hi = tokens.hi();
            Ok(ConstructorArg::FieldExpr(FieldExpr {
                ident,
                expr,
                node_id: self.next_node_id(),
                span: self.mk_span(lo, hi),
            }))
        } else if advance_if!(tokens, Tok::DotDot) {
            let spread = self.parse_expr(tokens, true)?;
            let hi = tokens.hi();
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
    fn parse_lit(&mut self, tokens: &mut Cursor) -> Result<Expr> {
        let lo = tokens.lo();
        let lit = expect!(tokens, Tok::Literal(lit) => lit)?;
        let hi = tokens.hi();
        Ok(Expr {
            kind: ExprKind::Literal(lit),
            node_id: self.next_node_id(),
            span: self.mk_span(lo, hi),
        })
    }

    /// ⟨expr_path⟩ := ⟨ident⟩ ⟨ :: ⟨ident⟩ ⟩*
    fn parse_expr_path(&mut self, tokens: &mut Cursor) -> Result<ExprPath> {
        let lo = tokens.lo();
        let mut segments = vec![self.parse_expr_path_segment(tokens)?];
        while tokens.advance_if(Tok::PathSep) {
            segments.push(self.parse_expr_path_segment(tokens)?);
        }
        let hi = tokens.hi();
        let span = self.mk_span(lo, hi);
        Ok(ExprPath { segments, node_id: self.next_node_id(), span })
    }

    fn parse_expr_path_segment(&mut self, tokens: &mut Cursor) -> Result<ExprPathSegment> {
        Ok(ExprPathSegment { ident: self.parse_ident(tokens)?, node_id: self.next_node_id() })
    }

    fn parse_if_expr(&mut self, tokens: &mut Cursor) -> Result<Expr> {
        let mut branches = vec![];

        loop {
            let lo = tokens.lo();
            expect!(tokens, Tok::If)?;
            let cond = self.parse_expr(tokens, false)?;
            let then_ = self.parse_block_expr(tokens)?;
            branches.push((lo, cond, then_));
            expect!(tokens, Tok::Else)?;

            if !peek!(tokens, Tok::If) {
                break;
            }
        }
        let mut else_ = self.parse_block_expr(tokens)?;

        let hi = tokens.hi();
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
    fn parse_block_expr(&mut self, tokens: &mut Cursor) -> Result<Expr> {
        delimited(tokens, Brace, |tokens| self.parse_expr(tokens, true))
    }

    fn parse_ident(&mut self, tokens: &mut Cursor) -> Result<Ident> {
        let lo = tokens.lo();
        let name = expect!(tokens, Tok::Ident(name) => name)?;
        let hi = tokens.hi();
        Ok(Ident { name, span: self.mk_span(lo, hi) })
    }

    fn parse_int<T: FromStr>(&mut self, tokens: &mut Cursor) -> Result<T> {
        let lit = expect!(tokens, Tok::Literal(lit) => lit)?;
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
    fn parse_sort(&mut self, tokens: &mut Cursor) -> Result<Sort> {
        if peek!(tokens, OpenDelim(Parenthesis)) {
            // ( ⟨base_sort⟩,* ) -> ⟨base_sort⟩
            let inputs = parens(tokens, Comma, |tokens| self.parse_base_sort(tokens))?;
            expect!(tokens, Tok::RArrow)?;
            let output = self.parse_base_sort(tokens)?;
            Ok(Sort::Func { inputs, output })
        } else {
            let bsort = self.parse_base_sort(tokens)?;
            if tokens.advance_if(Tok::RArrow) {
                // ⟨base_sort⟩ -> ⟨base_sort⟩
                let output = self.parse_base_sort(tokens)?;
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
    fn parse_base_sort(&mut self, tokens: &mut Cursor) -> Result<BaseSort> {
        if advance_if!(tokens, Tok::BitVec) {
            expect!(tokens, Tok::Lt)?;
            let len = self.parse_int(tokens)?;
            expect!(tokens, Tok::Gt | Tok::GtFollowedByGt)?;
            Ok(BaseSort::BitVec(len))
        } else {
            let segments = sep1(tokens, Tok::PathSep, |tokens| self.parse_ident(tokens))?;
            let args = opt_angle_brackets(tokens, |tokens| self.parse_base_sort(tokens))?;
            let path = SortPath { segments, args, node_id: self.next_node_id() };
            Ok(BaseSort::Path(path))
        }
    }
}

fn opt_angle_brackets<T>(
    tokens: &mut Cursor,
    parse: impl FnMut(&mut Cursor) -> Result<T>,
) -> Result<Vec<T>> {
    if !peek!(tokens, Tok::Lt) {
        return Ok(vec![]);
    }
    angle_brackets(tokens, parse)
}

fn angle_brackets<T>(
    tokens: &mut Cursor,
    mut parse: impl FnMut(&mut Cursor) -> Result<T>,
) -> Result<Vec<T>> {
    expect!(tokens, Tok::Lt)?;
    let mut items = vec![];
    while !peek!(tokens, Tok::Gt | Tok::GtFollowedByGt) {
        items.push(parse(tokens)?);

        if !tokens.advance_if(Comma) {
            break;
        }
    }
    expect!(tokens, Tok::Gt | Tok::GtFollowedByGt)?;
    Ok(items)
}

#[track_caller]
fn delimited<T>(
    tokens: &mut Cursor,
    delim: Delimiter,
    parse: impl FnOnce(&mut Cursor) -> Result<T>,
) -> Result<T> {
    expect!(tokens, OpenDelim(d) if d == delim)?;
    let r = parse(tokens)?;
    expect!(tokens, CloseDelim(d) if d == delim)?;
    Ok(r)
}

fn brackets<T>(
    tokens: &mut Cursor,
    sep: Tok,
    parse: impl FnMut(&mut Cursor) -> Result<T>,
) -> Result<Vec<T>> {
    Ok(punctuated(tokens, Bracket, sep, parse)?.0)
}

fn parens<T>(
    tokens: &mut Cursor,
    sep: Tok,
    parse: impl FnMut(&mut Cursor) -> Result<T>,
) -> Result<Vec<T>> {
    Ok(punctuated(tokens, Parenthesis, sep, parse)?.0)
}

fn braces<T>(
    tokens: &mut Cursor,
    sep: Tok,
    parse: impl FnMut(&mut Cursor) -> Result<T>,
) -> Result<Vec<T>> {
    Ok(punctuated(tokens, Brace, sep, parse)?.0)
}

#[track_caller]
fn punctuated<T>(
    tokens: &mut Cursor,
    delim: Delimiter,
    sep: Tok,
    mut parse: impl FnMut(&mut Cursor) -> Result<T>,
) -> Result<(Vec<T>, bool)> {
    expect!(tokens, OpenDelim(d) if delim == d)?;
    let mut items = vec![];

    let mut trailing = false;
    while tokens.at(0) != CloseDelim(delim) {
        items.push(parse(tokens)?);

        trailing = tokens.advance_if(sep);
        if !trailing {
            break;
        }
    }
    expect!(tokens, CloseDelim(d) if d == delim)?;
    Ok((items, trailing))
}

fn sep1<T>(
    tokens: &mut Cursor,
    sep: Tok,
    mut parse: impl FnMut(&mut Cursor) -> Result<T>,
) -> Result<Vec<T>> {
    let mut items = vec![parse(tokens)?];
    while tokens.advance_if(sep) {
        items.push(parse(tokens)?);
    }
    Ok(items)
}

fn terminated<T>(
    tokens: &mut Cursor,
    sep: Tok,
    end: Tok,
    mut parse: impl FnMut(&mut Cursor) -> Result<T>,
) -> Result<Vec<T>> {
    let mut items = vec![];
    while tokens.at(0) != end {
        items.push(parse(tokens)?);
        if !tokens.advance_if(sep) {
            break;
        }
    }
    expect!(tokens, t if t == end)?;
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
