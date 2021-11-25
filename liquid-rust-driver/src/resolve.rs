use hir::def_id::DefId;
use itertools::{Either, Itertools};
use liquid_rust_common::{errors::ErrorReported, index::IndexGen, iter::IterExt};
use liquid_rust_core::ty::{self, Name, ParamTy};
use liquid_rust_syntax::ast;
use quickscope::ScopeMap;
use rustc_hash::FxHashMap;
use rustc_hir::{self as hir, def_id::LocalDefId};
use rustc_middle::ty::TyCtxt;
use rustc_session::Session;
use rustc_span::{sym, symbol::kw, MultiSpan, Span, Symbol};

pub struct Resolver<'tcx> {
    tcx: TyCtxt<'tcx>,
    diagnostics: Diagnostics<'tcx>,
    symbols: Symbols,
}

struct Symbols {
    int: Symbol,
}
struct Matcher<'a> {
    regions: FxHashMap<Symbol, &'a ast::Ty>,
}

struct Matching<'tcx> {
    requires: FxHashMap<Symbol, &'tcx hir::Ty<'tcx>>,
    args: Vec<&'tcx hir::Ty<'tcx>>,
    ret: &'tcx hir::Ty<'tcx>,
    ensures: FxHashMap<Symbol, &'tcx hir::Ty<'tcx>>,
}

enum ParamTyOrBaseTy {
    BaseTy(ty::BaseTy),
    ParamTy(ty::ParamTy),
}

struct Diagnostics<'tcx> {
    sess: &'tcx Session,
    errors: usize,
}

struct Subst {
    exprs: ScopeMap<Symbol, ty::Var>,
    regions: FxHashMap<Symbol, Name>,
    types: FxHashMap<DefId, ParamTy>,
}

impl<'tcx> Resolver<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            diagnostics: Diagnostics::new(tcx.sess),
            symbols: Symbols::new(),
        }
    }

    pub fn resolve(
        tcx: TyCtxt<'tcx>,
        def_id: LocalDefId,
        fn_sig: ast::FnSig,
    ) -> Result<ty::FnSig, ErrorReported> {
        let mut resolver = Self::new(tcx);

        let mut subst = Subst::new();
        let name_gen = IndexGen::new();

        let generics = resolver.tcx.hir().get_generics(def_id.to_def_id()).unwrap();

        let hir_id = tcx.hir().local_def_id_to_hir_id(def_id);
        let hir_fn_sig = tcx.hir().fn_sig_by_hir_id(hir_id).unwrap();

        // The rest of the analysis depends on a valid matching and generics being correctly resolved so we bail out if
        // there's an error.
        let matching = Matcher::match_fn_sigs(&mut resolver.diagnostics, &fn_sig, hir_fn_sig)?;

        let params = resolver.resolve_generics(fn_sig.generics, generics, &name_gen, &mut subst)?;

        // From here on each step is independent so we check for errors at the end.

        let requires = fn_sig
            .requires
            .into_iter()
            .map(|(region, ty)| {
                let fresh = name_gen.fresh();
                subst.insert_region(region.name, fresh);
                let ty = resolver.resolve_ty(ty, matching.requires[&region.name], &mut subst)?;
                Ok((fresh, ty))
            })
            .try_collect_exhaust();

        let args = fn_sig
            .args
            .into_iter()
            .zip(matching.args)
            .map(|(ty, hir_ty)| resolver.resolve_ty(ty, hir_ty, &mut subst))
            .try_collect_exhaust();

        let ensures = fn_sig
            .ensures
            .into_iter()
            .map(|(region, ty)| {
                let name = if let Some(name) = subst.get_region(region.name) {
                    name
                } else {
                    let fresh = name_gen.fresh();
                    subst.insert_region(region.name, fresh);
                    fresh
                };
                let ty = resolver.resolve_ty(ty, matching.ensures[&region.name], &mut subst)?;
                Ok((name, ty))
            })
            .try_collect_exhaust();

        let ret = resolver.resolve_ty(fn_sig.ret, matching.ret, &mut subst);

        Ok(ty::FnSig {
            params,
            requires: requires?,
            args: args?,
            ret: ret?,
            ensures: ensures?,
        })
    }

    fn resolve_generics(
        &mut self,
        generics: ast::Generics,
        hir_generics: &hir::Generics,
        name_gen: &IndexGen<Name>,
        subst: &mut Subst,
    ) -> Result<Vec<ty::Param>, ErrorReported> {
        let mut hir_ty_params = vec![];
        for param in hir_generics.params {
            if !param.bounds.is_empty() {
                self.diagnostics.emit_unsupported_signature(
                    param.span,
                    "generic bounds are not supported yet".to_string(),
                );
            }
            match param.kind {
                hir::GenericParamKind::Type { default: None, .. } => {
                    hir_ty_params.push((param.hir_id, param.name.ident()));
                }
                hir::GenericParamKind::Type {
                    default: Some(_), ..
                } => {
                    self.diagnostics.emit_unsupported_signature(
                        param.span,
                        "default type parameters are not supported yet".to_string(),
                    );
                }
                hir::GenericParamKind::Lifetime { .. } => {
                    self.diagnostics.emit_unsupported_signature(
                        param.span,
                        "lifetime parameters are not supported yet".to_string(),
                    );
                }
                hir::GenericParamKind::Const { .. } => {
                    self.diagnostics.emit_unsupported_signature(
                        param.span,
                        "const parameters are not supported yet".to_string(),
                    );
                }
            }
        }
        self.diagnostics.raise_if_errors()?;

        let (pure_params, ty_params): (Vec<_>, Vec<_>) =
            generics
                .params
                .into_iter()
                .partition_map(|param| match param {
                    ast::GenericParam::Pure { name, sort, pred } => {
                        Either::Left((name, sort, pred))
                    }
                    ast::GenericParam::Type(param) => Either::Right(param),
                });

        if ty_params.len() != hir_ty_params.len() {
            return self
                .diagnostics
                .emit_generic_count_mismatch(
                    generics.span,
                    ty_params.len(),
                    hir_generics.span,
                    hir_ty_params.len(),
                )
                .raise();
        }

        for (idx, (param, (hir_id, hir_param))) in
            ty_params.into_iter().zip(hir_ty_params).enumerate()
        {
            if param.name != hir_param.name {
                self.diagnostics
                    .emit_generic_name_mismatch(param, hir_param);
            } else {
                subst.insert_type(
                    self.tcx.hir().local_def_id(hir_id).to_def_id(),
                    ty::ParamTy {
                        index: idx as u32,
                        name: param.name,
                    },
                );
            }
        }
        self.diagnostics.raise_if_errors()?;

        let pure_params = pure_params
            .into_iter()
            .map(|(name, sort, pred)| self.resolve_pure_param(name, sort, pred, subst, name_gen))
            .try_collect_exhaust()?;

        Ok(pure_params)
    }

    fn resolve_pure_param(
        &mut self,
        name: ast::Ident,
        sort: ast::Ident,
        pred: Option<ast::Expr>,
        subst: &mut Subst,
        name_gen: &IndexGen<Name>,
    ) -> Result<ty::Param, ErrorReported> {
        let fresh = name_gen.fresh();
        if subst.insert_expr(name.name, ty::Var::Free(fresh)).is_some() {
            self.diagnostics
                .emit_duplicate_param_name(name.span)
                .raise()
        } else {
            let name = ty::Ident {
                name: fresh,
                source_info: (name.span, name.name),
            };
            let sort = self.resolve_sort(sort);
            let pred = match pred {
                Some(expr) => self.resolve_expr(expr, subst),
                None => Ok(ty::Expr::TRUE),
            };
            Ok(ty::Param {
                name,
                sort: sort?,
                pred: pred?,
            })
        }
    }

    fn resolve_ty(
        &mut self,
        ty: ast::Ty,
        hir_ty: &'tcx hir::Ty<'tcx>,
        subst: &mut Subst,
    ) -> Result<ty::Ty, ErrorReported> {
        match (ty.kind, &hir_ty.kind) {
            (ast::TyKind::BaseTy(path), hir::TyKind::Path(qpath)) => {
                match self.resolve_path(ty.span, path, qpath, subst)? {
                    ParamTyOrBaseTy::BaseTy(bty) => Ok(ty::Ty::Exists(bty, ty::Pred::TRUE)),
                    ParamTyOrBaseTy::ParamTy(param_ty) => Ok(ty::Ty::Param(param_ty)),
                }
            }
            (ast::TyKind::RefineTy { path, refine }, hir::TyKind::Path(qpath)) => {
                match self.resolve_path(ty.span, path, qpath, subst)? {
                    ParamTyOrBaseTy::BaseTy(bty) => {
                        let refine = self.resolve_expr(refine, subst);
                        Ok(ty::Ty::Refine(bty, refine?))
                    }
                    ParamTyOrBaseTy::ParamTy(_) => {
                        self.diagnostics.emit_refined_param_ty(ty.span).raise()
                    }
                }
            }
            (ast::TyKind::Exists { bind, path, pred }, hir::TyKind::Path(qpath)) => {
                match self.resolve_path(ty.span, path, qpath, subst)? {
                    ParamTyOrBaseTy::BaseTy(bty) => {
                        subst.push_expr_layer();
                        subst.insert_expr(bind.name, ty::Var::Bound);
                        let e = self.resolve_expr(pred, subst);
                        subst.pop_expr_layer();
                        Ok(ty::Ty::Exists(bty, ty::Pred::Expr(e?)))
                    }
                    ParamTyOrBaseTy::ParamTy(_) => {
                        self.diagnostics.emit_refined_param_ty(ty.span).raise()
                    }
                }
            }
            (ast::TyKind::MutRef(region), hir::TyKind::Rptr(_, mut_ty)) => {
                if !matches!(mut_ty.mutbl, hir::Mutability::Mut) {
                    return self
                        .diagnostics
                        .emit_unsupported_signature(
                            hir_ty.span,
                            "immutable references are not supported yet".to_string(),
                        )
                        .raise();
                }
                if let Some(name) = subst.get_region(region.name) {
                    Ok(ty::Ty::MutRef(name))
                } else {
                    self.diagnostics.emit_unknown_region(region).raise()
                }
            }
            _ => self
                .diagnostics
                .emit_invalid_refinement(ty.span, hir_ty.span)
                .raise(),
        }
    }

    fn resolve_path(
        &mut self,
        ty_span: Span,
        path: ast::Path,
        qpath: &'tcx hir::QPath<'tcx>,
        subst: &mut Subst,
    ) -> Result<ParamTyOrBaseTy, ErrorReported> {
        let hir_path = if let hir::QPath::Resolved(None, path) = qpath {
            path
        } else {
            return self
                .diagnostics
                .emit_unsupported_signature(qpath.span(), "unsupported type".to_string())
                .raise();
        };

        let (args, hir_args): (Vec<ast::Ty>, &[hir::GenericArg]) = match hir_path.segments {
            [hir::PathSegment {
                ident: segment_ident,
                args: hir_args,
                ..
            }] => {
                if path.ident.name != segment_ident.name {
                    return self
                        .diagnostics
                        .emit_invalid_refinement(ty_span, qpath.span())
                        .raise();
                }
                match (path.args, hir_args) {
                    (Some(args), Some(hir_args)) => {
                        if args.len() != hir_args.args.len() {
                            return self
                                .diagnostics
                                .emit_invalid_refinement(ty_span, qpath.span())
                                .raise();
                        }
                        if !hir_args.bindings.is_empty() {
                            return self
                                .diagnostics
                                .emit_unsupported_signature(
                                    hir_args.span_ext,
                                    "bindings for associated types are not supported yet"
                                        .to_string(),
                                )
                                .raise();
                        }
                        (args, hir_args.args)
                    }
                    (None, None) => (vec![], &[]),
                    _ => {
                        return self
                            .diagnostics
                            .emit_invalid_refinement(ty_span, qpath.span())
                            .raise();
                    }
                }
            }
            _ => {
                return self
                    .diagnostics
                    .emit_unsupported_signature(
                        qpath.span(),
                        "multi-segment paths are not supported yet".to_string(),
                    )
                    .raise();
            }
        };

        let hir_args: Vec<&'tcx hir::Ty<'tcx>> = hir_args
            .iter()
            .map(|arg| {
                if let hir::GenericArg::Type(ty) = arg {
                    Ok(ty)
                } else {
                    self.diagnostics
                        .emit_unsupported_signature(
                            arg.span(),
                            "associated types are not supported yet".to_string(),
                        )
                        .raise()
                }
            })
            .try_collect_exhaust()?;

        match hir_path.res {
            hir::def::Res::Def(hir::def::DefKind::TyParam, did) => {
                Ok(ParamTyOrBaseTy::ParamTy(subst.get_param_ty(did).unwrap()))
            }
            hir::def::Res::Def(hir::def::DefKind::Struct, did) => {
                let args = args
                    .into_iter()
                    .zip(hir_args)
                    .map(|(arg, hir_arg)| self.resolve_ty(arg, hir_arg, subst))
                    .try_collect()?;
                Ok(ParamTyOrBaseTy::BaseTy(ty::BaseTy::Adt(did, args)))
            }
            hir::def::Res::Def(_, _) => self
                .diagnostics
                .emit_unsupported_signature(qpath.span(), "unsupported type".to_string())
                .raise(),
            hir::def::Res::PrimTy(hir::PrimTy::Int(int_ty)) => Ok(ParamTyOrBaseTy::BaseTy(
                ty::BaseTy::Int(rustc_middle::ty::int_ty(int_ty)),
            )),
            hir::def::Res::PrimTy(hir::PrimTy::Uint(uint_ty)) => Ok(ParamTyOrBaseTy::BaseTy(
                ty::BaseTy::Uint(rustc_middle::ty::uint_ty(uint_ty)),
            )),
            hir::def::Res::PrimTy(hir::PrimTy::Bool) => {
                Ok(ParamTyOrBaseTy::BaseTy(ty::BaseTy::Bool))
            }
            hir::def::Res::PrimTy(hir::PrimTy::Float(_)) => self
                .diagnostics
                .emit_unsupported_signature(
                    qpath.span(),
                    "floats are not supported yet".to_string(),
                )
                .raise(),
            hir::def::Res::PrimTy(hir::PrimTy::Str) => self
                .diagnostics
                .emit_unsupported_signature(
                    qpath.span(),
                    "string slices are not supported yet".to_string(),
                )
                .raise(),
            hir::def::Res::PrimTy(hir::PrimTy::Char) => self
                .diagnostics
                .emit_unsupported_signature(qpath.span(), "chars are not suported yet".to_string())
                .raise(),
            hir::def::Res::SelfTy { .. } => self
                .diagnostics
                .emit_unsupported_signature(
                    qpath.span(),
                    "self types are not supported yet".to_string(),
                )
                .raise(),
            _ => unreachable!("unexpected type resolution"),
        }
    }

    fn resolve_expr(&self, expr: ast::Expr, subst: &Subst) -> Result<ty::Expr, ErrorReported> {
        let kind = match expr.kind {
            ast::ExprKind::Var(ident) => {
                ty::ExprKind::Var(self.resolve_var(ident, subst)?, ident.name, ident.span)
            }
            ast::ExprKind::Literal(lit) => ty::ExprKind::Literal(self.resolve_lit(lit)?),
            ast::ExprKind::BinaryOp(op, e1, e2) => {
                let e1 = self.resolve_expr(*e1, subst);
                let e2 = self.resolve_expr(*e2, subst);
                ty::ExprKind::BinaryOp(op, Box::new(e1?), Box::new(e2?))
            }
        };
        Ok(ty::Expr {
            kind,
            span: Some(expr.span),
        })
    }

    fn resolve_var(&self, ident: ast::Ident, subst: &Subst) -> Result<ty::Var, ErrorReported> {
        match subst.get_expr(ident.name) {
            Some(var) => Ok(var),
            None => self.emit_error(
                &format!("cannot find value `{}` in this scope", ident.name),
                ident.span,
            ),
        }
    }

    fn resolve_lit(&self, lit: ast::Lit) -> Result<ty::Lit, ErrorReported> {
        match lit.kind {
            ast::LitKind::Integer => match lit.symbol.as_str().parse::<i128>() {
                Ok(n) => Ok(ty::Lit::Int(n)),
                Err(_) => self.emit_error("integer literal is too large", lit.span),
            },
            ast::LitKind::Bool => Ok(ty::Lit::Bool(lit.symbol == kw::True)),
            _ => {
                self.tcx.sess.span_err(lit.span, "unexpected literal");
                Err(ErrorReported)
            }
        }
    }

    fn resolve_sort(&self, sort: ast::Ident) -> Result<ty::Sort, ErrorReported> {
        if sort.name == self.symbols.int {
            Ok(ty::Sort::Int)
        } else if sort.name == sym::bool {
            Ok(ty::Sort::Bool)
        } else {
            self.emit_error(
                &format!("cannot find sort `{}` in this scope", sort.name),
                sort.span,
            )
        }
    }

    fn emit_error<T>(&self, message: &str, span: Span) -> Result<T, ErrorReported> {
        self.tcx.sess.span_err(span, message);
        Err(ErrorReported)
    }
}

impl Symbols {
    fn new() -> Self {
        Self {
            int: Symbol::intern("int"),
        }
    }
}

impl Subst {
    fn new() -> Self {
        Self {
            exprs: ScopeMap::new(),
            regions: FxHashMap::default(),
            types: FxHashMap::default(),
        }
    }

    fn push_expr_layer(&mut self) {
        self.exprs.push_layer();
    }

    fn pop_expr_layer(&mut self) {
        self.exprs.pop_layer();
    }

    fn insert_expr(&mut self, symb: Symbol, name: ty::Var) -> Option<ty::Var> {
        let old = if self.exprs.contains_key_at_top(&symb) {
            self.exprs.get(&symb).copied()
        } else {
            None
        };
        self.exprs.define(symb, name);
        old
    }

    fn insert_region(&mut self, symb: Symbol, name: Name) -> Option<Name> {
        self.regions.insert(symb, name)
    }

    fn insert_type(&mut self, did: DefId, param_ty: ParamTy) -> Option<ParamTy> {
        self.types.insert(did, param_ty)
    }

    fn get_expr(&self, symb: Symbol) -> Option<ty::Var> {
        self.exprs.get(&symb).copied()
    }

    fn get_region(&self, symb: Symbol) -> Option<Name> {
        self.regions.get(&symb).copied()
    }

    fn get_param_ty(&self, did: DefId) -> Option<ParamTy> {
        self.types.get(&did).copied()
    }
}

impl Diagnostics<'_> {
    fn new(sess: &Session) -> Diagnostics {
        Diagnostics { sess, errors: 0 }
    }

    fn raise<T>(&mut self) -> Result<T, ErrorReported> {
        assert!(self.errors > 0);
        self.errors = 0;
        Err(ErrorReported)
    }

    fn raise_if_errors(&mut self) -> Result<(), ErrorReported> {
        if self.errors > 0 {
            self.errors = 0;
            Err(ErrorReported)
        } else {
            Ok(())
        }
    }

    fn emit_multiple_matches(&mut self, ty: &ast::Ty, matches: &[&hir::Ty]) -> &mut Self {
        self.errors += 1;
        let mut s = MultiSpan::from_span(ty.span);
        s.push_span_label(
            ty.span,
            "type may correspond to more than one type in the function signature".to_string(),
        );
        for hir_ty in matches {
            s.push_span_label(hir_ty.span, "".to_string());
        }
        self.sess.span_err(s, "ambiguous type refinement");
        self
    }

    fn emit_invalid_refinement(&mut self, refined: Span, hir: Span) -> &mut Self {
        let mut s = MultiSpan::from_span(refined);
        s.push_span_label(
            refined,
            "type is not a valid refinement of the corresponding matched type in the function declaration".to_string(),
        );
        s.push_span_label(hir, "matched type".to_string());
        self.sess.span_err(s, "invalid refinement");
        self.errors += 1;
        self
    }

    fn emit_unsupported_signature(&mut self, span: Span, msg: String) -> &mut Self {
        let mut s = MultiSpan::from_span(span);
        s.push_span_label(span, msg);
        self.sess.span_err(s, "unsupported function signature");
        self.errors += 1;
        self
    }

    fn emit_generic_name_mismatch(
        &mut self,
        refined: ast::Ident,
        hir: rustc_span::symbol::Ident,
    ) -> &mut Self {
        let mut s = MultiSpan::from_span(refined.span);
        s.push_span_label(
            refined.span,
            format!("refined signature declares parameter `{}`", refined.name),
        );
        s.push_span_label(
            hir.span,
            format!("function declares parameter `{}`", hir.name),
        );
        self.sess.span_err(s, "type parameter name mismatch");
        self.errors += 1;
        self
    }

    fn emit_generic_count_mismatch(
        &mut self,
        generics_span: Span,
        found: usize,
        hir_generics_span: Span,
        expected: usize,
    ) -> &mut Self {
        let mut s = MultiSpan::from_span(generics_span);
        s.push_span_label(
            generics_span,
            format!("refined signature has {} type parameters", found),
        );
        s.push_span_label(
            hir_generics_span,
            format!("function declared here with {} type parameters", expected),
        );
        self.sess.span_err(s, "generic count mismatch");
        self.errors += 1;
        self
    }

    fn emit_unresolved_region_type(&mut self, ty: &ast::Ty) {
        let mut s = MultiSpan::from_span(ty.span);
        s.push_span_label(
            ty.span,
            "type cannot be matched to any type in the function signature".to_string(),
        );
        self.sess.span_err(s, "unresolved type");
        self.errors += 1;
    }

    fn emit_refined_param_ty(&mut self, ty_span: Span) -> &mut Self {
        self.sess
            .span_err(ty_span, "type parameters cannot be refined");
        self.errors += 1;
        self
    }

    fn emit_args_count_mismatch(
        &mut self,
        fn_sig: &ast::FnSig,
        hir_fn_sig: &hir::FnSig,
    ) -> &mut Self {
        let mut s = MultiSpan::from_span(fn_sig.span);
        s.push_span_label(
            fn_sig.span,
            format!("refined signatured has {} arguments", fn_sig.args.len()),
        );
        s.push_span_label(
            hir_fn_sig.span,
            format!(
                "function declared here with {} arguments",
                hir_fn_sig.decl.inputs.len()
            ),
        );
        self.sess.span_err(s, "argument count mismatch");
        self.errors += 1;
        self
    }

    fn emit_unknown_region(&mut self, region: ast::Ident) -> &mut Self {
        self.sess.span_err(
            region.span,
            &format!(
                "cannot find region parameter `{}` in this scope",
                region.name
            ),
        );
        self.errors += 1;
        self
    }

    fn emit_duplicate_param_name(&mut self, span: Span) -> &mut Self {
        self.sess.span_err(span, "duplicate parameter name");
        self.errors += 1;
        self
    }
}

impl Drop for Diagnostics<'_> {
    fn drop(&mut self) {
        assert!(self.errors == 0);
    }
}

impl Matcher<'_> {
    fn match_fn_sigs<'tcx>(
        diagnostics: &mut Diagnostics,
        fn_sig: &ast::FnSig,
        hir_fn_sig: &hir::FnSig<'tcx>,
    ) -> Result<Matching<'tcx>, ErrorReported> {
        if fn_sig.args.len() != hir_fn_sig.decl.inputs.len() {
            return diagnostics
                .emit_args_count_mismatch(fn_sig, hir_fn_sig)
                .raise();
        }

        let mut requires = FxHashMap::default();
        let mut args = vec![];
        let matcher = Matcher::new(&fn_sig.requires);
        for (ty, hir_ty) in fn_sig.args.iter().zip(hir_fn_sig.decl.inputs) {
            args.push(hir_ty);
            matcher.match_refs_rec(ty, hir_ty, &mut requires);
        }

        let matcher = Matcher::new(&fn_sig.ensures);
        let mut ensures = FxHashMap::default();
        let ret = match hir_fn_sig.decl.output {
            hir::FnRetTy::DefaultReturn(_) => {
                return diagnostics
                    .emit_unsupported_signature(
                        fn_sig.span,
                        "default return types are not supported yet".to_string(),
                    )
                    .raise();
            }
            hir::FnRetTy::Return(hir_ty) => {
                matcher.match_refs_rec(&fn_sig.ret, hir_ty, &mut ensures);
                hir_ty
            }
        };
        for (region, _) in &fn_sig.ensures {
            if let Some(matches) = requires.get(&region.name) {
                ensures
                    .entry(region.name)
                    .or_default()
                    .extend(matches.iter().copied());
                // for hir_ty in matches {
                //     matcher.match_refs_rec(ty, hir_ty, &mut ensures);
                // }
            }
        }

        let requires = check_matches(diagnostics, &fn_sig.requires, requires);
        let ensures = check_matches(diagnostics, &fn_sig.ensures, ensures);

        Ok(Matching {
            requires: requires?,
            args,
            ret,
            ensures: ensures?,
        })
    }

    fn new(regions: &[(ast::Ident, ast::Ty)]) -> Matcher {
        Matcher {
            regions: regions
                .iter()
                .map(|(ident, ty)| (ident.name, ty.clone()))
                .collect(),
        }
    }

    fn match_refs_rec<'tcx>(
        &self,
        ty: &ast::Ty,
        hir_ty: &'tcx hir::Ty<'tcx>,
        matches: &mut FxHashMap<Symbol, Vec<&'tcx hir::Ty<'tcx>>>,
    ) {
        match (&ty.kind, &hir_ty.kind) {
            (ast::TyKind::MutRef(region), hir::TyKind::Rptr(_, mut_ty)) => {
                if let Some(ty) = self.regions.get(&region.name) {
                    matches.entry(region.name).or_default().push(mut_ty.ty);
                    self.match_refs_rec(ty, mut_ty.ty, matches);
                }
            }
            _ => {}
        }
    }
}

fn check_matches<'tcx>(
    diagnostics: &mut Diagnostics,
    regions: &[(ast::Ident, ast::Ty)],
    matches: FxHashMap<Symbol, Vec<&'tcx hir::Ty<'tcx>>>,
) -> Result<FxHashMap<Symbol, &'tcx hir::Ty<'tcx>>, ErrorReported> {
    let mut finalized_matches = FxHashMap::default();
    for (region, ty) in regions {
        match matches.get(&region.name) {
            Some(matches) if matches.len() == 1 => {
                finalized_matches.insert(region.name, matches[0]);
            }
            Some(matches) if matches.is_empty() => {
                diagnostics.emit_unresolved_region_type(ty);
            }
            Some(matches) => {
                diagnostics.emit_multiple_matches(ty, matches);
            }
            None => {
                diagnostics.emit_unresolved_region_type(ty);
            }
        }
    }
    diagnostics.raise_if_errors()?;

    Ok(finalized_matches)
}
