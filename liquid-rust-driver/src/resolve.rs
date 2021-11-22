use itertools::{Either, Itertools};
use liquid_rust_common::{errors::ErrorReported, index::IndexGen, iter::IterExt};
use liquid_rust_core::ty::{self, Name, ParamTy};
use liquid_rust_syntax::ast;
use quickscope::ScopeMap;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty::TyCtxt;
use rustc_session::Session;
use rustc_span::{sym, symbol::kw, MultiSpan, Span, Symbol};

pub struct Resolver<'tcx> {
    tcx: TyCtxt<'tcx>,
    errors: ErrorEmitter<'tcx>,
    symbols: Symbols,
    requires: FxHashMap<Name, Res<'tcx>>,
}

struct Symbols {
    int: Symbol,
}

struct ErrorEmitter<'tcx> {
    sess: &'tcx Session,
}

struct Subst {
    exprs: ScopeMap<Symbol, ty::Var>,
    regions: FxHashMap<Symbol, Name>,
    types: FxHashMap<Symbol, ParamTy>,
}

enum Res<'tcx> {
    Unresolved(ast::Ty),
    Resolved(ty::Ty, &'tcx rustc_hir::Ty<'tcx>),
    Error,
}

impl<'tcx> Resolver<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            errors: ErrorEmitter::new(tcx.sess),
            symbols: Symbols::new(),
            requires: FxHashMap::default(),
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

        // The rest of the analysis depends on generics being correctly resolved so we bailed out if there's an error.
        let params = resolver.resolve_generics(fn_sig.generics, generics, &name_gen, &mut subst)?;

        for (region, ty) in fn_sig.requires {
            let fresh = name_gen.fresh();
            resolver.requires.insert(fresh, Res::Unresolved(ty));
            subst.insert_region(region.name, fresh);
        }

        let args = fn_sig
            .args
            .into_iter()
            .zip(hir_fn_sig.decl.inputs)
            .map(|(ty, hir_ty)| resolver.resolve_ty(ty, hir_ty, &mut subst))
            .try_collect_exhaust();

        let ret = match hir_fn_sig.decl.output {
            rustc_hir::FnRetTy::DefaultReturn(span) => resolver.errors.emit_unsupported_signature(
                span,
                "default returns are not supported yet".to_string(),
            ),
            rustc_hir::FnRetTy::Return(hir_ty) => {
                resolver.resolve_ty(fn_sig.ret, hir_ty, &mut subst)
            }
        };

        let ensures = resolver.resolve_ensures(fn_sig.ensures, &mut subst);

        let requires = resolver
            .requires
            .into_iter()
            .map(|(name, res)| match res {
                Res::Resolved(ty, _) => Ok((name, ty)),
                Res::Error => Err(ErrorReported),
                Res::Unresolved(ty) => resolver.errors.emit_unresolved_region_type(ty),
            })
            .try_collect_exhaust()?;

        Ok(ty::FnSig {
            params,
            requires,
            args: args?,
            ret: ret?,
            ensures: ensures?,
        })
    }

    fn resolve_ensures(
        &mut self,
        ensures: Vec<(ast::Ident, ast::Ty)>,
        subst: &mut Subst,
    ) -> Result<Vec<(Name, ty::Ty)>, ErrorReported> {
        ensures
            .into_iter()
            .map(|(region, ty)| {
                if let Some(name) = subst.get_region(region.name) {
                    let hir_ty = match self.requires.get(&name) {
                        Some(Res::Resolved(_, hir_ty)) => *hir_ty,
                        _ => return self.errors.emit_unresolved_region_type(ty),
                    };
                    let ty = self.resolve_ty(ty, hir_ty, subst)?;
                    Ok((name, ty))
                } else {
                    self.errors.emit_unresolved_region_type(ty)
                }
            })
            .try_collect_exhaust()
    }

    fn resolve_generics(
        &self,
        generics: ast::Generics,
        hir_generics: &rustc_hir::Generics,
        name_gen: &IndexGen<Name>,
        subst: &mut Subst,
    ) -> Result<Vec<ty::Param>, ErrorReported> {
        let mut hir_ty_params = vec![];
        for param in hir_generics.params {
            if !param.bounds.is_empty() {
                return self.errors.emit_unsupported_signature(
                    param.span,
                    "generic bounds are not supported yet".to_string(),
                );
            }
            match param.kind {
                rustc_hir::GenericParamKind::Type { default: None, .. } => {
                    hir_ty_params.push(param.name.ident());
                }
                rustc_hir::GenericParamKind::Type {
                    default: Some(_), ..
                } => {
                    return self.errors.emit_unsupported_signature(
                        param.span,
                        "default type parameters are not supported yet".to_string(),
                    );
                }
                rustc_hir::GenericParamKind::Lifetime { .. } => {
                    return self.errors.emit_unsupported_signature(
                        param.span,
                        "lifetime parameters are not supported yet".to_string(),
                    );
                }
                rustc_hir::GenericParamKind::Const { .. } => {
                    return self.errors.emit_unsupported_signature(
                        param.span,
                        "const parameters are not supported yet".to_string(),
                    );
                }
            }
        }

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
            return self.errors.emit_generic_count_mismatch(
                generics.span,
                ty_params.len(),
                hir_generics.span,
                hir_ty_params.len(),
            );
        }

        for (idx, (param, hir_param)) in ty_params.into_iter().zip(hir_ty_params).enumerate() {
            if param.name != hir_param.name {
                return self.errors.emit_generic_name_mismatch(param, hir_param);
            }
            subst.insert_type(
                param.name,
                ty::ParamTy {
                    index: idx as u32,
                    name: param.name,
                },
            );
        }

        let pure_params = pure_params
            .into_iter()
            .map(|(name, sort, pred)| self.resolve_pure_param(name, sort, pred, subst, name_gen))
            .try_collect_exhaust()?;

        Ok(pure_params)
    }

    fn resolve_pure_param(
        &self,
        name: ast::Ident,
        sort: ast::Ident,
        pred: Option<ast::Expr>,
        subst: &mut Subst,
        name_gen: &IndexGen<Name>,
    ) -> Result<ty::Param, ErrorReported> {
        let fresh = name_gen.fresh();
        if subst.insert_expr(name.name, ty::Var::Free(fresh)).is_some() {
            self.tcx
                .sess
                .span_err(name.span, "duplicate parameter name");
            Err(ErrorReported)
        } else {
            let name = ty::Ident {
                name: fresh,
                source_info: (name.span, name.name),
            };
            let sort = self.resolve_sort(sort);
            let pred = match pred {
                Some(expr) => self.resolve_expr(expr, &subst),
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
        hir_ty: &'tcx rustc_hir::Ty<'tcx>,
        subst: &mut Subst,
    ) -> Result<ty::Ty, ErrorReported> {
        match (ty.kind, &hir_ty.kind) {
            (ast::TyKind::BaseTy(bty), rustc_hir::TyKind::Path(qpath)) => {
                if let Some(param_ty) = subst.get_param_ty(bty.name) {
                    self.resolve_param_ty(ty.span, param_ty, bty, qpath)
                } else {
                    let bty = self.resolve_bty(ty.span, bty, qpath)?;
                    Ok(ty::Ty::Exists(bty, ty::Pred::TRUE))
                }
            }
            (ast::TyKind::RefineTy { bty, refine }, rustc_hir::TyKind::Path(qpath)) => {
                let bty = self.resolve_bty(ty.span, bty, qpath);
                let refine = self.resolve_expr(refine, subst);
                Ok(ty::Ty::Refine(bty?, refine?))
            }
            (ast::TyKind::Exists { bind, bty, pred }, rustc_hir::TyKind::Path(qpath)) => {
                let bty = self.resolve_bty(ty.span, bty, qpath);
                subst.push_expr_layer();
                subst.insert_expr(bind.name, ty::Var::Bound);
                let e = self.resolve_expr(pred, subst);
                subst.pop_expr_layer();
                Ok(ty::Ty::Exists(bty?, ty::Pred::Expr(e?)))
            }
            (ast::TyKind::MutRef(region), rustc_hir::TyKind::Rptr(_, mut_ty)) => {
                if !matches!(mut_ty.mutbl, rustc_hir::Mutability::Mut) {
                    return self.errors.emit_unsupported_signature(
                        hir_ty.span,
                        "immutable references are not supported yet".to_string(),
                    );
                }
                if let Some(name) = subst.get_region(region.name) {
                    self.resolve_region(name, &mut_ty.ty, subst);
                    Ok(ty::Ty::MutRef(name))
                } else {
                    return self.errors.emit_unknown_region(region);
                }
            }
            _ => self.errors.emit_invalid_refinement(ty.span, hir_ty.span),
        }
    }

    fn resolve_region(
        &mut self,
        region: Name,
        hir_ty: &'tcx rustc_hir::Ty<'tcx>,
        subst: &mut Subst,
    ) {
        match self.requires.remove(&region).unwrap() {
            Res::Unresolved(ty) => {
                if let Ok(ty) = self.resolve_ty(ty, hir_ty, subst) {
                    self.requires.insert(region, Res::Resolved(ty, hir_ty));
                } else {
                    self.requires.insert(region, Res::Error);
                }
            }
            res @ Res::Resolved(..) | res @ Res::Error => {
                self.requires.insert(region, res);
            }
        }
    }

    fn resolve_param_ty(
        &self,
        ty_span: Span,
        param_ty: ty::ParamTy,
        ident: ast::Ident,
        qpath: &rustc_hir::QPath,
    ) -> Result<ty::Ty, ErrorReported> {
        let path = if let rustc_hir::QPath::Resolved(None, path) = qpath {
            path
        } else {
            return self
                .errors
                .emit_unsupported_signature(qpath.span(), "unsupported type".to_string());
        };

        if matches!(path.segments, [segment] if segment.ident.name == ident.name) {
            Ok(ty::Ty::Param(param_ty))
        } else {
            self.errors.emit_invalid_refinement(ty_span, qpath.span())
        }
    }

    fn resolve_bty(
        &self,
        ty_span: Span,
        ident: ast::Ident,
        qpath: &rustc_hir::QPath,
    ) -> Result<ty::BaseTy, ErrorReported> {
        let path = if let rustc_hir::QPath::Resolved(None, path) = qpath {
            path
        } else {
            return self
                .errors
                .emit_unsupported_signature(qpath.span(), "unsupported type".to_string());
        };

        match path.segments {
            [rustc_hir::PathSegment {
                ident: segment_ident,
                args: None,
                ..
            }] => {
                if segment_ident.name != ident.name {
                    return self.errors.emit_invalid_refinement(ty_span, qpath.span());
                }
            }
            [rustc_hir::PathSegment { args: Some(_), .. }] => {
                todo!("implement paths with arguments");
            }
            _ => {
                return self.errors.emit_unsupported_signature(
                    qpath.span(),
                    "multi-segment paths are not supported yet".to_string(),
                )
            }
        }

        match path.res {
            rustc_hir::def::Res::Def(_, _) => todo!("implement structs"),
            rustc_hir::def::Res::PrimTy(rustc_hir::PrimTy::Int(int_ty)) => {
                Ok(ty::BaseTy::Int(rustc_middle::ty::int_ty(int_ty)))
            }
            rustc_hir::def::Res::PrimTy(rustc_hir::PrimTy::Bool) => Ok(ty::BaseTy::Bool),
            rustc_hir::def::Res::PrimTy(rustc_hir::PrimTy::Uint(_)) => {
                self.errors.emit_unsupported_signature(
                    qpath.span(),
                    "unsigned ints are not supported yet".to_string(),
                )
            }
            rustc_hir::def::Res::PrimTy(rustc_hir::PrimTy::Float(_)) => {
                self.errors.emit_unsupported_signature(
                    qpath.span(),
                    "floats are not supported yet".to_string(),
                )
            }
            rustc_hir::def::Res::PrimTy(rustc_hir::PrimTy::Str) => {
                self.errors.emit_unsupported_signature(
                    qpath.span(),
                    "string slices are not supported yet".to_string(),
                )
            }
            rustc_hir::def::Res::PrimTy(rustc_hir::PrimTy::Char) => self
                .errors
                .emit_unsupported_signature(qpath.span(), "chars are not suported yet".to_string()),
            rustc_hir::def::Res::SelfTy { .. } => self.errors.emit_unsupported_signature(
                qpath.span(),
                "self types are not supported yet".to_string(),
            ),
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

    fn insert_type(&mut self, symb: Symbol, param_ty: ParamTy) -> Option<ParamTy> {
        self.types.insert(symb, param_ty)
    }

    fn get_expr(&self, symb: Symbol) -> Option<ty::Var> {
        self.exprs.get(&symb).copied()
    }

    fn get_region(&self, symb: Symbol) -> Option<Name> {
        self.regions.get(&symb).copied()
    }

    fn get_param_ty(&self, symb: Symbol) -> Option<ParamTy> {
        self.types.get(&symb).copied()
    }
}

impl ErrorEmitter<'_> {
    fn new(sess: &Session) -> ErrorEmitter {
        ErrorEmitter { sess }
    }

    fn emit_invalid_refinement<T>(&self, refined: Span, hir: Span) -> Result<T, ErrorReported> {
        let mut s = MultiSpan::from_span(refined);
        s.push_span_label(
            refined,
            "type is not a valid refinement of the corresponding rust type".to_string(),
        );
        s.push_span_label(hir, "rust type".to_string());
        self.sess.span_err(s, "invalid refinement");
        Err(ErrorReported)
    }

    fn emit_unsupported_signature<T>(&self, span: Span, msg: String) -> Result<T, ErrorReported> {
        let mut s = MultiSpan::from_span(span);
        s.push_span_label(span, msg);
        self.sess
            .span_err(s, "refinement of unsupported function signature");
        Err(ErrorReported)
    }

    fn emit_generic_name_mismatch<T>(
        &self,
        refined: ast::Ident,
        hir: rustc_span::symbol::Ident,
    ) -> Result<T, ErrorReported> {
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
        Err(ErrorReported)
    }

    fn emit_generic_count_mismatch<T>(
        &self,
        generics_span: Span,
        found: usize,
        hir_generics_span: Span,
        expected: usize,
    ) -> Result<T, ErrorReported> {
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
        Err(ErrorReported)
    }

    fn emit_unresolved_region_type<T>(&self, ty: ast::Ty) -> Result<T, ErrorReported> {
        let mut s = MultiSpan::from_span(ty.span);
        s.push_span_label(
            ty.span,
            "type couldn't be matched to any rust type".to_string(),
        );
        self.sess.span_err(s, "unresolved type");
        Err(ErrorReported)
    }

    fn emit_unknown_region<T>(&self, region: ast::Ident) -> Result<T, ErrorReported> {
        self.sess.span_err(
            region.span,
            &format!(
                "cannot find region parameter `{}` in this scope",
                region.name
            ),
        );
        Err(ErrorReported)
    }
}
