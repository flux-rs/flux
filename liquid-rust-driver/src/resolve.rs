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
    resolutions: FxHashMap<Symbol, hir::def::Res>,
    def_id: LocalDefId,
}

struct Symbols {
    int: Symbol,
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
    pub fn new(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> Result<Self, ErrorReported> {
        let hir_id = tcx.hir().local_def_id_to_hir_id(def_id);
        let fn_sig = tcx.hir().fn_sig_by_hir_id(hir_id).unwrap();

        let mut diagnostics = Diagnostics::new(tcx.sess);
        let resolutions = collect_res(&mut diagnostics, fn_sig)?;
        Ok(Self {
            tcx,
            diagnostics,
            symbols: Symbols::new(),
            resolutions,
            def_id,
        })
    }

    pub fn resolve(&mut self, fn_sig: ast::FnSig) -> Result<ty::FnSig, ErrorReported> {
        let mut subst = Subst::new();
        let name_gen = IndexGen::new();

        let hir_generics = self
            .tcx
            .hir()
            .get_generics(self.def_id.to_def_id())
            .unwrap();

        // The rest of the analysis depends on generics being correctly resolved so we bail out if
        // there's an error.

        let params = self.resolve_generics(fn_sig.generics, hir_generics, &name_gen, &mut subst)?;

        // From here on each step is independent so we check for errors at the end.

        let requires = fn_sig
            .requires
            .into_iter()
            .map(|(region, ty)| {
                let fresh = name_gen.fresh();
                subst.insert_region(region.name, fresh);
                let ty = self.resolve_ty(ty, &mut subst)?;
                Ok((fresh, ty))
            })
            .try_collect_exhaust();

        let args = fn_sig
            .args
            .into_iter()
            .map(|ty| self.resolve_ty(ty, &mut subst))
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
                let ty = self.resolve_ty(ty, &mut subst)?;
                Ok((name, ty))
            })
            .try_collect_exhaust();

        let ret = self.resolve_ty(fn_sig.ret, &mut subst);

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

    fn resolve_ty(&mut self, ty: ast::Ty, subst: &mut Subst) -> Result<ty::Ty, ErrorReported> {
        match ty.kind {
            ast::TyKind::BaseTy(path) => match self.resolve_path(path, subst)? {
                ParamTyOrBaseTy::BaseTy(bty) => Ok(ty::Ty::Exists(bty, ty::Pred::TRUE)),
                ParamTyOrBaseTy::ParamTy(param_ty) => Ok(ty::Ty::Param(param_ty)),
            },
            ast::TyKind::RefineTy { path, refine } => match self.resolve_path(path, subst)? {
                ParamTyOrBaseTy::BaseTy(bty) => {
                    let refine = self.resolve_expr(refine, subst);
                    Ok(ty::Ty::Refine(bty, refine?))
                }
                ParamTyOrBaseTy::ParamTy(_) => {
                    self.diagnostics.emit_refined_param_ty(ty.span).raise()
                }
            },
            ast::TyKind::Exists { bind, path, pred } => match self.resolve_path(path, subst)? {
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
            },
            ast::TyKind::MutRef(region) => {
                if let Some(name) = subst.get_region(region.name) {
                    Ok(ty::Ty::MutRef(name))
                } else {
                    self.diagnostics.emit_unknown_region(region).raise()
                }
            }
        }
    }

    fn resolve_path(
        &mut self,
        path: ast::Path,
        subst: &mut Subst,
    ) -> Result<ParamTyOrBaseTy, ErrorReported> {
        let res = if let Some(res) = self.resolutions.get(&path.ident.name) {
            *res
        } else {
            return self.diagnostics.emit_unresolved_path(&path).raise();
        };

        match res {
            hir::def::Res::Def(hir::def::DefKind::TyParam, did) => {
                Ok(ParamTyOrBaseTy::ParamTy(subst.get_param_ty(did).unwrap()))
            }
            hir::def::Res::Def(hir::def::DefKind::Struct, did) => {
                let args = path
                    .args
                    .into_iter()
                    .flatten()
                    .map(|ty| self.resolve_ty(ty, subst))
                    .try_collect_exhaust()?;
                Ok(ParamTyOrBaseTy::BaseTy(ty::BaseTy::Adt(did, args)))
            }
            hir::def::Res::Def(_, _) => self
                .diagnostics
                .emit_unsupported_signature(path.span, "unsupported type".to_string())
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
                .emit_unsupported_signature(path.span, "floats are not supported yet".to_string())
                .raise(),
            hir::def::Res::PrimTy(hir::PrimTy::Str) => self
                .diagnostics
                .emit_unsupported_signature(
                    path.span,
                    "string slices are not supported yet".to_string(),
                )
                .raise(),
            hir::def::Res::PrimTy(hir::PrimTy::Char) => self
                .diagnostics
                .emit_unsupported_signature(path.span, "chars are not suported yet".to_string())
                .raise(),
            hir::def::Res::SelfTy { .. } => self
                .diagnostics
                .emit_unsupported_signature(
                    path.span,
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

    fn emit_unresolved_path(&mut self, path: &ast::Path) -> &mut Self {
        let mut s = MultiSpan::from_span(path.span);
        s.push_span_label(
            path.span,
            format!("could not resolve `{}`", path.ident.name),
        );
        self.emit_span_err(s, &format!("failed to resolve `{}`", path.ident.name))
    }

    fn emit_unsupported_signature(&mut self, span: Span, msg: String) -> &mut Self {
        let mut s = MultiSpan::from_span(span);
        s.push_span_label(span, msg);
        self.emit_span_err(s, "unsupported function signature")
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
        self.emit_span_err(s, "type parameter name mismatch")
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
        self.emit_span_err(s, "generic count mismatch")
    }

    fn emit_refined_param_ty(&mut self, ty_span: Span) -> &mut Self {
        self.emit_span_err(ty_span, "type parameters cannot be refined")
    }

    fn emit_unknown_region(&mut self, region: ast::Ident) -> &mut Self {
        self.emit_span_err(
            region.span,
            &format!(
                "cannot find region parameter `{}` in this scope",
                region.name
            ),
        )
    }

    fn emit_duplicate_param_name(&mut self, span: Span) -> &mut Self {
        self.emit_span_err(span, "duplicate parameter name")
    }

    fn emit_span_err(&mut self, span: impl Into<MultiSpan>, msg: &str) -> &mut Self {
        self.sess.span_err(span, msg);
        self.errors += 1;
        self
    }
}

impl Drop for Diagnostics<'_> {
    fn drop(&mut self) {
        assert!(self.errors == 0);
    }
}

fn collect_res(
    diagnostics: &mut Diagnostics,
    fn_sig: &hir::FnSig,
) -> Result<FxHashMap<Symbol, hir::def::Res>, ErrorReported> {
    let mut resolutions = FxHashMap::default();

    fn_sig
        .decl
        .inputs
        .iter()
        .try_for_each_exhaust(|ty| collect_res_ty(diagnostics, ty, &mut resolutions))?;

    match fn_sig.decl.output {
        hir::FnRetTy::DefaultReturn(span) => {
            return diagnostics
                .emit_unsupported_signature(
                    span,
                    "default return types are not supported yet".to_string(),
                )
                .raise();
        }
        hir::FnRetTy::Return(ty) => {
            collect_res_ty(diagnostics, ty, &mut resolutions)?;
        }
    }

    Ok(resolutions)
}

fn collect_res_ty(
    diagnostics: &mut Diagnostics,
    ty: &hir::Ty,
    resolutions: &mut FxHashMap<Symbol, hir::def::Res>,
) -> Result<(), ErrorReported> {
    match &ty.kind {
        hir::TyKind::Slice(ty) | hir::TyKind::Array(ty, _) => {
            collect_res_ty(diagnostics, ty, resolutions)
        }
        hir::TyKind::Ptr(mut_ty) | hir::TyKind::Rptr(_, mut_ty) => {
            collect_res_ty(diagnostics, mut_ty.ty, resolutions)
        }
        hir::TyKind::Tup(tys) => tys
            .iter()
            .try_for_each(|ty| collect_res_ty(diagnostics, ty, resolutions)),
        hir::TyKind::Path(qpath) => {
            let path = if let hir::QPath::Resolved(None, path) = qpath {
                path
            } else {
                return diagnostics
                    .emit_unsupported_signature(qpath.span(), "unsupported type".to_string())
                    .raise();
            };

            let (ident, args) = match path.segments {
                [hir::PathSegment { ident, args, .. }] => (ident, args),
                _ => {
                    return diagnostics
                        .emit_unsupported_signature(
                            qpath.span(),
                            "multi-segment paths are not supported yet".to_string(),
                        )
                        .raise();
                }
            };
            resolutions.insert(ident.name, path.res);

            args.map(|args| args.args)
                .iter()
                .copied()
                .flatten()
                .try_for_each_exhaust(|arg| collect_res_generic_arg(diagnostics, arg, resolutions))
        }
        hir::TyKind::BareFn(_)
        | hir::TyKind::Never
        | hir::TyKind::OpaqueDef(_, _)
        | hir::TyKind::TraitObject(_, _, _)
        | hir::TyKind::Typeof(_)
        | hir::TyKind::Infer
        | hir::TyKind::Err => Ok(()),
    }
}

fn collect_res_generic_arg(
    diagnostics: &mut Diagnostics,
    arg: &hir::GenericArg,
    types: &mut FxHashMap<Symbol, hir::def::Res>,
) -> Result<(), ErrorReported> {
    match arg {
        hir::GenericArg::Type(ty) => collect_res_ty(diagnostics, ty, types),
        hir::GenericArg::Lifetime(_) => diagnostics
            .emit_unsupported_signature(arg.span(), "lifetimes are not supported yet".to_string())
            .raise(),
        hir::GenericArg::Const(_) => diagnostics
            .emit_unsupported_signature(
                arg.span(),
                "const generics are not supported yet".to_string(),
            )
            .raise(),
        hir::GenericArg::Infer(_) => unreachable!(),
    }
}
