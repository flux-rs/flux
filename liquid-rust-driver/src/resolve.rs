use hir::def_id::DefId;
use itertools::{Either, Itertools};
use liquid_rust_common::{errors::ErrorReported, index::IndexGen, iter::IterExt};
use liquid_rust_core::ty::{self, Name, ParamTy};
use liquid_rust_syntax::ast;
use quickscope::ScopeMap;
use rustc_hash::FxHashMap;
use rustc_hir::{self as hir, def_id::LocalDefId};
use rustc_middle::ty::TyCtxt;
use rustc_session::{Session, SessionDiagnostic};
use rustc_span::{sym, symbol::kw, Symbol};

pub struct Resolver<'tcx> {
    tcx: TyCtxt<'tcx>,
    diagnostics: Diagnostics<'tcx>,
    resolutions: FxHashMap<Symbol, hir::def::Res>,
    def_id: LocalDefId,
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
                self.diagnostics.emit_err(errors::UnsupportedSignature {
                    span: param.span,
                    msg: "generic bounds are not supported yet",
                });
            }
            match param.kind {
                hir::GenericParamKind::Type { default: None, .. } => {
                    hir_ty_params.push((param.hir_id, param.name.ident()));
                }
                hir::GenericParamKind::Type {
                    default: Some(_), ..
                } => {
                    self.diagnostics.emit_err(errors::UnsupportedSignature {
                        span: param.span,
                        msg: "default type parameters are not supported yet",
                    });
                }
                hir::GenericParamKind::Lifetime { .. } => {
                    self.diagnostics.emit_err(errors::UnsupportedSignature {
                        span: param.span,
                        msg: "lifetime parameters are not supported yet",
                    });
                }
                hir::GenericParamKind::Const { .. } => {
                    self.diagnostics.emit_err(errors::UnsupportedSignature {
                        span: param.span,
                        msg: "const parameters are not supported yet",
                    });
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
                .emit_err(errors::GenericCountMismatch::new(
                    generics.span,
                    ty_params.len(),
                    hir_generics.span,
                    hir_ty_params.len(),
                ))
                .raise();
        }

        for (idx, (param, (hir_id, hir_param))) in
            ty_params.into_iter().zip(hir_ty_params).enumerate()
        {
            if param.name != hir_param.name {
                self.diagnostics
                    .emit_err(errors::GenericNameMismatch::new(param, hir_param));
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
                .emit_err(errors::DuplicateGenericParam::new(name))
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
                ParamTyOrBaseTy::ParamTy(_) => self
                    .diagnostics
                    .emit_err(errors::RefinedTypeParam { span: ty.span })
                    .raise(),
            },
            ast::TyKind::Exists { bind, path, pred } => match self.resolve_path(path, subst)? {
                ParamTyOrBaseTy::BaseTy(bty) => {
                    subst.push_expr_layer();
                    subst.insert_expr(bind.name, ty::Var::Bound);
                    let e = self.resolve_expr(pred, subst);
                    subst.pop_expr_layer();
                    Ok(ty::Ty::Exists(bty, ty::Pred::Expr(e?)))
                }
                ParamTyOrBaseTy::ParamTy(_) => self
                    .diagnostics
                    .emit_err(errors::RefinedTypeParam { span: ty.span })
                    .raise(),
            },
            ast::TyKind::MutRef(region) => {
                if let Some(name) = subst.get_region(region.name) {
                    Ok(ty::Ty::MutRef(name))
                } else {
                    self.diagnostics
                        .emit_err(errors::UnresolvedLoc::new(region))
                        .raise()
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
            return self
                .diagnostics
                .emit_err(errors::UnresolvedPath::new(&path))
                .raise();
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
                .emit_err(errors::UnsupportedSignature {
                    span: path.span,
                    msg: "unsupported type",
                })
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
                .emit_err(errors::UnsupportedSignature {
                    span: path.span,
                    msg: "floats are not supported yet",
                })
                .raise(),
            hir::def::Res::PrimTy(hir::PrimTy::Str) => self
                .diagnostics
                .emit_err(errors::UnsupportedSignature {
                    span: path.span,
                    msg: "string slices are not supported yet",
                })
                .raise(),
            hir::def::Res::PrimTy(hir::PrimTy::Char) => self
                .diagnostics
                .emit_err(errors::UnsupportedSignature {
                    span: path.span,
                    msg: "chars are not suported yet",
                })
                .raise(),
            hir::def::Res::SelfTy { .. } => self
                .diagnostics
                .emit_err(errors::UnsupportedSignature {
                    span: path.span,
                    msg: "self types are not supported yet",
                })
                .raise(),
            _ => unreachable!("unexpected type resolution"),
        }
    }

    fn resolve_expr(&mut self, expr: ast::Expr, subst: &Subst) -> Result<ty::Expr, ErrorReported> {
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

    fn resolve_var(&mut self, var: ast::Ident, subst: &Subst) -> Result<ty::Var, ErrorReported> {
        match subst.get_expr(var.name) {
            Some(var) => Ok(var),
            None => self
                .diagnostics
                .emit_err(errors::UnresolvedVar::new(var))
                .raise(),
        }
    }

    fn resolve_lit(&mut self, lit: ast::Lit) -> Result<ty::Lit, ErrorReported> {
        match lit.kind {
            ast::LitKind::Integer => match lit.symbol.as_str().parse::<i128>() {
                Ok(n) => Ok(ty::Lit::Int(n)),
                Err(_) => self
                    .diagnostics
                    .emit_err(errors::IntTooLarge { span: lit.span })
                    .raise(),
            },
            ast::LitKind::Bool => Ok(ty::Lit::Bool(lit.symbol == kw::True)),
            _ => self
                .diagnostics
                .emit_err(errors::UnexpectedLiteral { span: lit.span })
                .raise(),
        }
    }

    fn resolve_sort(&mut self, sort: ast::Ident) -> Result<ty::Sort, ErrorReported> {
        if sort.name == SORTS.int {
            Ok(ty::Sort::Int)
        } else if sort.name == sym::bool {
            Ok(ty::Sort::Bool)
        } else {
            self.diagnostics
                .emit_err(errors::UnresolvedSort::new(sort))
                .raise()
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
        if self.exprs.contains_key_at_top(&symb) {
            self.exprs.get(&symb).copied()
        } else {
            self.exprs.define(symb, name);
            None
        }
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

    fn emit_err<'a>(&'a mut self, err: impl SessionDiagnostic<'a>) -> &mut Self {
        self.sess.emit_err(err);
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
                .emit_err(errors::UnsupportedSignature {
                    span,
                    msg: "default return types are not supported yet",
                })
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
                    .emit_err(errors::UnsupportedSignature {
                        span: qpath.span(),
                        msg: "unsupported type",
                    })
                    .raise();
            };

            let (ident, args) = match path.segments {
                [hir::PathSegment { ident, args, .. }] => (ident, args),
                _ => {
                    return diagnostics
                        .emit_err(errors::UnsupportedSignature {
                            span: qpath.span(),
                            msg: "multi-segment paths are not supported yet",
                        })
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
            .emit_err(errors::UnsupportedSignature {
                span: arg.span(),
                msg: "lifetime parameters are not supported yet",
            })
            .raise(),
        hir::GenericArg::Const(_) => diagnostics
            .emit_err(errors::UnsupportedSignature {
                span: arg.span(),
                msg: "const generics are not supported yet",
            })
            .raise(),

        hir::GenericArg::Infer(_) => unreachable!(),
    }
}

struct Sorts {
    int: Symbol,
}

static SORTS: std::lazy::SyncLazy<Sorts> = std::lazy::SyncLazy::new(|| Sorts {
    int: Symbol::intern("int"),
});

mod errors {
    use liquid_rust_syntax::ast;
    use rustc_errors::pluralize;
    use rustc_macros::SessionDiagnostic;
    use rustc_span::{symbol::Ident, Span};

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct UnsupportedSignature {
        #[message = "unsupported function signature"]
        #[label = "{msg}"]
        pub span: Span,
        pub msg: &'static str,
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct UnresolvedPath {
        #[message = "could not resolve `{path}`"]
        #[label = "failed to resolve `{path}`"]
        pub span: Span,
        pub path: Ident,
    }

    impl UnresolvedPath {
        pub fn new(path: &ast::Path) -> Self {
            Self {
                span: path.span,
                path: path.ident,
            }
        }
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct GenericNameMismatch {
        #[message = "type parameter name mismatch"]
        #[label = "refined signature declares parameter `{found_name}`"]
        pub found: Span,
        pub found_name: Ident,
        #[label = "function declares parameter `{expected_name}`"]
        pub expected: Span,
        pub expected_name: Ident,
    }

    impl GenericNameMismatch {
        pub fn new(found: Ident, expected: Ident) -> Self {
            Self {
                found: found.span,
                found_name: found,
                expected: expected.span,
                expected_name: expected,
            }
        }
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct GenericCountMismatch {
        #[message = "function declared with {expected} type parameters{expected_plural} but refined signature has {found}"]
        #[label = "refined signature has {found} type parameter{found_plural}"]
        pub found_span: Span,
        pub found: usize,
        pub found_plural: &'static str,
        #[label = "function declared here with {expected} type parameter{expected_plural}"]
        pub expected_span: Span,
        pub expected: usize,
        pub expected_plural: &'static str,
    }

    impl GenericCountMismatch {
        pub fn new(found_span: Span, found: usize, expected_span: Span, expected: usize) -> Self {
            Self {
                found_span,
                found,
                found_plural: pluralize!(found),
                expected_span,
                expected,
                expected_plural: pluralize!(expected),
            }
        }
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct UnresolvedLoc {
        #[message = "cannot find location parameter `{loc}` in this scope"]
        span: Span,
        loc: Ident,
    }

    impl UnresolvedLoc {
        pub fn new(loc: Ident) -> Self {
            Self {
                span: loc.span,
                loc,
            }
        }
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct DuplicateGenericParam {
        #[message = "the name `{name}` is already used for a generic parameter"]
        #[label = "already used"]
        span: Span,
        name: Ident,
    }

    impl DuplicateGenericParam {
        pub fn new(name: Ident) -> Self {
            Self {
                span: name.span,
                name,
            }
        }
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct RefinedTypeParam {
        #[message = "type parameters cannot be refined"]
        #[label = "refined type parameter"]
        pub span: Span,
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct UnresolvedSort {
        #[message = "cannot find sort `{sort}` in this scope"]
        #[label = "not found in this scope"]
        pub span: Span,
        pub sort: Ident,
    }

    impl UnresolvedSort {
        pub fn new(sort: Ident) -> Self {
            Self {
                span: sort.span,
                sort,
            }
        }
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct UnresolvedVar {
        #[message = "cannot find value `{var}` in this scope"]
        #[label = "not found in this scope"]
        pub span: Span,
        pub var: Ident,
    }

    impl UnresolvedVar {
        pub fn new(var: Ident) -> Self {
            Self {
                span: var.span,
                var,
            }
        }
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct IntTooLarge {
        #[message = "integer literal is too large"]
        pub span: Span,
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct UnexpectedLiteral {
        #[message = "unexpected literal"]
        pub span: Span,
    }
}
