use hir::{def_id::DefId, Impl, ItemId, ItemKind};
use liquid_rust_common::{errors::ErrorReported, index::IndexGen, iter::IterExt};
use liquid_rust_core::ty::{self, Name, ParamTy};
use liquid_rust_syntax::ast;
use quickscope::ScopeMap;
use rustc_hash::FxHashMap;
use rustc_hir::{self as hir, def_id::LocalDefId};
use rustc_middle::ty::TyCtxt;
use rustc_session::{Session, SessionDiagnostic};
use rustc_span::{sym, symbol::kw, Symbol};

type NameResTable = FxHashMap<Symbol, hir::def::Res>;

pub struct Resolver<'tcx> {
    tcx: TyCtxt<'tcx>,
    diagnostics: Diagnostics<'tcx>,
    name_res_table: NameResTable,
    def_id: LocalDefId,
    parent: Option<&'tcx Impl<'tcx>>,
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
    types: ScopeMap<DefId, ParamTy>,
}

impl<'tcx> Resolver<'tcx> {
    pub fn resolve(
        tcx: TyCtxt<'tcx>,
        def_id: LocalDefId,
        fn_sig: ast::FnSig,
    ) -> Result<ty::FnSig, ErrorReported> {
        let hir_id = tcx.hir().local_def_id_to_hir_id(def_id);
        let hir_fn_sig = tcx.hir().fn_sig_by_hir_id(hir_id).unwrap();

        let mut diagnostics = Diagnostics::new(tcx.sess);

        let mut name_res_table = FxHashMap::default();
        let mut parent = None;
        if let Some(impl_did) = tcx.impl_of_method(def_id.to_def_id()) {
            let item_id = ItemId { def_id: impl_did.expect_local() };
            let item = tcx.hir().item(item_id);
            if let ItemKind::Impl(impl_parent) = &item.kind {
                parent = Some(impl_parent);
                collect_res_ty(&mut diagnostics, impl_parent.self_ty, &mut name_res_table)?;
            }
        }
        collect_res(&mut diagnostics, hir_fn_sig, &mut name_res_table)?;

        let mut resolver = Self { tcx, diagnostics, parent, name_res_table, def_id };
        resolver.run(fn_sig)
    }

    fn run(&mut self, fn_sig: ast::FnSig) -> Result<ty::FnSig, ErrorReported> {
        let mut subst = Subst::new();

        let name_gen = IndexGen::new();

        if let Some(parent) = self.parent {
            self.insert_generic_types(&parent.generics, &mut subst);
            subst.push_type_layer();
        }

        let hir_generics = self.tcx.hir().get_generics(self.def_id).unwrap();

        self.insert_generic_types(hir_generics, &mut subst);

        let params = self.resolve_generics(fn_sig.generics, &name_gen, &mut subst);

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
            params: params?,
            requires: requires?,
            args: args?,
            ret: ret?,
            ensures: ensures?,
        })
    }

    fn insert_generic_types(&self, generics: &hir::Generics, subst: &mut Subst) {
        for param in generics.params.iter() {
            if let hir::GenericParamKind::Type { .. } = param.kind {
                let def_id = self.tcx.hir().local_def_id(param.hir_id).to_def_id();
                let name = param.name.ident().name;
                subst.insert_type(def_id, name);
            }
        }
    }

    fn resolve_generics(
        &mut self,
        generics: ast::Generics,
        name_gen: &IndexGen<Name>,
        subst: &mut Subst,
    ) -> Result<Vec<ty::Param>, ErrorReported> {
        generics
            .into_iter()
            .map(|param| {
                let fresh = name_gen.fresh();
                if subst
                    .insert_expr(param.name.name, ty::Var::Free(fresh))
                    .is_some()
                {
                    self.diagnostics
                        .emit_err(errors::DuplicateGenericParam::new(param.name))
                        .raise()
                } else {
                    let name =
                        ty::Ident { name: fresh, source_info: (param.name.span, param.name.name) };
                    let sort = self.resolve_sort(param.sort);
                    let pred = match param.pred {
                        Some(expr) => self.resolve_expr(expr, subst),
                        None => Ok(ty::Expr::TRUE),
                    };
                    Ok(ty::Param { name, sort: sort?, pred: pred? })
                }
            })
            .try_collect_exhaust()
    }

    fn resolve_ty(&mut self, ty: ast::Ty, subst: &mut Subst) -> Result<ty::Ty, ErrorReported> {
        match ty.kind {
            ast::TyKind::BaseTy(path) => {
                match self.resolve_path(path, subst)? {
                    ParamTyOrBaseTy::BaseTy(bty) => Ok(ty::Ty::Exists(bty, ty::Pred::TRUE)),
                    ParamTyOrBaseTy::ParamTy(param_ty) => Ok(ty::Ty::Param(param_ty)),
                }
            }
            ast::TyKind::RefineTy { path, refine } => {
                match self.resolve_path(path, subst)? {
                    ParamTyOrBaseTy::BaseTy(bty) => {
                        let refine = self.resolve_expr(refine, subst);
                        Ok(ty::Ty::Refine(bty, refine?))
                    }
                    ParamTyOrBaseTy::ParamTy(_) => {
                        self.diagnostics
                            .emit_err(errors::RefinedTypeParam { span: ty.span })
                            .raise()
                    }
                }
            }
            ast::TyKind::Exists { bind, path, pred } => {
                match self.resolve_path(path, subst)? {
                    ParamTyOrBaseTy::BaseTy(bty) => {
                        subst.push_expr_layer();
                        subst.insert_expr(bind.name, ty::Var::Bound);
                        let e = self.resolve_expr(pred, subst);
                        subst.pop_expr_layer();
                        Ok(ty::Ty::Exists(bty, ty::Pred::Expr(e?)))
                    }
                    ParamTyOrBaseTy::ParamTy(_) => {
                        self.diagnostics
                            .emit_err(errors::RefinedTypeParam { span: ty.span })
                            .raise()
                    }
                }
            }
            ast::TyKind::StrgRef(region) => {
                if let Some(name) = subst.get_region(region.name) {
                    Ok(ty::Ty::StrgRef(name))
                } else {
                    self.diagnostics
                        .emit_err(errors::UnresolvedLoc::new(region))
                        .raise()
                }
            }
            ast::TyKind::WeakRef(ty) => {
                let ty = self.resolve_ty(*ty, subst)?;
                Ok(ty::Ty::WeakRef(Box::new(ty)))
            }
            ast::TyKind::ShrRef(ty) => {
                let ty = self.resolve_ty(*ty, subst)?;
                Ok(ty::Ty::ShrRef(Box::new(ty)))
            }
        }
    }

    fn resolve_path(
        &mut self,
        path: ast::Path,
        subst: &mut Subst,
    ) -> Result<ParamTyOrBaseTy, ErrorReported> {
        let res = if let Some(res) = self.name_res_table.get(&path.ident.name) {
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
            hir::def::Res::PrimTy(hir::PrimTy::Int(int_ty)) => {
                Ok(ParamTyOrBaseTy::BaseTy(ty::BaseTy::Int(rustc_middle::ty::int_ty(int_ty))))
            }
            hir::def::Res::PrimTy(hir::PrimTy::Uint(uint_ty)) => {
                Ok(ParamTyOrBaseTy::BaseTy(ty::BaseTy::Uint(rustc_middle::ty::uint_ty(uint_ty))))
            }
            hir::def::Res::PrimTy(hir::PrimTy::Bool) => {
                Ok(ParamTyOrBaseTy::BaseTy(ty::BaseTy::Bool))
            }
            hir::def::Res::PrimTy(hir::PrimTy::Float(_)) => {
                self.diagnostics
                    .emit_err(errors::UnsupportedSignature {
                        span: path.span,
                        msg: "floats are not supported yet",
                    })
                    .raise()
            }
            hir::def::Res::PrimTy(hir::PrimTy::Str) => {
                self.diagnostics
                    .emit_err(errors::UnsupportedSignature {
                        span: path.span,
                        msg: "string slices are not supported yet",
                    })
                    .raise()
            }
            hir::def::Res::PrimTy(hir::PrimTy::Char) => {
                self.diagnostics
                    .emit_err(errors::UnsupportedSignature {
                        span: path.span,
                        msg: "chars are not suported yet",
                    })
                    .raise()
            }
            hir::def::Res::Def(_, _) | hir::def::Res::SelfTy(..) => {
                self.diagnostics
                    .emit_err(errors::UnsupportedSignature {
                        span: path.span,
                        msg: "path resolved to an unsupported type",
                    })
                    .raise()
            }
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
        Ok(ty::Expr { kind, span: Some(expr.span) })
    }

    fn resolve_var(&mut self, var: ast::Ident, subst: &Subst) -> Result<ty::Var, ErrorReported> {
        match subst.get_expr(var.name) {
            Some(var) => Ok(var),
            None => {
                self.diagnostics
                    .emit_err(errors::UnresolvedVar::new(var))
                    .raise()
            }
        }
    }

    fn resolve_lit(&mut self, lit: ast::Lit) -> Result<ty::Lit, ErrorReported> {
        match lit.kind {
            ast::LitKind::Integer => {
                match lit.symbol.as_str().parse::<i128>() {
                    Ok(n) => Ok(ty::Lit::Int(n)),
                    Err(_) => {
                        self.diagnostics
                            .emit_err(errors::IntTooLarge { span: lit.span })
                            .raise()
                    }
                }
            }
            ast::LitKind::Bool => Ok(ty::Lit::Bool(lit.symbol == kw::True)),
            _ => {
                self.diagnostics
                    .emit_err(errors::UnexpectedLiteral { span: lit.span })
                    .raise()
            }
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
        Self { exprs: ScopeMap::new(), regions: FxHashMap::default(), types: ScopeMap::new() }
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

    fn insert_type(&mut self, did: DefId, name: Symbol) {
        let index = self.types.len() as u32;
        let param_ty = ty::ParamTy { index, name };
        assert!(!self.types.contains_key_at_top(&did));
        self.types.define(did, param_ty);
    }

    fn push_type_layer(&mut self) {
        self.types.push_layer();
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

    // fn raise_if_errors(&mut self) -> Result<(), ErrorReported> {
    //     if self.errors > 0 {
    //         self.errors = 0;
    //         Err(ErrorReported)
    //     } else {
    //         Ok(())
    //     }
    // }

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
    table: &mut NameResTable,
) -> Result<(), ErrorReported> {
    fn_sig
        .decl
        .inputs
        .iter()
        .try_for_each_exhaust(|ty| collect_res_ty(diagnostics, ty, table))?;

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
            collect_res_ty(diagnostics, ty, table)?;
        }
    }

    Ok(())
}

fn collect_res_ty(
    diagnostics: &mut Diagnostics,
    ty: &hir::Ty,
    table: &mut NameResTable,
) -> Result<(), ErrorReported> {
    match &ty.kind {
        hir::TyKind::Slice(ty) | hir::TyKind::Array(ty, _) => {
            collect_res_ty(diagnostics, ty, table)
        }
        hir::TyKind::Ptr(mut_ty) | hir::TyKind::Rptr(_, mut_ty) => {
            collect_res_ty(diagnostics, mut_ty.ty, table)
        }
        hir::TyKind::Tup(tys) => {
            tys.iter()
                .try_for_each(|ty| collect_res_ty(diagnostics, ty, table))
        }
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
            table.insert(ident.name, path.res);

            args.map(|args| args.args)
                .iter()
                .copied()
                .flatten()
                .try_for_each_exhaust(|arg| collect_res_generic_arg(diagnostics, arg, table))
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
    table: &mut NameResTable,
) -> Result<(), ErrorReported> {
    match arg {
        hir::GenericArg::Type(ty) => collect_res_ty(diagnostics, ty, table),
        hir::GenericArg::Lifetime(_) => {
            diagnostics
                .emit_err(errors::UnsupportedSignature {
                    span: arg.span(),
                    msg: "lifetime parameters are not supported yet",
                })
                .raise()
        }
        hir::GenericArg::Const(_) => {
            diagnostics
                .emit_err(errors::UnsupportedSignature {
                    span: arg.span(),
                    msg: "const generics are not supported yet",
                })
                .raise()
        }

        hir::GenericArg::Infer(_) => unreachable!(),
    }
}

struct Sorts {
    int: Symbol,
}

static SORTS: std::lazy::SyncLazy<Sorts> =
    std::lazy::SyncLazy::new(|| Sorts { int: Symbol::intern("int") });

mod errors {
    use liquid_rust_syntax::ast;
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
            Self { span: path.span, path: path.ident }
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
            Self { span: loc.span, loc }
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
            Self { span: name.span, name }
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
            Self { span: sort.span, sort }
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
            Self { span: var.span, var }
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
