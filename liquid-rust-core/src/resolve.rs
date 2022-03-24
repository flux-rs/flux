use crate::{
    desugar::desugar,
    ty::{self, Name},
};
use hir::{Impl, ItemId, ItemKind};
use liquid_rust_common::{errors::ErrorReported, index::IndexGen, iter::IterExt};
use liquid_rust_syntax::{
    ast,
    ast::AdtDef,
    surface::{self, DefFnSig},
};
// use quickscope::ScopeMap;
use rustc_hash::FxHashMap;
use rustc_hir::{self as hir, def_id::LocalDefId};
use rustc_middle::ty::TyCtxt;
// use rustc_session::{Session, SessionDiagnostic};
use rustc_span::{sym, Span, Symbol};

use crate::{
    desugar::{
        convert_loc, desugar_exists, desugar_expr, desugar_loc, desugar_pure, desugar_refine,
    },
    diagnostics::{errors, Diagnostics},
    subst::Subst,
};

type NameResTable = FxHashMap<Symbol, hir::def::Res>;

pub struct Resolver<'tcx> {
    tcx: TyCtxt<'tcx>,
    diagnostics: Diagnostics<'tcx>,
    name_res_table: NameResTable,
    parent: Option<&'tcx Impl<'tcx>>,
}

enum ResolvedPath {
    BaseTy(ty::BaseTy),
    ParamTy(ty::ParamTy),
    Float(ty::FloatTy),
}

impl<'tcx> Resolver<'tcx> {
    pub fn from_fn(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> Result<Resolver<'tcx>, ErrorReported> {
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

        Ok(Resolver { tcx, diagnostics, name_res_table, parent })
    }

    /// `desugar_def_sig(sig)` translates a `DefFnSig` into a `core::FnSig`, and is used by
    ///  * functions with specs whose `BareFnSig` is first resolved by `resolve_bare_sig` and
    ///  * functions without specs whose `rust::FnSig` is used to generate a default `DefFnSig`
    fn desugar(
        &mut self,
        def_id: LocalDefId,
        dsig: surface::DefFnSig,
    ) -> Result<ty::FnSig, ErrorReported> {
        let mut subst = self.resolve_rust_generics(def_id);
        let name_gen = IndexGen::new();
        desugar(dsig, &name_gen, &mut subst, &mut self.diagnostics)
    }

    /// `default_fn_sig(f, span)` uses the type-context to generate a default `DefFnSig` for `f`
    fn default_fn_sig(
        &mut self,
        def_id: LocalDefId,
        span: Span,
    ) -> Result<DefFnSig, ErrorReported> {
        let binder_sig = self.tcx.fn_sig(def_id);
        // let Some(rust_sig) = self.tcx.fn_sig(def_id).no_bound_vars();
        let rust_sig = self.tcx.erase_late_bound_regions(binder_sig);
        // print!("default_sig: {:?}", rust_sig);
        Ok(surface::default_fn_sig(rust_sig, span))
    }

    /// `resolve_bare_sig(f, sig)` uses the rust-type sig for `f` to
    /// 1. generate a "default" signature for `f`
    /// 2. zip that default sig with `sig` to get a resolved `DefFnSig` for `f`.
    fn resolve_bare_sig(
        &mut self,
        def_id: LocalDefId,
        sig: surface::BareFnSig,
    ) -> Result<surface::DefFnSig, ErrorReported> {
        let dsig = self.default_fn_sig(def_id, sig.span)?;
        let res = surface::zip::zip_bare_def(sig, dsig);
        // print!("resolve_bare_sig {:?}", res);
        Ok(res)
    }

    /// `desugar_bare_sig(f, sig)` resolves the `sig:BareSig` and then desugars into a `core::FnSig`
    fn desugar_bare_sig(
        &mut self,
        def_id: LocalDefId,
        ssig: surface::BareFnSig,
    ) -> Result<ty::FnSig, ErrorReported> {
        let dsig = self.resolve_bare_sig(def_id, ssig)?;
        self.desugar(def_id, dsig)
    }

    /// `default_sig(f)` produces a "default" (trivial) `core::FnSig` for `f`
    pub fn default_sig(
        &mut self,
        def_id: LocalDefId,
        span: Span,
    ) -> Result<ty::FnSig, ErrorReported> {
        let dsig = self.default_fn_sig(def_id, span)?;
        self.desugar(def_id, dsig)
    }

    pub fn resolve_qualifier(
        tcx: TyCtxt<'tcx>,
        qualifier: ast::Qualifier,
    ) -> Result<ty::Qualifier, ErrorReported> {
        let name_gen = IndexGen::new();
        let mut subst = Subst::new();
        let mut diagnostics = Diagnostics::new(tcx.sess);

        let name_res_table = FxHashMap::default();
        let parent = None;

        let args = qualifier
            .args
            .into_iter()
            .map(|qualifparam| {
                let loc = qualifparam.name;
                let sort = resolve_sort(&mut diagnostics, qualifparam.sort)?;
                desugar_pure(loc, sort, &name_gen, &mut subst, &mut diagnostics)
            })
            .try_collect_exhaust();

        let mut resolver = Self { tcx, diagnostics, parent, name_res_table };

        let expr = desugar_expr(qualifier.expr, &subst, &mut resolver.diagnostics)?;

        let name = qualifier.name.name.to_ident_string();

        Ok(ty::Qualifier { name, args: args?, expr })
    }

    pub fn from_adt(
        tcx: TyCtxt<'tcx>,
        def_id: LocalDefId,
    ) -> Result<Resolver<'tcx>, ErrorReported> {
        let mut diagnostics = Diagnostics::new(tcx.sess);
        let item = tcx.hir().expect_item(def_id);
        let data = if let ItemKind::Struct(data, _) = &item.kind {
            data
        } else {
            panic!("expected a struct")
        };

        let mut name_res_table = FxHashMap::default();
        for field in data.fields() {
            collect_res_ty(&mut diagnostics, field.ty, &mut name_res_table)?;
        }

        Ok(Self { tcx, diagnostics, parent: None, name_res_table })
    }

    pub fn resolve_adt_def(&mut self, spec: AdtDef) -> Result<ty::AdtDef, ErrorReported> {
        let name_gen = IndexGen::new();
        let mut subst = Subst::new();

        let (refined_by, constrs) = match spec.refined_by {
            Some(refined_by) => self.resolve_generic_values(refined_by, &name_gen, &mut subst)?,
            None => (vec![], vec![]),
        };
        assert!(constrs.is_empty());

        if spec.opaque {
            Ok(ty::AdtDef::Opaque { refined_by })
        } else {
            let fields = spec
                .fields
                .into_iter()
                .map(|ty| self.resolve_ty(ty.unwrap(), &mut subst))
                .try_collect_exhaust()?;

            Ok(ty::AdtDef::Transparent { refined_by, fields })
        }
    }

    /// Resolve rust-generics from parent
    fn resolve_rust_generics(&mut self, def_id: LocalDefId) -> Subst {
        let mut subst = Subst::new();

        if let Some(parent) = self.parent {
            subst.insert_generic_types(self.tcx, &parent.generics);
            subst.push_type_layer();
        }
        let hir_generics = self.tcx.hir().get_generics(def_id).unwrap();
        subst.insert_generic_types(self.tcx, hir_generics);

        subst
    }

    fn resolve_ast_fn_sig(
        &mut self,
        def_id: LocalDefId,
        fn_sig: ast::FnSig,
    ) -> Result<ty::FnSig, ErrorReported> {
        // 1. Initialize `subst` with rust-generics
        let mut subst = self.resolve_rust_generics(def_id);

        // 2. Fresh name generator
        let name_gen = IndexGen::new();

        // 3. Resolve pure-binders and constraints
        let (mut params, mut requires) =
            self.resolve_generic_values(fn_sig.generics, &name_gen, &mut subst)?;

        // 4. Resolve INPUT locations
        for (loc, ty) in fn_sig.requires {
            let loc = desugar_loc(loc, &name_gen, &mut subst);
            let ty = self.resolve_ty(ty, &mut subst)?;

            params.push(ty::Param { name: loc, sort: ty::Sort::Loc });
            requires.push(ty::Constr::Type(loc, ty));
        }

        // 5. Resolve INPUT types
        let args = fn_sig
            .args
            .into_iter()
            .map(|ty| self.resolve_ty(ty, &mut subst))
            .try_collect_exhaust();

        // 5. Resolve OUTPUT locations
        let ensures = fn_sig
            .ensures
            .into_iter()
            .map(|(loc, ty)| {
                let loc = convert_loc(loc, &subst, &mut self.diagnostics)?;
                let ty = self.resolve_ty(ty, &mut subst)?;
                Ok(ty::Constr::Type(loc, ty))
            })
            .try_collect_exhaust();

        // 6. Resolve OUTPUT type
        let ret = self.resolve_ty(fn_sig.ret, &mut subst);

        Ok(ty::FnSig { params, requires, args: args?, ret: ret?, ensures: ensures? })
    }

    fn _resolve_sur_fn_sig_old(
        &mut self,
        def_id: LocalDefId,
        ssig: surface::BareFnSig,
    ) -> Result<ty::FnSig, ErrorReported> {
        let ast_sig = surface::desugar(ssig);
        self.resolve_ast_fn_sig(def_id, ast_sig)
    }

    pub fn resolve_fn_sig(
        &mut self,
        def_id: LocalDefId,
        fn_sig: surface::BareSig,
    ) -> Result<ty::FnSig, ErrorReported> {
        match fn_sig {
            surface::BareSig::AstSig(sig) => self.resolve_ast_fn_sig(def_id, sig),
            surface::BareSig::SurSig(sig) => self.desugar_bare_sig(def_id, sig),
        }
    }

    fn resolve_generic_values(
        &mut self,
        generics: ast::Generics,
        name_gen: &IndexGen<Name>,
        subst: &mut Subst,
    ) -> Result<(Vec<ty::Param>, Vec<ty::Constr>), ErrorReported> {
        let params = generics
            .iter()
            .map(|param| {
                let sort = resolve_sort(&mut self.diagnostics, param.sort)?;
                desugar_pure(param.name, sort, name_gen, subst, &mut self.diagnostics)
            })
            .try_collect_exhaust()?;

        let constrs = generics
            .into_iter()
            .filter_map(|param| param.pred)
            .map(|pred| Ok(ty::Constr::Pred(desugar_expr(pred, subst, &mut self.diagnostics)?)))
            .try_collect_exhaust()?;

        Ok((params, constrs))
    }

    fn resolve_ty(&mut self, ty: ast::Ty, subst: &mut Subst) -> Result<ty::Ty, ErrorReported> {
        match ty.kind {
            ast::TyKind::BaseTy(path) => {
                match self.resolve_path(path, subst)? {
                    ResolvedPath::BaseTy(bty) => Ok(ty::Ty::Exists(bty, ty::Pred::TRUE)),
                    ResolvedPath::ParamTy(param_ty) => Ok(ty::Ty::Param(param_ty)),
                    ResolvedPath::Float(float_ty) => Ok(ty::Ty::Float(float_ty)),
                }
            }
            ast::TyKind::RefineTy { path, refine } => {
                match self.resolve_path(path, subst)? {
                    ResolvedPath::BaseTy(bty) => {
                        let refine = desugar_refine(refine, subst, &mut self.diagnostics)?;
                        Ok(ty::Ty::Refine(bty, refine))
                    }
                    ResolvedPath::ParamTy(_) => {
                        self.diagnostics
                            .emit_err(errors::RefinedTypeParam { span: ty.span })
                            .raise()
                    }
                    ResolvedPath::Float(_) => {
                        self.diagnostics
                            .emit_err(errors::RefinedFloat { span: ty.span })
                            .raise()
                    }
                }
            }
            ast::TyKind::Exists { bind, path, pred } => {
                match self.resolve_path(path, subst)? {
                    ResolvedPath::BaseTy(bty) => {
                        let pred = desugar_exists(bind, pred, subst, &mut self.diagnostics)?;
                        Ok(ty::Ty::Exists(bty, pred))
                    }
                    ResolvedPath::ParamTy(_) => {
                        self.diagnostics
                            .emit_err(errors::RefinedTypeParam { span: ty.span })
                            .raise()
                    }
                    ResolvedPath::Float(_) => {
                        self.diagnostics
                            .emit_err(errors::RefinedFloat { span: ty.span })
                            .raise()
                    }
                }
            }
            ast::TyKind::StrgRef(loc) => {
                if let Some(name) = subst.get_loc(loc.name) {
                    let loc = ty::Ident { name, source_info: (loc.span, loc.name) };
                    Ok(ty::Ty::StrgRef(loc))
                } else {
                    self.diagnostics
                        .emit_err(errors::UnresolvedLoc::new(loc))
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
    ) -> Result<ResolvedPath, ErrorReported> {
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
                Ok(ResolvedPath::ParamTy(subst.get_param_ty(did).unwrap()))
            }
            hir::def::Res::Def(hir::def::DefKind::Struct, did) => {
                let args = path
                    .args
                    .into_iter()
                    .flatten()
                    .map(|ty| self.resolve_ty(ty, subst))
                    .try_collect_exhaust()?;
                Ok(ResolvedPath::BaseTy(ty::BaseTy::Adt(did, args)))
            }
            hir::def::Res::PrimTy(hir::PrimTy::Int(int_ty)) => {
                Ok(ResolvedPath::BaseTy(ty::BaseTy::Int(rustc_middle::ty::int_ty(int_ty))))
            }
            hir::def::Res::PrimTy(hir::PrimTy::Uint(uint_ty)) => {
                Ok(ResolvedPath::BaseTy(ty::BaseTy::Uint(rustc_middle::ty::uint_ty(uint_ty))))
            }
            hir::def::Res::PrimTy(hir::PrimTy::Bool) => Ok(ResolvedPath::BaseTy(ty::BaseTy::Bool)),
            hir::def::Res::PrimTy(hir::PrimTy::Float(float_ty)) => {
                Ok(ResolvedPath::Float(rustc_middle::ty::float_ty(float_ty)))
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
            hir::def::Res::Def(_, _) | hir::def::Res::SelfTy { .. } => {
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
}

fn resolve_sort(
    diagnostics: &mut Diagnostics,
    sort: ast::Ident,
) -> Result<ty::Sort, ErrorReported> {
    if sort.name == SORTS.int {
        Ok(ty::Sort::Int)
    } else if sort.name == sym::bool {
        Ok(ty::Sort::Bool)
    } else {
        diagnostics
            .emit_err(errors::UnresolvedSort::new(sort))
            .raise()
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
