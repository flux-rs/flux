//! Checks type well-formedness
//!
//! Well-formedness checking assumes names are correctly bound which is guaranteed after desugaring.

mod errors;
mod sortck;

use std::iter;

use flux_common::{iter::IterExt, span_bug};
use flux_errors::FluxSession;
use flux_middle::{
    early_ctxt::EarlyCtxt,
    fhir::{self, FluxOwnerId, SurfaceIdent, WfckResults},
};
use rustc_data_structures::snapshot_map::{self, SnapshotMap};
use rustc_errors::{ErrorGuaranteed, IntoDiagnostic};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::LocalDefId;
use rustc_span::Symbol;

use self::sortck::{Env, SortChecker};

struct Wf<'a, 'tcx> {
    early_cx: &'a EarlyCtxt<'a, 'tcx>,
    modes: FxHashMap<fhir::Name, fhir::InferMode>,
    wfckresults: fhir::WfckResults,
    xi: XiCtxt,
}

/// Keeps track of all refinement parameters that were used as an index such that their value is fully
/// determined. The context is called Xi because in the paper [Focusing on Liquid Refinement Typing], the
/// well-formedness judgment uses an uppercase Xi (Ξ) for a context that is similar in purpose.
///
/// This is basically a set of [`fhir::Name`] implemented with a snapshot map such that elements
/// can be removed in batch when there's a change in polarity.
///
/// [Focusing on Liquid Refinement Typing]: https://arxiv.org/pdf/2209.13000.pdf
#[derive(Default)]
struct XiCtxt(SnapshotMap<fhir::Name, ()>);

pub(crate) fn check_type(
    early_cx: &EarlyCtxt,
    ty: &fhir::Ty,
    owner: LocalDefId,
) -> Result<WfckResults, ErrorGuaranteed> {
    let mut wf = Wf::new(early_cx, FluxOwnerId::Rust(owner));
    let mut env = Env::default();
    wf.check_type(&mut env, ty)?;
    Ok(wf.into_results())
}

pub(crate) fn check_qualifier(
    early_cx: &EarlyCtxt,
    qualifier: &fhir::Qualifier,
) -> Result<(), ErrorGuaranteed> {
    let env = Env::from(&qualifier.args[..]);
    let flux_id = FluxOwnerId::Flux(qualifier.name);
    SortChecker::new(early_cx, &mut WfckResults::new(flux_id)).check_expr(
        &env,
        &qualifier.expr,
        &fhir::Sort::Bool,
    )
}

pub(crate) fn check_defn(early_cx: &EarlyCtxt, defn: &fhir::Defn) -> Result<(), ErrorGuaranteed> {
    let env = Env::from(&defn.args[..]);
    let flux_id = FluxOwnerId::Flux(defn.name);
    SortChecker::new(early_cx, &mut WfckResults::new(flux_id))
        .check_expr(&env, &defn.expr, &defn.sort)
}

pub(crate) fn check_fn_quals(
    sess: &FluxSession,
    qualifiers: &FxHashSet<Symbol>,
    fn_quals: &Vec<SurfaceIdent>,
) -> Result<(), ErrorGuaranteed> {
    for qual in fn_quals {
        if !qualifiers.contains(&qual.name) {
            let span = qual.span;
            return Err(sess.emit_err(errors::UnknownQualifier::new(span)));
        }
    }
    Ok(())
}

pub(crate) fn check_ty_alias(
    early_cx: &EarlyCtxt,
    alias: &fhir::TyAlias,
) -> Result<WfckResults, ErrorGuaranteed> {
    let mut wf = Wf::new(early_cx, FluxOwnerId::Rust(alias.def_id));
    let mut env = Env::from_iter(alias.all_params());
    wf.check_type(&mut env, &alias.ty)?;
    wf.check_params_determined(&env, alias.index_params.iter().map(|param| param.ident))?;
    Ok(wf.into_results())
}

pub(crate) fn check_struct_def(
    early_cx: &EarlyCtxt,
    struct_def: &fhir::StructDef,
) -> Result<WfckResults, ErrorGuaranteed> {
    let mut wf = Wf::new(early_cx, FluxOwnerId::Rust(struct_def.def_id));
    let mut env = Env::from(&struct_def.params[..]);

    struct_def
        .invariants
        .iter()
        .try_for_each_exhaust(|invariant| {
            wf.sort_checker()
                .check_expr(&env, invariant, &fhir::Sort::Bool)
        })?;

    if let fhir::StructKind::Transparent { fields } = &struct_def.kind {
        fields
            .iter()
            .try_for_each_exhaust(|field_def| wf.check_type(&mut env, &field_def.ty))?;
        wf.check_params_determined(&env, struct_def.params.iter().map(|param| param.ident))?;
    }

    Ok(wf.into_results())
}

pub(crate) fn check_enum_def(
    early_cx: &EarlyCtxt,
    enum_def: &fhir::EnumDef,
) -> Result<WfckResults, ErrorGuaranteed> {
    let mut wf = Wf::new(early_cx, FluxOwnerId::Rust(enum_def.def_id));

    let env = Env::from(&enum_def.params[..]);
    enum_def
        .invariants
        .iter()
        .try_for_each_exhaust(|invariant| {
            wf.sort_checker()
                .check_expr(&env, invariant, &fhir::Sort::Bool)
        })?;

    enum_def
        .variants
        .iter()
        .try_for_each_exhaust(|variant| wf.check_variant(variant))?;

    Ok(wf.into_results())
}

pub(crate) fn check_fn_sig(
    early_cx: &EarlyCtxt,
    fn_sig: &fhir::FnSig,
    def_id: LocalDefId,
) -> Result<WfckResults, ErrorGuaranteed> {
    let mut wf = Wf::new(early_cx, FluxOwnerId::Rust(def_id));
    for param in &fn_sig.params {
        wf.modes.insert(param.ident.name, param.mode);
    }
    let mut env = Env::from(&fn_sig.params[..]);

    let args = fn_sig
        .args
        .iter()
        .try_for_each_exhaust(|ty| wf.check_type(&mut env, ty));

    let requires = fn_sig
        .requires
        .iter()
        .try_for_each_exhaust(|constr| wf.check_constraint(&mut env, constr));

    let output = wf.check_fn_output(&mut env, &fn_sig.output);

    let constrs = wf.check_output_locs(fn_sig);

    args?;
    output?;
    requires?;
    constrs?;

    wf.check_params_determined(&env, fn_sig.params.iter().map(|param| param.ident))?;

    Ok(wf.into_results())
}

impl<'a, 'tcx> Wf<'a, 'tcx> {
    fn new(early_cx: &'a EarlyCtxt<'a, 'tcx>, owner: FluxOwnerId) -> Self {
        Wf {
            early_cx,
            modes: Default::default(),
            wfckresults: fhir::WfckResults::new(owner),
            xi: Default::default(),
        }
    }

    fn into_results(self) -> fhir::WfckResults {
        self.wfckresults
    }

    fn check_params_determined(
        &mut self,
        env: &Env,
        params: impl IntoIterator<Item = fhir::Ident>,
    ) -> Result<(), ErrorGuaranteed> {
        params.into_iter().try_for_each_exhaust(|param| {
            let determined = self.xi.remove(param.name);
            if self.infer_mode(env, param.name) == fhir::InferMode::EVar && !determined {
                return self.emit_err(errors::ParamNotDetermined::new(param));
            }
            Ok(())
        })
    }

    fn check_variant(&mut self, variant: &fhir::VariantDef) -> Result<(), ErrorGuaranteed> {
        let mut env = Env::from(&variant.params[..]);
        let fields = variant
            .fields
            .iter()
            .try_for_each_exhaust(|ty| self.check_type(&mut env, ty));
        let expected = self.sort_of_bty(&variant.ret.bty);
        let indices = self.check_refine_arg(&mut env, &variant.ret.idx, &expected);
        fields?;
        indices?;
        Ok(())
    }

    fn check_fn_output(
        &mut self,
        env: &mut Env,
        fn_output: &fhir::FnOutput,
    ) -> Result<(), ErrorGuaranteed> {
        let snapshot = self.xi.snapshot();
        env.push_layer(fn_output.params.iter().cloned());
        self.check_type(env, &fn_output.ret)?;
        fn_output
            .ensures
            .iter()
            .try_for_each_exhaust(|constr| self.check_constraint(env, constr))?;

        let params =
            self.check_params_determined(env, fn_output.params.iter().map(|param| param.ident));

        self.xi.rollback_to(snapshot);

        params
    }

    fn check_output_locs(&self, fn_sig: &fhir::FnSig) -> Result<(), ErrorGuaranteed> {
        let mut output_locs = FxHashSet::default();
        fn_sig
            .output
            .ensures
            .iter()
            .try_for_each_exhaust(|constr| {
                if let fhir::Constraint::Type(loc, _) = constr
                    && !output_locs.insert(loc.name)
                {
                    self.emit_err(errors::DuplicatedEnsures::new(loc))
                } else {
                    Ok(())
                }
            })?;

        fn_sig.requires.iter().try_for_each_exhaust(|constr| {
            if let fhir::Constraint::Type(loc, _) = constr
               && !output_locs.contains(&loc.name)
            {
                self.emit_err(errors::MissingEnsures::new(loc))
            } else {
                Ok(())
            }
        })
    }

    fn check_constraint(
        &mut self,
        env: &mut Env,
        constr: &fhir::Constraint,
    ) -> Result<(), ErrorGuaranteed> {
        match constr {
            fhir::Constraint::Type(loc, ty) => {
                [self.sort_checker().check_loc(env, *loc), self.check_type(env, ty)]
                    .into_iter()
                    .try_collect_exhaust()
            }
            fhir::Constraint::Pred(pred) => self.check_pred(env, pred),
        }
    }

    fn check_type(&mut self, env: &mut Env, ty: &fhir::Ty) -> Result<(), ErrorGuaranteed> {
        match &ty.kind {
            fhir::TyKind::BaseTy(bty) => self.check_base_ty(env, bty),
            fhir::TyKind::Indexed(bty, idx) => {
                let expected = self.sort_of_bty(bty);
                self.check_refine_arg(env, idx, &expected)?;
                self.check_base_ty(env, bty)
            }
            fhir::TyKind::Exists(params, ty) => {
                env.push_layer(params.iter().cloned());
                self.check_type(env, ty)?;
                self.check_params_determined(env, params.iter().map(|param| param.ident))
            }
            fhir::TyKind::Ptr(loc) => {
                self.xi.insert(loc.name);
                self.sort_checker().check_loc(env, *loc)
            }
            fhir::TyKind::Tuple(tys) => {
                tys.iter()
                    .try_for_each_exhaust(|ty| self.check_type(env, ty))
            }
            fhir::TyKind::Ref(_, ty) | fhir::TyKind::Array(ty, _) => self.check_type(env, ty),
            fhir::TyKind::Constr(pred, ty) => {
                self.check_pred(env, pred)?;
                self.check_type(env, ty)
            }
            fhir::TyKind::RawPtr(ty, _) => self.check_type(env, ty),
            fhir::TyKind::Never => Ok(()),
        }
    }

    fn check_base_ty(&mut self, env: &mut Env, bty: &fhir::BaseTy) -> Result<(), ErrorGuaranteed> {
        match &bty.kind {
            fhir::BaseTyKind::Path(path) => self.check_path(env, path),
            fhir::BaseTyKind::Slice(ty) => self.check_type(env, ty),
        }
    }

    fn check_path(&mut self, env: &mut Env, path: &fhir::Path) -> Result<(), ErrorGuaranteed> {
        match &path.res {
            fhir::Res::Alias(def_id) => {
                let sorts = self.early_cx.early_bound_sorts_of(*def_id);
                if path.refine.len() != sorts.len() {
                    return self.emit_err(errors::EarlyBoundArgCountMismatch::new(
                        path.span,
                        sorts.len(),
                        path.refine.len(),
                    ));
                }
                iter::zip(&path.refine, sorts)
                    .try_for_each_exhaust(|(arg, sort)| self.check_refine_arg(env, arg, sort))?;
            }
            fhir::Res::Enum(_)
            | fhir::Res::Struct(_)
            | fhir::Res::PrimTy(..)
            | fhir::Res::Param(_) => {}
        }
        let snapshot = self.xi.snapshot();
        let res = path
            .generics
            .iter()
            .try_for_each_exhaust(|ty| self.check_type(env, ty));
        if !self.early_cx.is_box(path.res) {
            self.xi.rollback_to(snapshot);
        }
        res
    }

    fn check_refine_arg(
        &mut self,
        env: &mut Env,
        arg: &fhir::RefineArg,
        expected: &fhir::Sort,
    ) -> Result<(), ErrorGuaranteed> {
        self.sort_checker().check_refine_arg(env, arg, expected)?;
        self.check_param_uses_refine_arg(env, arg)
    }

    fn check_pred(&mut self, env: &Env, expr: &fhir::Expr) -> Result<(), ErrorGuaranteed> {
        self.sort_checker()
            .check_expr(env, expr, &fhir::Sort::Bool)?;
        self.check_param_uses_expr(env, expr, true)
    }

    /// Checks that refinement parameters of function sort are used in allowed positions.
    fn check_param_uses_refine_arg(
        &mut self,
        env: &Env,
        arg: &fhir::RefineArg,
    ) -> Result<(), ErrorGuaranteed> {
        match arg {
            fhir::RefineArg::Expr { expr, .. } => {
                if let fhir::ExprKind::Var(var) = &expr.kind {
                    self.xi.insert(var.name);
                } else {
                    self.check_param_uses_expr(env, expr, false)?;
                }
                Ok(())
            }
            fhir::RefineArg::Abs(_, body, ..) => self.check_param_uses_expr(env, body, true),
            fhir::RefineArg::Aggregate(_, flds, ..) => {
                flds.iter()
                    .try_for_each_exhaust(|arg| self.check_param_uses_refine_arg(env, arg))
            }
        }
    }

    /// Checks that refinement parameters of function sort are used in allowed positions.
    fn check_param_uses_expr(
        &self,
        env: &Env,
        expr: &fhir::Expr,
        is_top_level_conj: bool,
    ) -> Result<(), ErrorGuaranteed> {
        match &expr.kind {
            fhir::ExprKind::BinaryOp(bin_op, exprs) => {
                let is_pred = is_top_level_conj && matches!(bin_op, fhir::BinOp::And);
                exprs
                    .iter()
                    .try_for_each_exhaust(|e| self.check_param_uses_expr(env, e, is_pred))
            }
            fhir::ExprKind::UnaryOp(_, e) => self.check_param_uses_expr(env, e, false),
            fhir::ExprKind::App(func, args) => {
                if !is_top_level_conj
                   && let fhir::Func::Var(var) = func
                   && let fhir::InferMode::KVar = self.modes[&var.name]
                {
                    return self.emit_err(errors::InvalidParamPos::new(var.span(), &env[var.name]));
                }
                args.iter()
                    .try_for_each_exhaust(|arg| self.check_param_uses_expr(env, arg, false))
            }
            fhir::ExprKind::Var(var) => {
                if let sort @ fhir::Sort::Func(_) = &env[var.name] {
                    return self.emit_err(errors::InvalidParamPos::new(var.span(), sort));
                }
                Ok(())
            }
            fhir::ExprKind::IfThenElse(exprs) => {
                exprs
                    .iter()
                    .try_for_each_exhaust(|e| self.check_param_uses_expr(env, e, false))
            }
            fhir::ExprKind::Literal(_) | fhir::ExprKind::Const(_, _) => Ok(()),
            fhir::ExprKind::Dot(var, _) => {
                if let sort @ fhir::Sort::Func(_) = &env[var.name] {
                    return self.emit_err(errors::InvalidParamPos::new(var.span(), sort));
                }
                Ok(())
            }
        }
    }

    fn infer_mode(&self, env: &Env, name: fhir::Name) -> fhir::InferMode {
        self.modes
            .get(&name)
            .copied()
            .unwrap_or_else(|| env[name].default_infer_mode())
    }

    fn sort_of_bty(&self, bty: &fhir::BaseTy) -> fhir::Sort {
        self.early_cx
            .sort_of_bty(bty)
            .unwrap_or_else(|| span_bug!(bty.span, "unrefinable base type: `{bty:?}`"))
    }

    fn sort_checker(&mut self) -> SortChecker<'_, 'tcx> {
        SortChecker::new(self.early_cx, &mut self.wfckresults)
    }

    #[track_caller]
    fn emit_err<'b, R>(&'b self, err: impl IntoDiagnostic<'b>) -> Result<R, ErrorGuaranteed> {
        Err(self.early_cx.emit_err(err))
    }
}

impl XiCtxt {
    fn insert(&mut self, name: fhir::Name) {
        self.0.insert(name, ());
    }

    fn remove(&mut self, name: fhir::Name) -> bool {
        self.0.remove(name)
    }

    fn snapshot(&mut self) -> snapshot_map::Snapshot {
        self.0.snapshot()
    }

    fn rollback_to(&mut self, snapshot: snapshot_map::Snapshot) {
        self.0.rollback_to(snapshot);
    }
}
