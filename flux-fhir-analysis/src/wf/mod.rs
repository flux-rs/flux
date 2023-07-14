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
use rustc_hir::OwnerId;
use rustc_span::Symbol;

use self::sortck::InferCtxt;

struct Wf<'a, 'tcx> {
    early_cx: &'a EarlyCtxt<'a, 'tcx>,
    modes: FxHashMap<fhir::Name, fhir::InferMode>,
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
    owner: OwnerId,
) -> Result<WfckResults, ErrorGuaranteed> {
    let mut infcx = InferCtxt::new(early_cx, owner.into());
    let mut wf = Wf::new(early_cx);
    wf.check_type(&mut infcx, ty)?;
    Ok(infcx.into_results())
}

pub(crate) fn check_qualifier(
    early_cx: &EarlyCtxt,
    qualifier: &fhir::Qualifier,
) -> Result<WfckResults, ErrorGuaranteed> {
    let owner = FluxOwnerId::Flux(qualifier.name);
    let mut infcx = InferCtxt::new(early_cx, owner);
    infcx.push_layer(&qualifier.args);
    infcx.check_expr(&qualifier.expr, &fhir::Sort::Bool)?;
    Ok(infcx.into_results())
}

pub(crate) fn check_defn(
    early_cx: &EarlyCtxt,
    defn: &fhir::Defn,
) -> Result<WfckResults, ErrorGuaranteed> {
    let owner = FluxOwnerId::Flux(defn.name);
    let mut infcx = InferCtxt::new(early_cx, owner);
    infcx.push_layer(&defn.args);
    infcx.check_expr(&defn.expr, &defn.sort)?;
    Ok(infcx.into_results())
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
    ty_alias: &fhir::TyAlias,
) -> Result<WfckResults, ErrorGuaranteed> {
    let mut infcx = InferCtxt::new(early_cx, ty_alias.owner_id.into());
    let mut wf = Wf::new(early_cx);
    infcx.push_layer(ty_alias.all_params());
    wf.check_type(&mut infcx, &ty_alias.ty)?;
    wf.check_params_determined(&infcx, &ty_alias.index_params)?;
    Ok(infcx.into_results())
}

pub(crate) fn check_struct_def(
    early_cx: &EarlyCtxt,
    struct_def: &fhir::StructDef,
) -> Result<WfckResults, ErrorGuaranteed> {
    let mut infcx = InferCtxt::new(early_cx, struct_def.owner_id.into());
    let mut wf = Wf::new(early_cx);
    infcx.push_layer(&struct_def.params);

    struct_def
        .invariants
        .iter()
        .try_for_each_exhaust(|invariant| infcx.check_expr(invariant, &fhir::Sort::Bool))?;

    if let fhir::StructKind::Transparent { fields } = &struct_def.kind {
        fields
            .iter()
            .try_for_each_exhaust(|field_def| wf.check_type(&mut infcx, &field_def.ty))?;
        wf.check_params_determined(&infcx, &struct_def.params)?;
    }

    Ok(infcx.into_results())
}

pub(crate) fn check_enum_def(
    early_cx: &EarlyCtxt,
    enum_def: &fhir::EnumDef,
) -> Result<WfckResults, ErrorGuaranteed> {
    let mut infcx = InferCtxt::new(early_cx, enum_def.owner_id.into());
    let mut wf = Wf::new(early_cx);
    infcx.push_layer(&enum_def.params);

    enum_def
        .invariants
        .iter()
        .try_for_each_exhaust(|invariant| infcx.check_expr(invariant, &fhir::Sort::Bool))?;

    // We are reusing the same `InferCtxt` which may contain some variables from the enum params.
    // This is not a problem because parameters in the variants with the same name will overwrite them.
    enum_def
        .variants
        .iter()
        .try_for_each_exhaust(|variant| wf.check_variant(&mut infcx, variant))?;

    Ok(infcx.into_results())
}

pub(crate) fn check_fn_sig(
    early_cx: &EarlyCtxt,
    fn_sig: &fhir::FnSig,
    owner_id: OwnerId,
) -> Result<WfckResults, ErrorGuaranteed> {
    let mut infcx = InferCtxt::new(early_cx, owner_id.into());
    let mut wf = Wf::new(early_cx);
    for param in &fn_sig.params {
        wf.modes.insert(param.ident.name, param.mode);
    }
    infcx.push_layer(&fn_sig.params);

    let args = fn_sig
        .args
        .iter()
        .try_for_each_exhaust(|ty| wf.check_type(&mut infcx, ty));

    let requires = fn_sig
        .requires
        .iter()
        .try_for_each_exhaust(|constr| wf.check_constraint(&mut infcx, constr));

    let output = wf.check_fn_output(&mut infcx, &fn_sig.output);

    let constrs = wf.check_output_locs(fn_sig);

    args?;
    output?;
    requires?;
    constrs?;

    wf.check_params_determined(&infcx, &fn_sig.params)?;

    Ok(infcx.into_results())
}

impl<'a, 'tcx> Wf<'a, 'tcx> {
    fn new(early_cx: &'a EarlyCtxt<'a, 'tcx>) -> Self {
        Wf { early_cx, modes: Default::default(), xi: Default::default() }
    }

    fn check_params_determined(
        &mut self,
        env: &InferCtxt,
        params: &[fhir::RefineParam],
    ) -> Result<(), ErrorGuaranteed> {
        params.iter().try_for_each_exhaust(|param| {
            let determined = self.xi.remove(param.name());
            if self.infer_mode(env, param.name()) == fhir::InferMode::EVar && !determined {
                return self.emit_err(errors::ParamNotDetermined::new(param.ident));
            }
            Ok(())
        })
    }

    fn check_variant(
        &mut self,
        infcx: &mut InferCtxt,
        variant: &fhir::VariantDef,
    ) -> Result<(), ErrorGuaranteed> {
        infcx.push_layer(&variant.params);
        let fields = variant
            .fields
            .iter()
            .try_for_each_exhaust(|field| self.check_type(infcx, &field.ty));
        let expected = self.sort_of_bty(&variant.ret.bty);
        let indices = self.check_refine_arg(infcx, &variant.ret.idx, &expected);
        fields?;
        indices?;
        Ok(())
    }

    fn check_fn_output(
        &mut self,
        env: &mut InferCtxt,
        fn_output: &fhir::FnOutput,
    ) -> Result<(), ErrorGuaranteed> {
        let snapshot = self.xi.snapshot();
        env.push_layer(&fn_output.params);
        self.check_type(env, &fn_output.ret)?;
        fn_output
            .ensures
            .iter()
            .try_for_each_exhaust(|constr| self.check_constraint(env, constr))?;

        let params = self.check_params_determined(env, &fn_output.params);

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
        infcx: &mut InferCtxt,
        constr: &fhir::Constraint,
    ) -> Result<(), ErrorGuaranteed> {
        match constr {
            fhir::Constraint::Type(loc, ty) => {
                [infcx.check_loc(*loc), self.check_type(infcx, ty)]
                    .into_iter()
                    .try_collect_exhaust()
            }
            fhir::Constraint::Pred(pred) => self.check_pred(infcx, pred),
        }
    }

    fn check_type(&mut self, infcx: &mut InferCtxt, ty: &fhir::Ty) -> Result<(), ErrorGuaranteed> {
        match &ty.kind {
            fhir::TyKind::BaseTy(bty) => self.check_base_ty(infcx, bty),
            fhir::TyKind::Indexed(bty, idx) => {
                let expected = self.sort_of_bty(bty);
                self.check_refine_arg(infcx, idx, &expected)?;
                self.check_base_ty(infcx, bty)
            }
            fhir::TyKind::Exists(params, ty) => {
                infcx.push_layer(params);
                self.check_type(infcx, ty)?;
                infcx.resolve_params_sorts(params)?;
                self.check_params_determined(infcx, params)
            }
            fhir::TyKind::Ptr(_, loc) => {
                self.xi.insert(loc.name);
                infcx.check_loc(*loc)
            }
            fhir::TyKind::Tuple(tys) => {
                tys.iter()
                    .try_for_each_exhaust(|ty| self.check_type(infcx, ty))
            }
            fhir::TyKind::Ref(_, fhir::MutTy { ty, .. }) | fhir::TyKind::Array(ty, _) => {
                self.check_type(infcx, ty)
            }
            fhir::TyKind::Constr(pred, ty) => {
                self.check_type(infcx, ty)?;
                self.check_pred(infcx, pred)
            }
            fhir::TyKind::RawPtr(ty, _) => self.check_type(infcx, ty),
            fhir::TyKind::Hole | fhir::TyKind::Never => Ok(()),
        }
    }

    fn check_base_ty(
        &mut self,
        env: &mut InferCtxt,
        bty: &fhir::BaseTy,
    ) -> Result<(), ErrorGuaranteed> {
        match &bty.kind {
            fhir::BaseTyKind::Path(fhir::QPath::Resolved(self_ty, path)) => {
                if let Some(self_ty) = self_ty {
                    self.check_type(env, self_ty)?;
                }
                self.check_path(env, path)
            }
            fhir::BaseTyKind::Slice(ty) => self.check_type(env, ty),
        }
    }

    fn check_path(
        &mut self,
        env: &mut InferCtxt,
        path: &fhir::Path,
    ) -> Result<(), ErrorGuaranteed> {
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
            | fhir::Res::Param(_)
            | fhir::Res::Trait(_)
            | fhir::Res::AssocTy(_) => {}
        }
        let snapshot = self.xi.snapshot();
        let res = path.generics.iter().try_for_each_exhaust(|arg| {
            if let fhir::GenericArg::Type(ty) = arg {
                self.check_type(env, ty)
            } else {
                Ok(())
            }
        });
        if !self.early_cx.is_box(path.res) {
            self.xi.rollback_to(snapshot);
        }
        res
    }

    fn check_refine_arg(
        &mut self,
        infcx: &mut InferCtxt,
        arg: &fhir::RefineArg,
        expected: &fhir::Sort,
    ) -> Result<(), ErrorGuaranteed> {
        infcx.check_refine_arg(arg, expected)?;
        self.check_param_uses_refine_arg(infcx, arg)
    }

    fn check_pred(
        &mut self,
        infcx: &mut InferCtxt,
        expr: &fhir::Expr,
    ) -> Result<(), ErrorGuaranteed> {
        infcx.check_expr(expr, &fhir::Sort::Bool)?;
        self.check_param_uses_expr(infcx, expr, true)
    }

    /// Checks that refinement parameters of function sort are used in allowed positions.
    fn check_param_uses_refine_arg(
        &mut self,
        env: &InferCtxt,
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
            fhir::RefineArg::Record(_, flds, ..) => {
                flds.iter()
                    .try_for_each_exhaust(|arg| self.check_param_uses_refine_arg(env, arg))
            }
        }
    }

    /// Checks that refinement parameters of function sort are used in allowed positions.
    fn check_param_uses_expr(
        &self,
        env: &InferCtxt,
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
                   && let fhir::Func::Var(var, _) = func
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

    fn infer_mode(&self, env: &InferCtxt, name: fhir::Name) -> fhir::InferMode {
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
