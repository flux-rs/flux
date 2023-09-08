//! Checks type well-formedness
//!
//! Well-formedness checking assumes names are correctly bound which is guaranteed after desugaring.

mod errors;
mod sortck;

use std::iter;

use flux_common::{iter::IterExt, span_bug};
use flux_errors::FluxSession;
use flux_middle::{
    fhir::{self, FluxOwnerId, SurfaceIdent, WfckResults},
    global_env::GlobalEnv,
};
use rustc_data_structures::snapshot_map::{self, SnapshotMap};
use rustc_errors::{ErrorGuaranteed, IntoDiagnostic};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{def::DefKind, OwnerId};
use rustc_span::Symbol;

use self::sortck::InferCtxt;

struct Wf<'a, 'tcx> {
    genv: &'a GlobalEnv<'a, 'tcx>,
    modes: FxHashMap<fhir::Name, fhir::InferMode>,
    xi: XiCtxt,
}

/// Keeps track of all refinement parameters that are used as an index such that their value is fully
/// determined. The context is called Xi because in the paper [Focusing on Liquid Refinement Typing],
/// the well-formedness judgment uses an uppercase Xi (Ξ) for a context that is similar in purpose.
///
/// This is basically a set of [`fhir::Name`] implemented with a snapshot map such that elements
/// can be removed in batch when there's a change in polarity.
///
/// [Focusing on Liquid Refinement Typing]: https://arxiv.org/pdf/2209.13000.pdf
#[derive(Default)]
struct XiCtxt(SnapshotMap<fhir::Name, ()>);

pub(crate) fn check_type(
    genv: &GlobalEnv,
    ty: &fhir::Ty,
    owner: OwnerId,
) -> Result<WfckResults, ErrorGuaranteed> {
    let mut infcx = InferCtxt::new(genv, owner.into());
    let mut wf = Wf::new(genv);
    wf.check_type(&mut infcx, ty)?;
    Ok(infcx.into_results())
}

pub(crate) fn check_qualifier(
    genv: &GlobalEnv,
    qualifier: &fhir::Qualifier,
) -> Result<WfckResults, ErrorGuaranteed> {
    let owner = FluxOwnerId::Flux(qualifier.name);
    let mut infcx = InferCtxt::new(genv, owner);
    infcx.push_layer(&qualifier.args);
    infcx.check_expr(&qualifier.expr, &fhir::Sort::Bool)?;
    Ok(infcx.into_results())
}

pub(crate) fn check_defn(
    genv: &GlobalEnv,
    defn: &fhir::Defn,
) -> Result<WfckResults, ErrorGuaranteed> {
    let owner = FluxOwnerId::Flux(defn.name);
    let mut infcx = InferCtxt::new(genv, owner);
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
    genv: &GlobalEnv,
    ty_alias: &fhir::TyAlias,
) -> Result<WfckResults, ErrorGuaranteed> {
    let mut infcx = InferCtxt::new(genv, ty_alias.owner_id.into());
    let mut wf = Wf::new(genv);
    infcx.push_layer(ty_alias.all_params());
    wf.check_type(&mut infcx, &ty_alias.ty)?;
    wf.check_params_are_determined(&infcx, &ty_alias.index_params)?;
    Ok(infcx.into_results())
}

pub(crate) fn check_struct_def(
    genv: &GlobalEnv,
    struct_def: &fhir::StructDef,
) -> Result<WfckResults, ErrorGuaranteed> {
    let mut infcx = InferCtxt::new(genv, struct_def.owner_id.into());
    let mut wf = Wf::new(genv);
    infcx.push_layer(&struct_def.params);

    struct_def
        .invariants
        .iter()
        .try_for_each_exhaust(|invariant| infcx.check_expr(invariant, &fhir::Sort::Bool))?;

    if let fhir::StructKind::Transparent { fields } = &struct_def.kind {
        fields
            .iter()
            .try_for_each_exhaust(|field_def| wf.check_type(&mut infcx, &field_def.ty))?;
        wf.check_params_are_determined(&infcx, &struct_def.params)?;
    }

    Ok(infcx.into_results())
}

pub(crate) fn check_enum_def(
    genv: &GlobalEnv,
    enum_def: &fhir::EnumDef,
) -> Result<WfckResults, ErrorGuaranteed> {
    let mut infcx = InferCtxt::new(genv, enum_def.owner_id.into());
    let mut wf = Wf::new(genv);
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

pub(crate) fn check_opaque_ty(
    genv: &GlobalEnv,
    opaque_ty: &fhir::OpaqueTy,
    owner_id: OwnerId,
) -> Result<WfckResults, ErrorGuaranteed> {
    let mut infcx = InferCtxt::new(genv, owner_id.into());
    let mut wf = Wf::new(genv);
    let parent = genv.tcx.parent(owner_id.to_def_id());
    if let Some(parent_local) = parent.as_local() &&
       let Some(params) = genv.map().get_refine_params(genv.tcx, parent_local)
    {
        setup_refine_params(&mut infcx, &mut wf, params);
    }
    wf.check_opaque_ty(&mut infcx, opaque_ty)?;
    Ok(infcx.into_results())
}

fn setup_refine_params(infcx: &mut InferCtxt, wf: &mut Wf, params: &[fhir::RefineParam]) {
    for param in params {
        wf.modes.insert(param.ident.name, param.infer_mode());
    }
    infcx.push_layer(params);
}

pub(crate) fn check_fn_sig(
    genv: &GlobalEnv,
    fn_sig: &fhir::FnSig,
    owner_id: OwnerId,
) -> Result<WfckResults, ErrorGuaranteed> {
    let mut infcx = InferCtxt::new(genv, owner_id.into());
    let mut wf = Wf::new(genv);

    setup_refine_params(&mut infcx, &mut wf, &fn_sig.params);

    let args = fn_sig
        .args
        .iter()
        .try_for_each_exhaust(|ty| wf.check_type(&mut infcx, ty));

    let requires = fn_sig
        .requires
        .iter()
        .try_for_each_exhaust(|constr| wf.check_constraint(&mut infcx, constr));

    let predicates = genv.map().get_generic_predicates(owner_id.def_id).unwrap();
    wf.check_generic_predicates(&mut infcx, predicates)?;

    let output = wf.check_fn_output(&mut infcx, &fn_sig.output);

    let constrs = wf.check_output_locs(fn_sig);

    args?;
    output?;
    requires?;
    constrs?;

    wf.check_params_are_determined(&infcx, &fn_sig.params)?;

    Ok(infcx.into_results())
}

impl<'a, 'tcx> Wf<'a, 'tcx> {
    fn new(genv: &'a GlobalEnv<'a, 'tcx>) -> Self {
        Wf { genv, modes: Default::default(), xi: Default::default() }
    }

    fn check_params_are_determined(
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

    fn check_generic_predicates(
        &mut self,
        infcx: &mut InferCtxt,
        predicates: &fhir::GenericPredicates,
    ) -> Result<(), ErrorGuaranteed> {
        predicates
            .predicates
            .iter()
            .try_for_each_exhaust(|pred| self.check_generic_predicate(infcx, pred))
    }

    fn check_generic_bound(
        &mut self,
        infcx: &mut InferCtxt,
        bound: &fhir::GenericBound,
    ) -> Result<(), ErrorGuaranteed> {
        match bound {
            fhir::GenericBound::Trait(trait_ref, _) => self.check_path(infcx, trait_ref),
            fhir::GenericBound::LangItemTrait(_, args, bindings) => {
                self.check_generic_args(infcx, args)?;
                self.check_type_bindings(infcx, bindings)?;
                Ok(())
            }
        }
    }

    fn check_opaque_ty(
        &mut self,
        infcx: &mut InferCtxt,
        opaque_ty: &fhir::OpaqueTy,
    ) -> Result<(), ErrorGuaranteed> {
        opaque_ty
            .bounds
            .iter()
            .try_for_each_exhaust(|bound| self.check_generic_bound(infcx, bound))
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

        let params = self.check_params_are_determined(env, &fn_output.params);

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
                self.check_params_are_determined(infcx, params)
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
            fhir::TyKind::OpaqueDef(_, args, _) => self.check_generic_args(infcx, args),
            fhir::TyKind::RawPtr(ty, _) => self.check_type(infcx, ty),
            fhir::TyKind::Hole | fhir::TyKind::Never => Ok(()),
        }
    }

    fn check_generic_predicate(
        &mut self,
        infcx: &mut InferCtxt,
        predicate: &fhir::WhereBoundPredicate,
    ) -> Result<(), ErrorGuaranteed> {
        self.check_type(infcx, &predicate.bounded_ty)?;
        predicate
            .bounds
            .iter()
            .map(|bound| self.check_generic_bound(infcx, bound))
            .try_collect_exhaust()
    }

    fn check_generic_args(
        &mut self,
        infcx: &mut InferCtxt,
        args: &[fhir::GenericArg],
    ) -> Result<(), ErrorGuaranteed> {
        args.iter()
            .try_for_each_exhaust(|arg| self.check_generic_arg(infcx, arg))
    }

    fn check_generic_arg(
        &mut self,
        infcx: &mut InferCtxt,
        arg: &fhir::GenericArg,
    ) -> Result<(), ErrorGuaranteed> {
        if let fhir::GenericArg::Type(ty) = arg {
            self.check_type(infcx, ty)
        } else {
            Ok(())
        }
    }

    fn check_type_bindings(
        &mut self,
        infcx: &mut InferCtxt,
        bindings: &[fhir::TypeBinding],
    ) -> Result<(), ErrorGuaranteed> {
        bindings
            .iter()
            .try_for_each_exhaust(|binding| self.check_type(infcx, &binding.term))
    }

    fn check_base_ty(
        &mut self,
        infcx: &mut InferCtxt,
        bty: &fhir::BaseTy,
    ) -> Result<(), ErrorGuaranteed> {
        match &bty.kind {
            fhir::BaseTyKind::Path(fhir::QPath::Resolved(self_ty, path)) => {
                if let Some(self_ty) = self_ty {
                    self.check_type(infcx, self_ty)?;
                }
                self.check_path(infcx, path)
            }
            fhir::BaseTyKind::Slice(ty) => self.check_type(infcx, ty),
        }
    }

    fn check_path(
        &mut self,
        infcx: &mut InferCtxt,
        path: &fhir::Path,
    ) -> Result<(), ErrorGuaranteed> {
        match &path.res {
            fhir::Res::Def(DefKind::TyAlias { .. }, def_id) => {
                let sorts = self.genv.early_bound_sorts_of(*def_id);
                if path.refine.len() != sorts.len() {
                    return self.emit_err(errors::EarlyBoundArgCountMismatch::new(
                        path.span,
                        sorts.len(),
                        path.refine.len(),
                    ));
                }
                iter::zip(&path.refine, sorts)
                    .try_for_each_exhaust(|(arg, sort)| self.check_refine_arg(infcx, arg, sort))?;
            }
            fhir::Res::SelfTyAlias { .. } | fhir::Res::Def(..) | fhir::Res::PrimTy(..) => {}
        }
        let snapshot = self.xi.snapshot();
        let args = self.check_generic_args(infcx, &path.args);
        let bindings = self.check_type_bindings(infcx, &path.bindings);
        if !self.genv.is_box(path.res) {
            self.xi.rollback_to(snapshot);
        }
        args?;
        bindings?;
        Ok(())
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
        infcx: &InferCtxt,
        arg: &fhir::RefineArg,
    ) -> Result<(), ErrorGuaranteed> {
        match arg {
            fhir::RefineArg::Expr { expr, .. } => {
                if let fhir::ExprKind::Var(var) = &expr.kind {
                    self.xi.insert(var.name);
                } else {
                    self.check_param_uses_expr(infcx, expr, false)?;
                }
                Ok(())
            }
            fhir::RefineArg::Abs(_, body, ..) => self.check_param_uses_expr(infcx, body, true),
            fhir::RefineArg::Record(_, flds, ..) => {
                flds.iter()
                    .try_for_each_exhaust(|arg| self.check_param_uses_refine_arg(infcx, arg))
            }
        }
    }

    /// Checks that refinement parameters of function sort are used in allowed positions.
    fn check_param_uses_expr(
        &self,
        infcx: &InferCtxt,
        expr: &fhir::Expr,
        is_top_level_conj: bool,
    ) -> Result<(), ErrorGuaranteed> {
        match &expr.kind {
            fhir::ExprKind::BinaryOp(bin_op, exprs) => {
                let is_pred = is_top_level_conj && matches!(bin_op, fhir::BinOp::And);
                exprs
                    .iter()
                    .try_for_each_exhaust(|e| self.check_param_uses_expr(infcx, e, is_pred))
            }
            fhir::ExprKind::UnaryOp(_, e) => self.check_param_uses_expr(infcx, e, false),
            fhir::ExprKind::App(func, args) => {
                if !is_top_level_conj
                   && let fhir::Func::Var(var, _) = func
                   && let fhir::InferMode::KVar = self.modes[&var.name]
                {
                    return self.emit_err(errors::InvalidParamPos::new(var.span(), &infcx[var.name]));
                }
                args.iter()
                    .try_for_each_exhaust(|arg| self.check_param_uses_expr(infcx, arg, false))
            }
            fhir::ExprKind::Var(var) => {
                if let sort @ fhir::Sort::Func(_) = &infcx[var.name] {
                    return self.emit_err(errors::InvalidParamPos::new(var.span(), sort));
                }
                Ok(())
            }
            fhir::ExprKind::IfThenElse(exprs) => {
                exprs
                    .iter()
                    .try_for_each_exhaust(|e| self.check_param_uses_expr(infcx, e, false))
            }
            fhir::ExprKind::Literal(_) | fhir::ExprKind::Const(_, _) => Ok(()),
            fhir::ExprKind::Dot(var, _) => {
                if let sort @ fhir::Sort::Func(_) = &infcx[var.name] {
                    return self.emit_err(errors::InvalidParamPos::new(var.span(), sort));
                }
                Ok(())
            }
        }
    }

    fn infer_mode(&self, infcx: &InferCtxt, name: fhir::Name) -> fhir::InferMode {
        self.modes
            .get(&name)
            .copied()
            .unwrap_or_else(|| infcx[name].default_infer_mode())
    }

    fn sort_of_bty(&self, bty: &fhir::BaseTy) -> fhir::Sort {
        self.genv
            .sort_of_bty(bty)
            .unwrap_or_else(|| span_bug!(bty.span, "unrefinable base type: `{bty:?}`"))
    }

    #[track_caller]
    fn emit_err<'b, R>(&'b self, err: impl IntoDiagnostic<'b>) -> Result<R, ErrorGuaranteed> {
        Err(self.genv.sess.emit_err(err))
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
