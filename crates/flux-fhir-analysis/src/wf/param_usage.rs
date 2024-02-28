//! Code to check whether refinement parameters are used in allowed positions.
//!
//! The correct usage of a parameter depends on whether its infer mode is [evar] or [kvar].
//! For evar mode, parameters must be used at least once as an index in a position that fully
//! determines their value (see <https://arxiv.org/pdf/2209.13000.pdf> for details). Parameters
//! with kvar mode (i.e., abstract refinement predicates) must only be used in function position
//! in a top-level conjunction such that they result in a proper horn constraint after being
//! substituted by a kvar as required by fixpoint.
//!
//! [evar]: `fhir::InferMode::EVar`
//! [kvar]: `fhir::InferMode::KVar`

use flux_errors::Errors;
use flux_middle::{
    fhir::{self, visit::Visitor},
    rty, walk_list,
};
use rustc_data_structures::snapshot_map;
use rustc_span::ErrorGuaranteed;

use super::{
    errors::{InvalidParamPos, ParamNotDetermined},
    sortck::InferCtxt,
};

type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

pub(crate) fn check(infcx: &InferCtxt, node: &fhir::Node) -> Result {
    ParamUsesChecker::new(infcx).run(|ck| ck.visit_node(node))
}

struct ParamUsesChecker<'a, 'genv, 'tcx> {
    infcx: &'a InferCtxt<'genv, 'tcx>,
    /// Keeps track of all refinement parameters that are used as an index such that their value is fully
    /// determined. The name xi is taken from [1], where the well-formedness judgment uses an uppercase
    /// Xi (Ξ) for a context that is similar in purpose.
    ///
    /// This is basically a set of [`fhir::ParamId`] implemented with a snapshot map such that elements
    /// can be removed in batch when there's a change in polarity.
    ///
    /// [1]: https://arxiv.org/pdf/2209.13000.pdf
    xi: snapshot_map::SnapshotMap<fhir::ParamId, ()>,
    errors: Errors<'genv>,
}

impl<'a, 'genv, 'tcx> ParamUsesChecker<'a, 'genv, 'tcx> {
    fn new(infcx: &'a InferCtxt<'genv, 'tcx>) -> Self {
        Self { infcx, xi: Default::default(), errors: Errors::new(infcx.genv.sess()) }
    }

    fn run(mut self, f: impl FnOnce(&mut ParamUsesChecker)) -> Result {
        f(&mut self);
        self.errors.into_result()
    }

    /// Checks that refinement parameters of function sort are used in allowed positions.
    fn check_func_params_uses(&mut self, expr: &fhir::Expr, is_top_level_conj: bool) {
        match expr.kind {
            fhir::ExprKind::BinaryOp(bin_op, e1, e2) => {
                let is_pred = is_top_level_conj && matches!(bin_op, fhir::BinOp::And);
                self.check_func_params_uses(e1, is_pred);
                self.check_func_params_uses(e2, is_pred);
            }
            fhir::ExprKind::UnaryOp(_, e) => self.check_func_params_uses(e, false),
            fhir::ExprKind::App(func, args) => {
                if !is_top_level_conj
                    && let fhir::ExprRes::Param(_, id) = func.res
                    && let fhir::InferMode::KVar = self.infcx.infer_mode(id)
                {
                    self.errors
                        .emit(InvalidParamPos::new(func.span, &self.infcx.param_sort(id)));
                }
                for arg in args {
                    self.check_func_params_uses(arg, false);
                }
            }
            fhir::ExprKind::Alias(_, func_args) => {
                // TODO(nilehmann) should we check the usage inside the `AliasPred`?
                for arg in func_args {
                    self.check_func_params_uses(arg, false);
                }
            }
            fhir::ExprKind::Var(var, _) => {
                if let fhir::ExprRes::Param(_, id) = var.res
                    && let sort @ rty::Sort::Func(_) = self.infcx.param_sort(id)
                {
                    self.errors.emit(InvalidParamPos::new(var.span, &sort));
                }
            }
            fhir::ExprKind::IfThenElse(e1, e2, e3) => {
                self.check_func_params_uses(e1, false);
                self.check_func_params_uses(e3, false);
                self.check_func_params_uses(e2, false);
            }
            fhir::ExprKind::Literal(_) => {}
            fhir::ExprKind::Dot(var, _) => {
                if let fhir::ExprRes::Param(_, id) = var.res
                    && let sort @ rty::Sort::Func(_) = &self.infcx.param_sort(id)
                {
                    self.errors.emit(InvalidParamPos::new(var.span, sort));
                }
            }
        }
    }

    fn check_params_are_value_determined(&mut self, params: &[fhir::RefineParam]) {
        for param in params {
            let determined = self.xi.remove(param.id);
            if self.infcx.infer_mode(param.id) == fhir::InferMode::EVar && !determined {
                self.errors
                    .emit(ParamNotDetermined::new(param.span, param.name));
            }
        }
    }
}

impl fhir::visit::Visitor for ParamUsesChecker<'_, '_, '_> {
    fn visit_ty_alias(&mut self, ty_alias: &fhir::TyAlias) {
        fhir::visit::walk_ty_alias(self, ty_alias);
        self.check_params_are_value_determined(ty_alias.index_params);
    }

    fn visit_struct_def(&mut self, struct_def: &fhir::StructDef) {
        if let fhir::StructKind::Transparent { fields } = struct_def.kind {
            walk_list!(self, visit_field_def, fields);
            self.check_params_are_value_determined(struct_def.params);
        }
    }

    fn visit_variant(&mut self, variant: &fhir::VariantDef) {
        let snapshot = self.xi.snapshot();
        fhir::visit::walk_variant(self, variant);
        self.check_params_are_value_determined(variant.params);
        self.xi.rollback_to(snapshot);
    }

    fn visit_variant_ret(&mut self, ret: &fhir::VariantRet) {
        let snapshot = self.xi.snapshot();
        fhir::visit::walk_variant_ret(self, ret);
        self.xi.rollback_to(snapshot);
    }

    fn visit_refine_arg(&mut self, arg: &fhir::RefineArg) {
        match arg.kind {
            fhir::RefineArgKind::Expr(expr) => {
                if let fhir::ExprKind::Var(var, _) = &expr.kind {
                    if let fhir::ExprRes::Param(_, id) = var.res {
                        self.xi.insert(id, ());
                    }
                } else {
                    self.check_func_params_uses(&expr, false);
                }
            }
            fhir::RefineArgKind::Abs(_, body) => self.check_func_params_uses(&body, true),
            fhir::RefineArgKind::Record(flds) => {
                walk_list!(self, visit_refine_arg, flds);
            }
        }
    }

    fn visit_fn_decl(&mut self, decl: &fhir::FnDecl) {
        let snapshot = self.xi.snapshot();
        fhir::visit::walk_fn_decl(self, decl);
        self.check_params_are_value_determined(decl.generics.refinement_params);
        self.xi.rollback_to(snapshot);
    }

    fn visit_fn_output(&mut self, output: &fhir::FnOutput) {
        let snapshot = self.xi.snapshot();
        fhir::visit::walk_fn_output(self, output);
        self.check_params_are_value_determined(output.params);
        self.xi.rollback_to(snapshot);
    }

    fn visit_ty(&mut self, ty: &fhir::Ty) {
        match &ty.kind {
            fhir::TyKind::Ptr(_, loc) => {
                let (_, id) = loc.res.expect_param();
                self.xi.insert(id, ());
            }
            fhir::TyKind::Exists(params, ty) => {
                self.visit_ty(ty);
                self.check_params_are_value_determined(params);
            }
            _ => {
                fhir::visit::walk_ty(self, ty);
            }
        }
    }

    fn visit_expr(&mut self, expr: &fhir::Expr) {
        self.check_func_params_uses(expr, true);
    }

    fn visit_path(&mut self, path: &fhir::Path) {
        fhir::visit::walk_path(self, path);
    }

    fn visit_path_segment(&mut self, segment: &fhir::PathSegment) {
        let is_box = self.infcx.genv.is_box(segment.res);

        for (i, arg) in segment.args.iter().enumerate() {
            let snapshot = self.xi.snapshot();
            self.visit_generic_arg(arg);
            if !(is_box && i == 0) {
                self.xi.rollback_to(snapshot);
            }
        }
        walk_list!(self, visit_type_binding, segment.bindings);
    }
}
