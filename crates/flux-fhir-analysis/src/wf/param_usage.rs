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

pub(crate) fn check<'genv>(infcx: &InferCtxt<'genv, '_>, node: &fhir::OwnerNode<'genv>) -> Result {
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

    fn run(mut self, f: impl FnOnce(&mut Self)) -> Result {
        f(&mut self);
        self.errors.to_result()
    }

    /// Insert params that are considered to be value determined to `xi`.
    fn insert_value_determined(&mut self, expr: &fhir::Expr) {
        match expr.kind {
            fhir::ExprKind::Var(fhir::QPathExpr::Resolved(path, _))
                if let fhir::Res::Param(_, id) = path.res =>
            {
                self.xi.insert(id, ());
            }
            fhir::ExprKind::Record(fields) => {
                for field in fields {
                    self.insert_value_determined(field);
                }
            }
            fhir::ExprKind::Constructor(_, fields, _) => {
                for field in fields {
                    self.insert_value_determined(&field.expr);
                }
            }
            _ => {}
        }
    }

    /// Checks that refinement parameters of function sort are used in allowed positions.
    fn check_func_params_uses(&mut self, expr: &fhir::Expr, is_top_level_conj: bool) {
        match expr.kind {
            fhir::ExprKind::BinaryOp(bin_op, e1, e2) | fhir::ExprKind::PrimApp(bin_op, e1, e2) => {
                let is_top_level_conj = is_top_level_conj && matches!(bin_op, fhir::BinOp::And);
                self.check_func_params_uses(e1, is_top_level_conj);
                self.check_func_params_uses(e2, is_top_level_conj);
            }
            fhir::ExprKind::UnaryOp(_, e) => self.check_func_params_uses(e, false),
            fhir::ExprKind::App(func, args) => {
                if !is_top_level_conj
                    && let fhir::Res::Param(_, id) = func.res
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
            fhir::ExprKind::Var(fhir::QPathExpr::Resolved(path, _)) => {
                if let fhir::Res::Param(_, id) = path.res
                    && let sort @ rty::Sort::Func(_) = self.infcx.param_sort(id)
                {
                    self.errors.emit(InvalidParamPos::new(path.span, &sort));
                }
            }
            fhir::ExprKind::Var(fhir::QPathExpr::TypeRelative(..)) => {
                // TODO(nilehmann) should we check the usage inside the `qself`?
            }
            fhir::ExprKind::IfThenElse(e1, e2, e3) => {
                self.check_func_params_uses(e1, false);
                self.check_func_params_uses(e3, false);
                self.check_func_params_uses(e2, false);
            }
            fhir::ExprKind::Literal(_) => {}
            fhir::ExprKind::Dot(base, _) => {
                self.check_func_params_uses(base, false);
            }
            fhir::ExprKind::Abs(_, body) => {
                self.check_func_params_uses(body, true);
            }
            fhir::ExprKind::BoundedQuant(_, _, _, body) => {
                self.check_func_params_uses(body, false);
            }
            fhir::ExprKind::Record(exprs) | fhir::ExprKind::SetLiteral(exprs) => {
                for field in exprs {
                    self.check_func_params_uses(field, false);
                }
            }
            fhir::ExprKind::Constructor(_, fields, spread) => {
                if let Some(spread) = spread {
                    self.check_func_params_uses(&spread.expr, false);
                }
                for field in fields {
                    self.check_func_params_uses(&field.expr, false);
                }
            }
            fhir::ExprKind::Block(decls, body) => {
                for decl in decls {
                    self.check_func_params_uses(&decl.init, false);
                }
                self.check_func_params_uses(body, false);
            }
            fhir::ExprKind::Err(_) => {
                // an error has already been reported so we can just skip
            }
        }
    }

    /// Check that Hindly parameters in `params` appear in a value determined position
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

impl<'genv> fhir::visit::Visitor<'genv> for ParamUsesChecker<'_, 'genv, '_> {
    fn visit_node(&mut self, node: &fhir::OwnerNode<'genv>) {
        if node.fn_sig().is_some() {
            // Check early refinement parameters in fn-like nodes
            let snapshot = self.xi.snapshot();
            fhir::visit::walk_node(self, node);
            self.check_params_are_value_determined(node.generics().refinement_params);
            self.xi.rollback_to(snapshot);
        } else {
            fhir::visit::walk_node(self, node);
        }
    }

    fn visit_ty_alias(&mut self, ty_alias: &fhir::TyAlias<'genv>) {
        fhir::visit::walk_ty_alias(self, ty_alias);
        self.check_params_are_value_determined(ty_alias.index.as_slice());
    }

    fn visit_struct_def(&mut self, struct_def: &fhir::StructDef<'genv>) {
        if let fhir::StructKind::Transparent { fields } = struct_def.kind {
            walk_list!(self, visit_field_def, fields);
            self.check_params_are_value_determined(struct_def.params);
        }
    }

    fn visit_variant(&mut self, variant: &fhir::VariantDef<'genv>) {
        let snapshot = self.xi.snapshot();
        fhir::visit::walk_variant(self, variant);
        self.check_params_are_value_determined(variant.params);
        self.xi.rollback_to(snapshot);
    }

    fn visit_variant_ret(&mut self, ret: &fhir::VariantRet<'genv>) {
        let snapshot = self.xi.snapshot();
        fhir::visit::walk_variant_ret(self, ret);
        self.xi.rollback_to(snapshot);
    }

    fn visit_fn_output(&mut self, output: &fhir::FnOutput<'genv>) {
        let snapshot = self.xi.snapshot();
        fhir::visit::walk_fn_output(self, output);
        self.check_params_are_value_determined(output.params);
        self.xi.rollback_to(snapshot);
    }

    fn visit_ty(&mut self, ty: &fhir::Ty<'genv>) {
        match &ty.kind {
            fhir::TyKind::StrgRef(_, loc, ty) => {
                let (_, id) = loc.res.expect_param();
                self.xi.insert(id, ());
                self.visit_ty(ty);
            }
            fhir::TyKind::Exists(params, ty) => {
                self.visit_ty(ty);
                self.check_params_are_value_determined(params);
            }
            fhir::TyKind::Indexed(bty, expr) => {
                fhir::visit::walk_bty(self, bty);
                self.insert_value_determined(expr);
                self.check_func_params_uses(expr, false);
            }
            _ => fhir::visit::walk_ty(self, ty),
        }
    }

    fn visit_expr(&mut self, expr: &fhir::Expr) {
        self.check_func_params_uses(expr, true);
    }

    fn visit_path_segment(&mut self, segment: &fhir::PathSegment<'genv>) {
        let is_box = self.infcx.genv.is_box(segment.res);

        for (i, arg) in segment.args.iter().enumerate() {
            let snapshot = self.xi.snapshot();
            self.visit_generic_arg(arg);
            if !(is_box && i == 0) {
                self.xi.rollback_to(snapshot);
            }
        }
        walk_list!(self, visit_assoc_item_constraint, segment.constraints);
    }
}
