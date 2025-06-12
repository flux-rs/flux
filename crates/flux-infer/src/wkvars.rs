use std::{collections::HashMap, ops::ControlFlow};

use flux_middle::rty::{
    self,
    fold::{
        FallibleTypeFolder, TypeFolder, TypeSuperFoldable, TypeVisitable, TypeVisitor, TypeFoldable, },
};
use rustc_type_ir::{DebruijnIndex, INNERMOST};

pub struct WKVarInstantiator<'a> {
    /// Map from the actuals passed to this Weak KVar to its params
    ///
    /// In theory this could be a Vec<rty::Expr>, but the instantiator
    /// is configured right now to only return a single solution.
    args_to_param: &'a HashMap<rty::Expr, rty::Expr>,
    /// In theory, this could (and probably should) map to multiple
    /// solutions, i.e. a Vec<rty::Expr>.
    memo: &'a mut HashMap<rty::Expr, rty::Expr>,
    current_index: DebruijnIndex,
}

impl FallibleTypeFolder for WKVarInstantiator<'_> {
    /// We fail instantiation if we can't replace all free variables;
    /// return the name of the first unreplaceable free variable found.
    type Error = rty::Var;

    fn try_enter_binder(
        &mut self,
        _vars: &rty::BoundVariableKinds,
    ) {
        self.current_index.shift_in(1);
    }

    fn try_exit_binder(&mut self) {
        self.current_index.shift_out(1);
    }

    fn try_fold_expr(&mut self, e: &rty::Expr) -> Result<rty::Expr, rty::Var> {
        if let Some(instantiated_e) = self.memo.get(e) {
            return Ok(instantiated_e.clone());
        }

        // NOTE: In theory there is a choice here: either we substitute the
        // current expression for the parameter or we ignore it and continue
        // going. We'll choose to be greedy and always substitute if possible,
        // which I think will guarantee a solution if it exists, but I am not
        // sure.
        if let Some(param) = self.args_to_param.get(e) {
            let param_expr = param.shift_in_escaping(self.current_index.as_u32());
            self.memo.insert(e.clone(), param_expr.clone());
            return Ok(param_expr);
        }

        if let rty::ExprKind::Var(var) = e.kind() {
            // This is an escaping free var
            Err(*var)
        } else {
            let instantiated_expr = e.try_super_fold_with(self)?;
            self.memo.insert(e.clone(), instantiated_expr.clone());
            Ok(instantiated_expr)
        }
    }
}

impl WKVarInstantiator<'_> {
    /// If it succeeds: creates an expression that can replace the weak kvar,
    /// which when used as a refinement will produce the original expr in this
    /// branch after all substitutions have happened.
    ///
    /// FIXME: This does not properly deal with expressions that have bound variables:
    /// if the expression has a bound variable, we might fail the instantiation
    /// when it should succeed.
    pub fn try_instantiate_wkvar(wkvar: &rty::WKVar, expr: &rty::Expr) -> Option<rty::Expr> {
        let mut args_to_param = HashMap::new();
        std::iter::zip(
            wkvar.args.iter().map(|arg| arg.erase_spans()),
            wkvar
                .params
                .iter()
                .map(|param| rty::Expr::var(param.clone())),
        )
        .for_each(|(arg, param)| {
            ProductEtaExpander::eta_expand_products(param, arg, &mut args_to_param);
        });
        let mut instantiator = WKVarInstantiator {
            args_to_param: &args_to_param,
            memo: &mut HashMap::new(),
            current_index: INNERMOST,
        };
        instantiator.try_fold_expr(&expr.erase_spans()).ok()
    }
}

pub struct WKVarSubst {
    pub wkvar_instantiations: HashMap<rty::WKVid, rty::Expr>,
}

impl TypeFolder for WKVarSubst {
    fn fold_expr(&mut self, e: &rty::Expr) -> rty::Expr {
        match e.kind() {
            rty::ExprKind::WKVar(rty::WKVar { wkvid, .. })
                if let Some(subst_e) = self.wkvar_instantiations.get(wkvid) =>
            {
                subst_e.clone()
            }
            _ => e.super_fold_with(self),
        }
    }
}

struct ProductEtaExpander<'a> {
    // An expression that evalutes to the current_expr
    current_path: rty::Expr,
    // Maps an interior part of the product to its eta expansion.
    expr_to_eta_expansion: &'a mut HashMap<rty::Expr, rty::Expr>,
}

impl<'a> TypeVisitor for ProductEtaExpander<'a> {
    fn visit_expr(&mut self, expr: &rty::Expr) -> ControlFlow<Self::BreakTy> {
        match expr.kind() {
            rty::ExprKind::Tuple(subexprs) | rty::ExprKind::Ctor(_, subexprs) => {
                let current_path = self.current_path.clone();
                let mk_proj = |field| {
                    if let rty::ExprKind::Ctor(ctor, _) = expr.kind() {
                        rty::FieldProj::Adt { def_id: ctor.def_id(), field }
                    } else {
                        rty::FieldProj::Tuple { arity: subexprs.len(), field }
                    }
                };
                for (i, subexpr) in subexprs.iter().enumerate() {
                    self.current_path = rty::Expr::field_proj(&current_path, mk_proj(i as u32));
                    subexpr.visit_with(self)?;
                }
                ControlFlow::Continue(())
            }
            _ => {
                // NOTE: in theory this should be appending to a vec, not
                // clobbering whatever lives at expr currently. But we don't
                // currently support making multiple solutions in the weak kvar
                // instantiation so I'm not bothering.
                self.expr_to_eta_expansion
                    .insert(expr.clone(), self.current_path.clone());
                ControlFlow::Continue(())
            }
        }
    }
}

/// Recursively "unpacks" a product by eta-expanding each part of it.
/// Maps each part of the product to its eta-expanded path.
///
/// e.g.
///
///     in = {
///       current_path: self,
///       expr: TwoFields { 0: (a0.0, a0.1), 1: 42 })
///     }
///
///     out =
///       a0.0 => self.0.0
///       a0.1 => self.0.1
///       42 => self.1
impl<'a> ProductEtaExpander<'a> {
    fn eta_expand_products(
        current_path: rty::Expr,
        expr: rty::Expr,
        expr_to_eta_expansion: &'a mut HashMap<rty::Expr, rty::Expr>,
    ) {
        let mut expander = ProductEtaExpander { current_path, expr_to_eta_expansion };
        expr.visit_with(&mut expander);
    }
}
