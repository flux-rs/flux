use std::collections::HashMap;

use flux_middle::rty::{
        self,
        fold::{FallibleTypeFolder, TypeFolder, TypeFoldable, TypeSuperFoldable},
    };
use rustc_type_ir::{DebruijnIndex, INNERMOST};

pub struct WKVarInstantiator<'a> {
    /// Map from the actuals passed to this Weak KVar to its params
    ///
    /// In theory this could be a Vec<rty::Var>, but the instantiator
    /// is configured right now to only return a single solution.
    args_to_param: &'a HashMap<rty::Expr, rty::Var>,
    /// In theory, this could (and probably should) map to multiple
    /// solutions, i.e. a Vec<rty::Expr>.
    memo: &'a mut HashMap<rty::Expr, rty::Expr>,
    current_index: DebruijnIndex,
}

impl FallibleTypeFolder for WKVarInstantiator<'_> {
    /// We fail instantiation if we can't replace all free variables;
    /// return the name of the first unreplaceable free variable found.
    type Error = rty::Var;

    fn try_fold_binder<T: TypeFoldable>(
        &mut self,
        t: &rty::Binder<T>,
    ) -> Result<rty::Binder<T>, rty::Var> {
        self.current_index.shift_in(1);
        let r = t.try_super_fold_with(self);
        self.current_index.shift_out(1);
        r
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
            let param_expr = rty::Expr::var(param.shift_in(self.current_index.as_u32()));
            self.memo.insert(e.clone(), param_expr.clone());
            return Ok(param_expr);
        }

        if let rty::ExprKind::Var(var) = e.kind() {
            // This is an escaping free var
            Err(*var)
        } else {
            let instantiated_expr = e.try_super_fold_with(self)?;
            self.memo
                .insert(e.clone(), instantiated_expr.clone());
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
        let args_to_param: HashMap<rty::Expr, rty::Var> = std::iter::zip(
            wkvar.args.iter().map(|arg| arg.erase_spans()),
            wkvar.params.iter().copied(),
        )
        .collect();
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
            rty::ExprKind::WKVar(rty::WKVar{wkvid, ..}) if let Some(subst_e) = self.wkvar_instantiations.get(wkvid) => {
                subst_e.clone()
            }
            _ => {
                e.super_fold_with(self)
            }
        }
    }
}
