use std::ops::ControlFlow;

use flux_middle::rty::{
    self,
    fold::{
        FallibleTypeFolder, TypeFoldable, TypeFolder, TypeSuperFoldable, TypeVisitable, TypeVisitor,
    },
};
use itertools::Itertools;
use rustc_data_structures::unord::{UnordMap, UnordSet};
use rustc_type_ir::{DebruijnIndex, INNERMOST};

pub struct WKVarInstantiator<'a> {
    /// Map from the actuals passed to this Weak KVar to its params
    ///
    /// In theory this could be a Vec<rty::Expr>, but the instantiator
    /// is configured right now to only return a single solution.
    args_to_param: &'a UnordMap<rty::Expr, rty::Expr>,
    /// Set of self args
    self_args: &'a UnordSet<rty::Expr>,
    /// Were any of the self args used in the expr?
    any_self_args_used: bool,
    /// In theory, this could (and probably should) map to multiple
    /// solutions, i.e. a Vec<rty::Expr>.
    memo: &'a mut UnordMap<rty::Expr, rty::Expr>,
    current_index: DebruijnIndex,
}

impl FallibleTypeFolder for WKVarInstantiator<'_> {
    /// We fail instantiation if we can't replace all free variables;
    /// return the name of the first unreplaceable free variable found.
    type Error = rty::Var;

    fn try_enter_binder(&mut self, _vars: &rty::BoundVariableKinds) {
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
            // Check if this expression is a self_arg (if we haven't seen a
            // self_arg) yet.
            self.any_self_args_used |= self.self_args.contains(e);
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
    /// It requires that the expression uses at least one of the first
    /// `self_args` number of `wkvar_args`.
    ///
    /// There are a lot of patches we put in this algorithm to get around the fact
    /// that it is purely syntactic. We currently try to eagerly eta reduce any
    /// Ctor/Tuples + eta expand any args which aren't of that form
    ///
    /// FIXME(ck): This does not properly deal with expressions that have bound variables:
    /// if the expression has a bound variable, we might fail the instantiation
    /// when it should succeed.
    pub fn try_instantiate_wkvar_args(
        self_args: usize,
        wkvar_args: &[rty::Expr],
        expr: &rty::Expr,
    ) -> Option<rty::Binder<rty::Expr>> {
        // println!("trying to instantiate {:?} using args {:?}", expr, wkvar_args);
        let expr_without_metadata = expr.erase_metadata();
        let expr_eta_expanded_rel = expr_without_metadata.expand_bin_rels();
        let mut args_to_param = UnordMap::default();
        std::iter::zip(
            // Eta reduce and erase metadata.
            wkvar_args
                .iter()
                .map(|arg| arg.eta_reduce_projs().erase_metadata()),
            // We'll make an instantiator that is generic because this instatiation
            // may (and probably will) be used in multiple places
            (0..wkvar_args.len()).map(|var_num| {
                rty::Expr::bvar(INNERMOST, var_num.into(), rty::BoundReftKind::Anon)
            }),
        )
        .for_each(|(arg, param)| {
            ProductEtaExpander::eta_expand_products(param, arg, &mut args_to_param);
        });
        let self_args = wkvar_args[..self_args].iter().cloned().collect();
        let mut instantiator = WKVarInstantiator {
            args_to_param: &args_to_param,
            self_args: &self_args,
            any_self_args_used: false,
            memo: &mut UnordMap::default(),
            // This remains 0 because we use it to track how to shift our params,
            // so the scope is the same.
            current_index: INNERMOST,
        };
        // println!("eta expanded args: {:?}", args_to_param);
        instantiator
            .try_fold_expr(&expr_eta_expanded_rel)
            // .map_err(|e| println!("Couldn't unify with {:?}", e))
            .ok()
            .and_then(|instantiated_e| {
                if !instantiator.any_self_args_used && !instantiator.self_args.is_empty() {
                    // println!("Dropping instantiation {:?} because no self args were used", instantiated_e);
                    None
                } else {
                    Some(rty::Binder::bind_with_sorts(
                        instantiated_e,
                        &std::iter::repeat_n(rty::Sort::Err, wkvar_args.len()).collect_vec(),
                    ))
                }
            })
    }
}

pub struct WKVarSubst {
    /// A map from wkvid to each of the substitutions we made for it
    /// in whatever we folded over.
    ///
    /// In theory there should only ever be one value in this map.
    pub subst_instantiations: UnordMap<rty::WKVid, Vec<rty::Expr>>,
    pub wkvar_instantiations: UnordMap<rty::WKVid, rty::Binder<rty::Expr>>,
    /// Keep wkvars after substituting
    pub keep_wkvars: bool,
}

impl WKVarSubst {
    pub fn new(
        wkvar_instantiations: UnordMap<rty::WKVid, rty::Binder<rty::Expr>>,
        keep_wkvars: bool,
    ) -> Self {
        WKVarSubst { subst_instantiations: Default::default(), wkvar_instantiations, keep_wkvars }
    }
}

impl TypeFolder for WKVarSubst {
    fn fold_expr(&mut self, e: &rty::Expr) -> rty::Expr {
        match e.kind() {
            rty::ExprKind::WKVar(wkvar @ rty::WKVar { wkvid, .. })
                if let Some(bound_e) = self.wkvar_instantiations.get(wkvid) =>
            {
                // The bound expression has bound vars that need to be replaced
                // by the args given to the wkvar (in order).
                let instantiated_e = bound_e.replace_bound_refts(&wkvar.args);
                self.subst_instantiations
                    .entry(wkvid.clone())
                    .and_modify(|insts| insts.push(instantiated_e.clone()))
                    .or_insert_with(|| vec![instantiated_e.clone()]);
                if self.keep_wkvars {
                    rty::Expr::and(instantiated_e, e.clone())
                } else {
                    instantiated_e
                }
            }
            // Replace wkvars with true (i.e. eliminate them) if we aren't keeping them
            rty::ExprKind::WKVar(_) if !self.keep_wkvars => rty::Expr::tt(),
            _ => e.super_fold_with(self),
        }
    }
}

struct ProductEtaExpander<'a> {
    // An expression that evalutes to the current_expr
    current_path: rty::Expr,
    // Maps an interior part of the product to its eta expansion.
    expr_to_eta_expansion: &'a mut UnordMap<rty::Expr, rty::Expr>,
}

impl TypeVisitor for ProductEtaExpander<'_> {
    fn visit_expr(&mut self, expr: &rty::Expr) -> ControlFlow<Self::BreakTy> {
        match expr.kind() {
            rty::ExprKind::Tuple(subexprs) | rty::ExprKind::Ctor(_, subexprs) => {
                let current_path = self.current_path.clone();
                let mk_proj = |field| {
                    if let rty::ExprKind::Ctor(ctor, _) = expr.kind() {
                        let def_id = match ctor {
                            rty::Ctor::Struct(def_id) | rty::Ctor::Enum(def_id, _) => *def_id,
                            rty::Ctor::RawPtr => panic!("RawPtr ctor in wkvar path"),
                        };
                        rty::FieldProj::Adt { def_id, field }
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
        expr_to_eta_expansion: &'a mut UnordMap<rty::Expr, rty::Expr>,
    ) {
        let mut expander = ProductEtaExpander { current_path, expr_to_eta_expansion };
        let _ = expr.visit_with(&mut expander);
    }
}
