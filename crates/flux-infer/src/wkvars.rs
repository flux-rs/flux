

use std::{
    collections::{ TypeFoldable, HashMap, HashSet, hash_map::Entry, },
    ops::ControlFlow,
};

use flux_common::cache::QueryCache;
use flux_middle::{
    FixpointQueryKind,
    def_id::MaybeExternId,
    global_env::GlobalEnv,
    queries::QueryResult,
    rty::{
        self,
        fold::{
            FallibleTypeFolder, TypeFoldable, TypeFolder, TypeSuperFoldable, TypeVisitable,
            TypeVisitor,
        },
    },
};
use liquid_fixpoint::SmtSolver;
use rustc_hir::def_id::LocalDefId;
use rustc_type_ir::{DebruijnIndex, INNERMOST};

use crate::{
    fixpoint_encoding::{FixpointCheckError, FixpointCtxt, KVarGen},
    infer::Tag,
    refine_tree::RefineTree,
};

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

pub enum Order {
    /// Replace all occurrences of a wkvar's arg with its respective param
    /// (used for creating a solution that can be put in place of this wkvar)
    Forward,
    /// Replace all occurrences of a wkvar's param with its respective arg
    /// (used for taking an expression that uses the wkvar's original params
    ///  but needs to stand for it in its current location)
    Backward,
}

impl WKVarInstantiator<'_> {
    /// If it succeeds: creates an expression that can replace the weak kvar,
    /// which when used as a refinement will produce the original expr in this
    /// branch after all substitutions have happened.
    ///
    /// FIXME: This does not properly deal with expressions that have bound variables:
    /// if the expression has a bound variable, we might fail the instantiation
    /// when it should succeed.
    pub fn try_instantiate_wkvar(
        wkvar: &rty::WKVar,
        expr: &rty::Expr,
        order: Order,
    ) -> Option<rty::Expr> {
        let mut args_to_param = HashMap::new();
        std::iter::zip(
            wkvar.args.iter().map(|arg| arg.erase_spans()),
            wkvar.params.iter().map(|param| rty::Expr::var(*param)),
        )
        .for_each(|(arg, param)| {
            ProductEtaExpander::eta_expand_products(param, arg, &mut args_to_param);
        });
        match order {
            Order::Backward => {
                args_to_param = args_to_param
                    .into_iter()
                    .map(|(arg, param)| (param, arg))
                    .collect();
            }
            Order::Forward => {}
        }
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
            rty::ExprKind::WKVar(wkvar @ rty::WKVar { wkvid, .. })
                if let Some(subst_e) = self.wkvar_instantiations.get(wkvid) =>
            {
                // HACK: We will map from the params (which should be
                // substituted for in subst_e) to the _actual_ args given to the
                // current wkvar
                //
                // Why? because the params we keep around are the params in the fn_sig
                // but we need to substitute wkvars elsewhere
                let instantiated_e =
                    WKVarInstantiator::try_instantiate_wkvar(&wkvar, &subst_e, Order::Backward)
                        .unwrap_or_else(|| {
                            panic!("Couldn't anti-unfiy {:?} with {:?}", wkvar, subst_e)
                        });
                // NOTE: keeps the original wkvar to allow iterative
                // substitutions --- it gets turned into TRUE when output
                // anyway.
                rty::Expr::and(instantiated_e, e.clone())
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

impl TypeVisitor for ProductEtaExpander<'_> {
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

#[derive(Clone)]
pub struct WKVarSolutions {
    /// Each Expr is part of a conjunction of the solution.
    pub solutions: HashMap<rty::WKVid, HashSet<rty::Expr>>,
}

impl WKVarSolutions {
    pub fn new() -> Self {
        Self { solutions: HashMap::new() }
    }
}

pub struct Constraint {
    pub def_id: MaybeExternId,
    pub refine_tree: RefineTree,
    pub kvgen: KVarGen,
    pub query_kind: FixpointQueryKind,
    pub scrape_quals: bool,
    pub backend: SmtSolver,
}

pub type Constraints = Vec<Constraint>;

pub fn iterative_solve(
    genv: GlobalEnv,
    cstrs: Constraints,
    max_iters: usize,
) -> QueryResult<(WKVarSolutions, Vec<(LocalDefId, Vec<FixpointCheckError<Tag>>)>)> {
    let mut any_solution = true;
    let mut solutions = WKVarSolutions::new();
    let mut i = 1;
    let mut all_errors = Vec::new();
    while any_solution && i <= max_iters {
        println!("iteration {} of {}", i, max_iters);
        any_solution = false;
        all_errors = Vec::new();
        for cstr in &cstrs {
            let mut fcx = FixpointCtxt::new(genv, cstr.def_id, cstr.kvgen.clone());

            let mut wkvar_subst = WKVarSubst {
                wkvar_instantiations: solutions
                    .solutions
                    .iter()
                    .map(|(wkvid, exprs)| {
                        (wkvid.clone(), rty::Expr::and_from_iter(exprs.iter().cloned()))
                    })
                    .collect(),
            };
            // if solutions.solutions.len() > 0 {
            //     println!("{:?}", cstr.refine_tree);
            // }
            let mut solved_refine_tree = cstr.refine_tree.fold_with(&mut wkvar_subst);
            // if solutions.solutions.len() > 0 {
            //     println!("solved\n{:?}", solved_refine_tree);
            // }
            solved_refine_tree.simplify(genv);
            let fcstr = solved_refine_tree.into_fixpoint(&mut fcx)?;
            // println!("converted to fixpoint");
            let errors = fcx.check(
                &mut QueryCache::new(),
                fcstr,
                cstr.query_kind,
                cstr.scrape_quals,
                cstr.backend,
            )?;
            for error in &errors {
                let wkvars = error
                    .blame_ctx
                    .blame_analysis
                    .wkvars
                    // TODO: sort by depth in binder
                    .clone();
                for wkvar in wkvars {
                    // Take the first wkvar solution we can find
                    if let Some(instantiation) = WKVarInstantiator::try_instantiate_wkvar(
                        &wkvar,
                        &error.blame_ctx.expr,
                        Order::Forward,
                    ) {
                        // println!("Adding an instantiation for wkvar {:?}:", wkvar);
                        // println!("  {:?}", instantiation);
                        any_solution = true;
                        match solutions.solutions.entry(wkvar.wkvid) {
                            Entry::Occupied(mut entry) => {
                                entry.get_mut().insert(instantiation);
                            }
                            Entry::Vacant(entry) => {
                                entry.insert([instantiation].into());
                            }
                        }
                        break;
                    }
                }
            }
            if let Some(local_id) = cstr.def_id.as_local() {
                all_errors.push((local_id, errors));
            }
        }
        i += 1;
    }
    Ok((solutions, all_errors))
}
