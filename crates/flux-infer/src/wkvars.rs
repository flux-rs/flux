

use std::{
    collections::{ TypeFoldable, HashMap, hash_map::Entry, },
    ops::ControlFlow,
};
use itertools::Itertools;

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
use rustc_data_structures::{fx::{FxHashSet, FxHashMap}, snapshot_map::SnapshotMap};
use rustc_type_ir::{DebruijnIndex, INNERMOST};

use crate::{
    fixpoint_encoding::{BlameCtxt, FixpointCheckError, FixpointCtxt, KVarGen},
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
    ) -> Option<rty::Binder<rty::Expr>> {
        let mut args_to_param = HashMap::new();
        std::iter::zip(
            wkvar.args.iter().map(|arg| arg.erase_metadata()),
            // We'll make an instantiator that is generic because this instatiation
            // may (and probably will) be used in multiple places
            (0..wkvar.params.len()).into_iter().map(|var_num| rty::Expr::bvar(INNERMOST, var_num.into(), rty::BoundReftKind::Annon)),
        )
        .for_each(|(arg, param)| {
            ProductEtaExpander::eta_expand_products(param, arg, &mut args_to_param);
        });
        let mut instantiator = WKVarInstantiator {
            args_to_param: &args_to_param,
            memo: &mut HashMap::new(),
            // This remains 0 because we use it to track how to shift our params,
            // so the scope is the same.
            current_index: INNERMOST,
        };
        instantiator.try_fold_expr(&expr.erase_metadata()).ok().map(|instantiated_e| {
            rty::Binder::bind_with_sorts(instantiated_e, &std::iter::repeat_n(rty::Sort::Err, wkvar.params.len()).collect_vec())
        })
    }
}

pub struct WKVarSubst {
    pub wkvar_instantiations: HashMap<rty::WKVid, rty::Binder<rty::Expr>>,
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
        let _ = expr.visit_with(&mut expander);
    }
}

#[derive(Clone)]
pub struct WKVarSolutions {
    /// Each Expr is part of a conjunction of the solution.
    pub solutions: HashMap<rty::WKVid, WKVarSolution>,
}

/// NOTE: we expect that the binders for `solved_exprs` and `assumed_exprs` are
/// in the same order, though it is likely (and probable) that the names differ.
/// We at least will check that the number of variables matches.
#[derive(Clone, Default)]
pub struct WKVarSolution {
    /// Exprs we solved using our analysis (in a conjunction)
    pub solved_exprs: Option<rty::Binder<FxHashSet<rty::Expr>>>,
    /// Exprs we assumed (this only happens when we cannot
    /// solve _any_ wkvar --- we'll assume a solution to
    /// try and make everything work), also in a conjunction
    pub assumed_exprs: Option<rty::Binder<FxHashSet<rty::Expr>>>,
    /// Expressions removed from the `solved_exprs`. Given without
    /// a binder because we assume them to be compatible.
    pub removed_solved_exprs: FxHashSet<rty::Expr>,
}

impl WKVarSolution {
    pub fn into_wkvar_subst(&self) -> rty::Binder<rty::Expr> {
        match (&self.solved_exprs, &self.assumed_exprs) {
            (None, Some(assumed_exprs)) => assumed_exprs.map_ref(|exprs| {
                rty::Expr::and_from_iter(exprs.iter().cloned())
            }),
            (Some(solved_exprs), None)  => solved_exprs.map_ref(|exprs| {
                rty::Expr::and_from_iter(exprs.iter().filter(|expr| !self.removed_solved_exprs.contains(expr)).cloned())
            }),
            (None, None)                => unreachable!("Invariant: a solution should have at least one expr"),
            (Some(solved_exprs), Some(assumed_exprs)) => {
                // The best we can do is just check the # of vars matches
                // since we can't reasonably expect the names to be the same
                assert!(solved_exprs.vars().len() == assumed_exprs.vars().len());
                assumed_exprs.map_ref(|assumed_exprs_inner| {
                    // Put all of the solutions into a conjunction
                    rty::Expr::and_from_iter(assumed_exprs_inner.iter().cloned()
                                             .chain(solved_exprs.skip_binder_ref().iter().filter(|expr| !self.removed_solved_exprs.contains(expr)).cloned()))
                })
            }
        }
    }

    fn has_solved_expr(&self, expr: &rty::Expr) -> bool {
        let in_solved_exprs = self.solved_exprs.as_ref().map(|solved_exprs| solved_exprs.skip_binder_ref().contains(&expr.erase_metadata())).unwrap_or(false);
        let in_assumed_exprs = self.assumed_exprs.as_ref().map(|assumed_exprs| assumed_exprs.skip_binder_ref().contains(&expr.erase_metadata())).unwrap_or(false);
        in_solved_exprs || in_assumed_exprs
    }

    fn add_expr(opt_exprs: &mut Option<rty::Binder<FxHashSet<rty::Expr>>>, expr: &rty::Binder<rty::Expr>) -> bool {
        if let Some(exprs) = opt_exprs {
            assert!(exprs.vars() == expr.vars());
            exprs.skip_binder_ref_mut().insert(expr.skip_binder_ref().erase_metadata())
        } else {
            *opt_exprs = Some(expr.map_ref(|inner_expr| {
                let mut set = FxHashSet::default();
                set.insert(inner_expr.erase_metadata());
                set
            }));
            true
        }
    }

    fn add_solved_expr(&mut self, solved_expr: &rty::Binder<rty::Expr>) -> bool {
        if self.removed_solved_exprs.contains(&solved_expr.skip_binder_ref().erase_metadata()) {
            return false;
        }
        Self::add_expr(&mut self.solved_exprs, solved_expr)
    }

    fn add_assumed_expr(&mut self, assumed_expr: &rty::Binder<rty::Expr>) -> bool {
        if self.solved_exprs.as_ref().map(|solved_exprs| solved_exprs.skip_binder_ref().contains(&assumed_expr.skip_binder_ref().erase_metadata())).unwrap_or(false) {
            return false;
        }
        Self::add_expr(&mut self.assumed_exprs, assumed_expr)
    }

    fn remove_solved_expr(&mut self, annotated_solution: &Option<&Vec<rty::Binder<rty::Expr>>>) -> bool {
        if let Some(solved_exprs) = &self.solved_exprs {
            let mut exprs_to_remove = solved_exprs.skip_binder_ref().iter().filter(|solved_expr| {
                // Is the solved_expr in any of the annotated solutions?
                // If so, don't remove it.
                if let Some(annotated_solution) = annotated_solution {
                    !annotated_solution.iter().any(|annotated_expr| {
                        annotated_expr.skip_binder_ref().erase_metadata().kind() == solved_expr.kind()
                    })
                } else {
                    true
                }
            });
            for expr_to_remove in exprs_to_remove {
                // Make sure we haven't added it already
                if self.removed_solved_exprs.insert(expr_to_remove.clone()) {
                    return true;
                }
            }
        }
        false
    }
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
    let mut constraint_lhs_wkvars: FxHashMap<LocalDefId, FxHashSet<rty::WKVid>> = FxHashMap::default();
    let mut constraint_rhs_wkvars: FxHashMap<LocalDefId, FxHashSet<rty::WKVid>> = FxHashMap::default();
    for cstr in &cstrs {
        let id = cstr.def_id.expect_local();
        let (lhs_wkvars, rhs_wkvars) = cstr.refine_tree.wkvars();
        println!("all LHS wkvars for {:?}: {:?}", id, lhs_wkvars.iter().collect_vec());
        println!("all RHS wkvars for {:?}: {:?}", id, rhs_wkvars.iter().collect_vec());
        constraint_rhs_wkvars.insert(id, rhs_wkvars.into_iter().collect());
        constraint_lhs_wkvars.insert(id, lhs_wkvars.into_iter().collect());
    }
    let mut any_wkvar_change = true;
    let mut solutions = WKVarSolutions::new();
    let mut i = 1;
    let mut all_errors = Vec::new();
    while any_wkvar_change && i <= max_iters {
        println!("iteration {} of {}", i, max_iters);
        any_wkvar_change = false;
        all_errors = Vec::new();
        for cstr in &cstrs {
            let mut fcx = FixpointCtxt::new(genv, cstr.def_id, cstr.kvgen.clone());

            let mut wkvar_subst = WKVarSubst {
                wkvar_instantiations: solutions
                    .solutions
                    .iter()
                    .map(|(wkvid, solution)| {
                        (wkvid.clone(), solution.into_wkvar_subst())
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
                // println!("failing constraint {:?}", &error.blame_ctx.expr);
                let solution_candidates = find_solution_candidates(&error.blame_ctx);
                let wkvars = error
                    .blame_ctx
                    .blame_analysis
                    .wkvars
                    // TODO: sort by depth in binder
                    .clone();
                'outer: for wkvar in &wkvars {
                    for solution_candidate in &solution_candidates {
                        // Take the first wkvar solution we can find
                        if let Some(instantiation) = WKVarInstantiator::try_instantiate_wkvar(
                            wkvar,
                            solution_candidate,
                        ) {
                            let ground_truth_solutions = {
                                if let Some(solutions_map) = genv.weak_kvars_for(wkvar.wkvid.0) {
                                    solutions_map.get(&wkvar.wkvid.1.as_u32()).cloned().unwrap_or(vec!())
                                } else {
                                    vec!()
                                }
                            };
                            // println!("Adding an instantiation for wkvar {:?}:", wkvar);
                            // println!("  {:?}", instantiation);
                            let solution = solutions.solutions.entry(wkvar.wkvid).or_default();
                            // HACK: so that we don't waste time running around in circles, we
                            // will not attempt to add a wkvar instantiation if:
                            //   1. All of the ground truth solutions are
                            //      present in the solution.
                            //   2. There is at least 1 ground truth solution OR
                            //      we have removed at least 1 spurious
                            //      solution.  The latter case is to prevent us
                            //      adding and then removing different spurious
                            //      solutions over and over again.
                            if ground_truth_solutions.iter().all(|sol| solution.has_solved_expr(sol.skip_binder_ref()))
                                && (ground_truth_solutions.len() > 0 || solution.removed_solved_exprs.len() > 0) {
                                    continue;
                                }
                            any_wkvar_change = solution.add_solved_expr(&instantiation);
                            if any_wkvar_change {
                                break 'outer;
                            }
                        }
                    }
                }
            }
            let local_id = cstr.def_id.expect_local();
            if !errors.is_empty() {
                all_errors.push((local_id, errors));
            }
        }
        // Early exit if there are no errors to process.
        //
        // Before we would just rely on `any_wkvar_change` and exit if there
        // were no more changes, but now we have logic that will try to reveal
        // wkvars which we should only do if there are no more errors.
        if all_errors.is_empty() {
            break;
        }
        // Our analysis cannot solve _any_ wkvars, so we will try to continue by
        // "revealing" one of the correct solutions.
        //
        // If our analysis cannot solve a wkvar because there are no more
        // errors, this won't change anything (because the errors list will be
        // empty).
        if !any_wkvar_change {
            println!("No changes: trying to add a wkvar solution");
            'outer: for (local_id, errs) in &all_errors {
                for err in errs {
                    for wkvar in &err.blame_ctx.blame_analysis.wkvars {
                        // println!("Trying {:?} for {:?}", wkvar.wkvid, local_id);
                        if let Some(solutions_map) = &genv.weak_kvars_for(wkvar.wkvid.0) {
                            if let Some(sols) = solutions_map.get(&wkvar.wkvid.1.as_u32()) {
                                // println!("There are some solutions, trying them...");
                                for sol in sols {
                                    let current_sol = solutions.solutions.entry(wkvar.wkvid).or_default();
                                    any_wkvar_change = current_sol.add_assumed_expr(sol);
                                    if any_wkvar_change {
                                        println!("assumed solution {:?} for wkvar {:?}", sol, wkvar);
                                        break 'outer;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        // If we can't reveal _any_ wkvar that directly relates to a constraint,
        // we will instead try to reveal a wkvar used in the function itself.
        if !any_wkvar_change {
            println!("Still no changes: trying to add a wkvar solution anywhere in the failing functions");
            'outer: for (local_id, _errs) in &all_errors {
                for wkvid in &constraint_lhs_wkvars[local_id] {
                    // println!("Trying {:?} for {:?}", wkvid, local_id);
                    if let Some(solutions_map) = &genv.weak_kvars_for(wkvid.0) {
                        if let Some(sols) = solutions_map.get(&wkvid.1.as_u32()) {
                            // println!("There are some solutions, trying them...");
                            for sol in sols {
                                let current_sol = solutions.solutions.entry(*wkvid).or_default();
                                any_wkvar_change = current_sol.add_assumed_expr(sol);
                                if any_wkvar_change {
                                    println!("assumed solution {:?} for wkvid {:?}", sol, wkvid);
                                    break 'outer;
                                }
                            }
                        }
                    }
                }
            }
        }
        // If we still haven't gotten any changes, start to remove spurious
        // constraints from the solutions
        if !any_wkvar_change {
            println!("Still no changes: trying to remove wkvar solutions");
            'outer: for (local_id, _errs) in &all_errors {
                for wkvid in &constraint_rhs_wkvars[local_id] {
                    // println!("Trying {:?} for {:?}", wkvid, local_id);
                    if let Some(solution) = solutions.solutions.get_mut(wkvid) {
                        match &genv.weak_kvars_for(wkvid.0) {
                            Some(solutions_map) => {
                                let current_solutions = solutions_map.get(&wkvid.1.as_u32());
                                any_wkvar_change = solution.remove_solved_expr(&current_solutions);
                            }
                            None => {
                                any_wkvar_change = solution.remove_solved_expr(&None);
                            }
                        }
                        if any_wkvar_change {
                            println!("Removed a part of a wkvar solution, continuing...");
                            break 'outer;
                        }
                    }
                }
            }
        }
        i += 1;
    }
    Ok((solutions, all_errors))
}


/// Heuristic and syntactic approach to finding candidates each of whose proof
/// entails the failing constraint (blame_ctx.expr).
///
/// So far this is just the expression itself (trivial entailment) and
/// the equalities arising from antiunifying the expression with an
/// assumed predicate.
///
/// e.g. if the expression is x < y
///
/// assumed_pred: a < y
/// solution candidate: a == x
///
/// assumed_pred: a < b
/// solution candidate: a == x /\ b == y
///
/// assumed_pred: a > b
/// solution candidate: none
/// (it would be --- at the most conservative level taking into account these
///  are booleans --- a > b => x < y which is probably too trivial a constraint
///  to offer; we only equalities anyway)
pub fn find_solution_candidates(blame_ctx: &BlameCtxt) -> Vec<rty::Expr> {
    // println!("Failing constraint: {:?}", &blame_ctx.expr);
    let mut candidates = vec![blame_ctx.expr.clone()];
    for assumed_pred in &blame_ctx.blame_analysis.assumed_preds {
        // println!("Trying to unify against pred {:?}", assumed_pred);
        let au_map = rty::anti_unify(&blame_ctx.expr, assumed_pred);
        // This checks if the antiunification is trivial, i.e.
        // blame_ctx.expr == assumed_pred
        if au_map.get(&blame_ctx.expr).is_some() {
            continue;
        }
        for (e1, e2) in au_map.iter() {
            match (e1.kind(), e2.kind()) {
                // (rty::ExprKind::Constant(..), _) => continue,
                // (_, rty::ExprKind::Constant(..)) => continue,
                // _ => {},
                (rty::ExprKind::Var(..), rty::ExprKind::Var(..)) => {},
                _ => continue,
            }
        }
        // build a conjunction of equalities between each au pair.
        let conjs = au_map.into_iter()
                          .flat_map(|(e1, e2)| {
                              match (e1.kind(), e2.kind()) {
                                  (rty::ExprKind::Constant(..), _) |
                                  (_, rty::ExprKind::Constant(..)) => return None,
                                  _ => {},
                                  // (rty::ExprKind::Var(..), rty::ExprKind::Var(..)) => {},
                                  // _ => return None,
                              }
                              Some(rty::Expr::eq(e1, e2))
                          });
        candidates.push(rty::Expr::and_from_iter(conjs));
    }
    candidates.retain_mut(|expr| {
        expr.simplify(&SnapshotMap::default());
        !(expr.is_trivially_false() || expr.is_trivially_true())
    });
    // for candidate in &candidates {
    //     println!("equality candidate: {:?}", candidate);
    // }
    return candidates;
}
