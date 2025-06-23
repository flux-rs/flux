

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
use rustc_data_structures::{fx::FxHashSet, snapshot_map::SnapshotMap};
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
            wkvar.args.iter().map(|arg| arg.erase_spans()),
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
        instantiator.try_fold_expr(&expr.erase_spans()).ok().map(|instantiated_e| {
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
    pub solutions: HashMap<rty::WKVid, rty::Binder<FxHashSet<rty::Expr>>>,
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
                    .map(|(wkvid, exprs_binder)| {
                        (wkvid.clone(), exprs_binder.map_ref(|bound_es| rty::Expr::and_from_iter(bound_es.iter().cloned())))
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
                println!("failing constraint {:?}", &error.blame_ctx.expr);
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
                            println!("Adding an instantiation for wkvar {:?}:", wkvar);
                            println!("  {:?}", instantiation);
                            any_solution = true;
                            match solutions.solutions.entry(wkvar.wkvid) {
                                Entry::Occupied(mut entry) => {
                                    assert!(entry.get().vars() == instantiation.vars());
                                    entry.get_mut().skip_binder_ref_mut().insert(instantiation.skip_binder());
                                }
                                Entry::Vacant(entry) => {
                                    entry.insert(instantiation.map(|bound_e| {
                                        let mut set = FxHashSet::default();
                                        set.insert(bound_e);
                                        set
                                    }));
                                }
                            }
                            break 'outer;
                        }
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
    println!("Failing constraint: {:?}", &blame_ctx.expr);
    let mut candidates = vec![blame_ctx.expr.clone()];
    for assumed_pred in &blame_ctx.blame_analysis.assumed_preds {
        println!("Trying to unify against pred {:?}", assumed_pred);
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
    for candidate in &candidates {
        println!("equality candidate: {:?}", candidate);
    }
    return candidates;
}
