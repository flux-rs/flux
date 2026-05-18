use std::{collections::{HashMap, HashSet}, iter};

use itertools::Itertools;

use crate::{
    Assignments, BinRel, Identifier, Types,
    constraint::{Bind, Constant, Constraint, Expr, Pred, Qualifier},
    constraint_fragments::ConstraintFragments,
    graph::{FxIndexMap, FxIndexSet, topological_sort_sccs},
};

pub struct Solution<T: Types> {
    pub binders: Vec<Bind<T>>,
    pub args: Vec<Expr<T>>,
}

impl<T: Types> Constraint<T> {
    // fn contains_kvars(&self) -> bool {
    //     match self {
    //         Constraint::Conj(cs) => cs.iter().any(Constraint::contains_kvars),
    //         Constraint::ForAll(_bind, inner) => inner.contains_kvars(),
    //         Constraint::Pred(p, _tag) => p.contains_kvars(),
    //     }
    // }

    pub fn depth_first_fragments(&self) -> ConstraintFragments<'_, T> {
        ConstraintFragments::new(self)
    }

    /// Computes a map from each KVar to the minimum fragment index (DFS order)
    /// at which that KVar appears as an LHS/assumption kvar.  The `n_max`
    /// argument is used as the default rank for KVars that never appear in any
    /// LHS (they are effectively "infinity", i.e., never seen as assumptions).
    ///
    /// This mirrors the Haskell `edgeRank` in `Graph/Deps.hs`, which assigns
    /// each KVar the smallest sub-constraint ID where it appears on the LHS.
    pub(crate) fn kvar_ranks(&self, n_max: usize) -> FxIndexMap<T::KVar, usize> {
        let mut rank: FxIndexMap<T::KVar, usize> = FxIndexMap::default();
        for (i, frag) in self.depth_first_fragments().enumerate() {
            for k in frag.kvar_deps() {
                let r = rank.entry(k).or_insert(n_max);
                if i < *r {
                    *r = i;
                }
            }
        }
        rank
    }

    pub fn kvar_deps(&self) -> Vec<T::KVar> {
        match self {
            Constraint::Conj(_) => panic!("Conjunctions should not occur in fragments"),
            Constraint::ForAll(bind, inner) => {
                let mut dependencies = bind.pred.kvars();
                dependencies.extend_from_slice(&inner.kvar_deps());
                dependencies
            }
            Constraint::Pred(_, _) => vec![],
        }
    }

    pub(crate) fn kvar_mappings(&self) -> FxIndexMap<T::KVar, Vec<Constraint<T>>> {
        let mut kvar_to_fragments: FxIndexMap<T::KVar, Vec<Constraint<T>>> = FxIndexMap::default();
        for frag in self.depth_first_fragments() {
            if let Some(kvar) = frag.fragment_kvar_head() {
                kvar_to_fragments
                    .entry(kvar.clone())
                    .or_insert_with(Vec::new)
                    .push(frag);
            }
        }
        kvar_to_fragments
    }

    /// Computes the kvar dependency graph as an adjacency list.
    ///
    /// There's an edge $k0 -> $k1, if $k1 appears as an assumption when $k0 is a head.
    pub(crate) fn kvar_dep_graph(&self) -> FxIndexMap<T::KVar, Vec<T::KVar>> {
        fn go<T: Types>(
            cstr: &Constraint<T>,
            deps: &mut Vec<T::KVar>,
            graph: &mut FxIndexMap<T::KVar, Vec<T::KVar>>,
        ) {
            match cstr {
                Constraint::Pred(pred, _) => {
                    for kvar in pred.kvars() {
                        graph
                            .entry(kvar.clone())
                            .or_default()
                            .extend(deps.iter().cloned());
                    }
                }
                Constraint::Conj(cstrs) => {
                    for cstr in cstrs {
                        let n = deps.len();
                        go(cstr, deps, graph);
                        deps.truncate(n);
                    }
                }
                Constraint::ForAll(bind, cstr) => {
                    // Register assumption kvars as graph nodes with *empty* deps.
                    // Without this, assumption-only kvars (kvars that never appear as
                    // heads) would not be keys in the graph and would never be found by
                    // the acyclic-peeling loop in `eliminate_acyclic_kvars`.
                    //
                    // We must NOT inherit outer `deps` here: assumption kvars don't
                    // depend on the kvars in surrounding ForAll binders.  Their deps
                    // (if any) come only from when they appear as heads elsewhere in
                    // the constraint, which is handled by the `Constraint::Pred` arm.
                    for kvar in bind.pred.kvars() {
                        graph.entry(kvar.clone()).or_default();
                    }
                    deps.extend(bind.pred.kvars());
                    go(cstr, deps, graph);
                }
            }
        }
        let mut graph = Default::default();
        go(self, &mut vec![], &mut graph);
        graph
            .into_iter()
            .map(|(kvid, deps)| (kvid, deps.into_iter().dedup().collect()))
            .collect()
    }

    pub(crate) fn topo_order_fragments(&self) -> Vec<Self> {
        let dep_graph = self.kvar_dep_graph();
        let mut kvar_to_fragments = self.kvar_mappings();
        let topologically_ordered_kvids = topological_sort_sccs(&dep_graph);
        topologically_ordered_kvids
            .into_iter()
            .rev()
            .flatten()
            .flat_map(|kvid| kvar_to_fragments.remove(&kvid).unwrap())
            .collect()
    }

    pub fn fragment_kvar_head(&self) -> Option<T::KVar> {
        match self {
            Constraint::ForAll(_bind, inner) => inner.fragment_kvar_head(),
            Constraint::Pred(Pred::Expr(_expr), _tag) => None,
            Constraint::Pred(Pred::KVar(name, _args), _tag) => Some(name.clone()),
            _ => panic!("Conjunctions should not occur in fragments"),
        }
    }

    pub fn sub_all_kvars(&self, assignments: &Assignments<'_, T>) -> Self {
        match self {
            Constraint::ForAll(bind, inner) => {
                Constraint::ForAll(
                    Bind {
                        name: bind.name.clone(),
                        sort: bind.sort.clone(),
                        pred: bind.pred.sub_kvars(assignments),
                    },
                    Box::new(inner.sub_all_kvars(assignments)),
                )
            }
            Constraint::Pred(pred, tag) => {
                Constraint::Pred(pred.sub_kvars(assignments), tag.clone())
            }
            Constraint::Conj(conjuncts) => {
                Constraint::Conj(
                    conjuncts
                        .iter()
                        .map(|cstr| cstr.sub_all_kvars(assignments))
                        .collect(),
                )
            }
        }
    }

    pub fn sub_kvars_except_head(&self, assignments: &Assignments<'_, T>) -> Self {
        match self {
            Constraint::ForAll(bind, inner) => {
                Constraint::ForAll(
                    Bind {
                        name: bind.name.clone(),
                        sort: bind.sort.clone(),
                        pred: bind.pred.sub_kvars(assignments),
                    },
                    Box::new(inner.sub_kvars_except_head(assignments)),
                )
            }
            Constraint::Pred(pred, tag) => Constraint::Pred(pred.clone(), tag.clone()),
            _ => panic!("Conjunctions should not occur in constraint fragments"),
        }
    }

    pub fn sub_head(&self, assignment: &(&Qualifier<T>, Vec<usize>)) -> Self {
        match self {
            Constraint::ForAll(bind, inner) => {
                Constraint::ForAll(bind.clone(), Box::new(inner.sub_head(assignment)))
            }
            Constraint::Pred(pred, tag) => Constraint::Pred(pred.sub_head(assignment), tag.clone()),
            _ => panic!("Conjunctions should not occur in constraint fragments"),
        }
    }

    /// Compute the set of non-cut KVars using the SCC+rank algorithm that mirrors
    /// the Haskell fixpoint `elimVars`/`sccElims`/`edgeRankCut` logic in
    /// `Language.Fixpoint.Graph.Deps`.
    pub fn compute_non_cuts(&self) -> Vec<T::KVar> {
        let n_max = self.depth_first_fragments().count();
        let rank = self.kvar_ranks(n_max);
        let dep_graph = self.kvar_dep_graph();
        let sccs = topological_sort_sccs(&dep_graph);

        let mut non_cuts: Vec<T::KVar> = Vec::new();
        for scc in sccs {
            scc_dep::<T>(&scc, &dep_graph, &rank, n_max, &mut non_cuts);
        }
        non_cuts
    }

    /// Substitute all non-cut KVars with their solutions and return the resulting
    /// constraint. Non-cut KVars are those identified by the SCC+rank algorithm.
    pub fn elim_non_cut_kvars(&mut self, fresh: &mut dyn FnMut() -> T::Var) -> Self {
        self.simplify();
        let non_cuts = self.compute_non_cuts();
        let mut non_cuts = non_cuts;
        non_cuts.sort_by_key(|k| k.display().to_string());
        if std::env::var("FLUX_DEBUG_NONCUT").is_ok() {
            eprintln!("[noncut] vars={non_cuts:?}\n[noncut] before={:#?}", self);
        }
        let out = self.elim(&non_cuts, fresh);
        if std::env::var("FLUX_DEBUG_NONCUT").is_ok() {
            eprintln!("[noncut] after={:#?}", out);
        }
        out
    }

    pub fn non_cut_solution_strings(&self) -> Vec<(T::KVar, Vec<String>)> {
        self.compute_non_cuts()
            .into_iter()
            .map(|var| {
                let scope = self.kvar_scope(&var);
                let sols: Vec<String> = self
                    .sol1(&var)
                    .into_iter()
                    .map(|sol| self.fmt_cube_pred(&sol, &scope))
                    .collect();
                if std::env::var("FLUX_DEBUG_NONCUT").is_ok() {
                    eprintln!("[noncut-scope] var={var:?} scope={scope:?} sol_count={}", sols.len());
                }
                (var, sols)
            })
            .collect()
    }

    fn scope(&self, var: &T::KVar) -> Self {
        self.scope_help(var)
            .unwrap_or(Constraint::Pred(Pred::Expr(Expr::Constant(Constant::Boolean(true))), None))
    }

    fn scope_help(&self, var: &T::KVar) -> Option<Constraint<T>> {
        match self {
            Constraint::ForAll(bind, inner) => {
                if bind.pred.kvars().contains(var) {
                    Some(self.clone())
                } else {
                    inner.scope_help(var)
                }
            }
            Constraint::Pred(Pred::KVar(kvid, _args), _tag) if var.eq(kvid) => Some(self.clone()),
            Constraint::Pred(_, _) => None,
            Constraint::Conj(conjuncts) => {
                match conjuncts
                    .iter()
                    .filter_map(|inner| inner.scope_help(var))
                    .collect_vec()
                    .as_slice()
                {
                    [] => None,
                    [cstr] => Some(cstr.clone()),
                    _ => Some(self.clone()),
                }
            }
        }
    }

    fn sol1(&self, var: &T::KVar) -> Vec<Solution<T>> {
        match self {
            Constraint::ForAll(bind, inner) => {
                inner
                    .sol1(var)
                    .into_iter()
                    .map(|Solution { mut binders, args }| {
                        binders.insert(0, bind.clone());
                        Solution { binders, args }
                    })
                    .collect()
            }
            Constraint::Conj(conjuncts) => conjuncts.iter().flat_map(|cstr| cstr.sol1(var)).collect(),
            Constraint::Pred(pred, _) => pred.sol1(var),
        }
    }

    pub fn elim(&self, vars: &[T::KVar], fresh: &mut dyn FnMut() -> T::Var) -> Self {
        vars.iter().fold(self.clone(), |mut acc, var| {
            acc = acc.elim1_v2(var, fresh);
            acc.simplify();
            acc
        })
    }

    pub fn free_vars_report(&self) -> Vec<T::Var> {
        let mut free_vars = HashSet::new();
        self.free_vars_report_help(&HashSet::new(), &mut free_vars);
        free_vars.into_iter().collect_vec()
    }

    fn free_vars_report_help(&self, bound: &HashSet<T::Var>, free_vars: &mut HashSet<T::Var>) {
        match self {
            Constraint::Conj(conjuncts) => {
                for conjunct in conjuncts {
                    conjunct.free_vars_report_help(bound, free_vars);
                }
            }
            Constraint::ForAll(Bind { name, pred, .. }, inner) => {
                free_vars.extend(pred.free_vars().into_iter().filter(|v| !bound.contains(v)));

                let mut new_bound = bound.clone();
                new_bound.insert(name.clone());
                inner.free_vars_report_help(&new_bound, free_vars);
            }
            Constraint::Pred(pred, _) => {
                free_vars.extend(pred.free_vars().into_iter().filter(|v| !bound.contains(v)));
            }
        }
    }

    pub fn assert_no_free_vars(&self, context: &str) {
        let free_vars = self.free_vars_report();
        if !free_vars.is_empty() {
            panic!("{context}: found unbound vars: {free_vars:?}\n{self:#?}");
        }
    }

    fn elim1(&self, var: &T::KVar) -> Self {
        // Call sol1 on scope(var) — the LCA subtree — so that the collected
        // binders are exactly those that are "extra" (below the LCA), matching
        // Haskell's `elim1 c k = simplify $ doelim k (sol1 k (scope k c)) c`.
        let scoped = self.scope(var);
        let solution = scoped.sol1(var);
        if std::env::var("FLUX_DEBUG_NONCUT").is_ok() {
            eprintln!("[noncut] elim var={var:?} solution_count={}", solution.len());
            for (i, sol) in solution.iter().enumerate() {
                eprintln!("[noncut] solution[{i}] binders={} args={:?}", sol.binders.len(), sol.args);
            }
        }
        self.do_elim(var, &solution)
    }

    fn fmt_cube_pred(&self, sol: &Solution<T>, scope: &HashSet<T::Var>) -> String {
        let extra_binders: Vec<_> = sol.binders.iter().filter(|b| !scope.contains(&b.name)).collect();
        let equalities: Vec<String> = sol
            .args
            .iter()
            .enumerate()
            .map(|(i, arg)| format!("v{i}={arg:?}"))
            .collect();
        let binder_preds: Vec<String> = extra_binders
            .iter()
            .filter(|b| !matches!(b.pred, Pred::KVar(_, _)))
            .map(|b| format!("{:?}", b.pred))
            .collect();
        let body = equalities
            .iter()
            .map(|s| s.as_str())
            .chain(binder_preds.iter().map(|s| s.as_str()))
            .join(" /\\ ");
        if extra_binders.is_empty() {
            body
        } else {
            let qvars: Vec<_> = extra_binders
                .iter()
                .map(|b| format!("{:?}:{:?}", b.name, b.sort))
                .collect();
            format!("∃ {}. {}", qvars.join(", "), body)
        }
    }

    fn fmt_solution(&self, sol: &Solution<T>) -> String {
        let binders = sol
            .binders
            .iter()
            .map(|b| format!("({:?} {:?} {:?})", b.name, b.sort, b.pred))
            .collect::<Vec<_>>()
            .join(", ");
        let args = sol
            .args
            .iter()
            .map(|a| format!("{:?}", a))
            .collect::<Vec<_>>()
            .join(", ");
        format!("binders=[{binders}] args=[{args}]")
    }

    /// Computes `sScp[k]`: the intersection of all binders that are universally in scope
    /// at every occurrence (guard or head) of `var` in this constraint.
    /// Mirrors Haskell's `kvScopes` / `sScp` in `Language.Fixpoint.Solver.Eliminate`.
    fn kvar_scope(&self, var: &T::KVar) -> HashSet<T::Var> {
        let mut paths: Vec<HashSet<T::Var>> = Vec::new();
        collect_occurrence_binders(self, var, &HashSet::new(), &mut paths);
        if paths.is_empty() {
            return HashSet::new();
        }
        let mut scope = paths.swap_remove(0);
        for path in paths {
            scope.retain(|x| path.contains(x));
        }
        scope
    }

    /// FUSION-style elimination of a single non-cut kvar `var`.
    ///
    /// Mirrors `Solver/Solution.hs::cubePred`/`hypPred`: for each occurrence of
    /// `var` at a head position we collect a *cube* (chain of enclosing ForAll
    /// binders + formal args). At each *use* site `KVar(var, actuals)`, we
    /// substitute `Pred::Hyp` of those cubes (existentially quantifying each
    /// cube's "extra" binders — those not in `sScp[var]` — and adding
    /// `formal_i = actual_i` equalities). Head occurrences of `var` themselves
    /// become `Pred::TRUE` (the obligation is discharged by the substitution
    /// at use sites).
    ///
    /// Unlike the Horn-syntactic `doelim`, this does NOT change the constraint
    /// structure: no new outer ForAlls, no Conj-of-cubes. Cube bodies preserve
    /// `Pred` shape so any cut-kvar references inside extra binders' preds are
    /// kept verbatim for fixpoint to resolve later.
    fn elim1_v2(&self, var: &T::KVar, fresh: &mut dyn FnMut() -> T::Var) -> Self {
        let scope = self.kvar_scope(var);
        let mut cubes: Vec<CollectedCube<T>> = Vec::new();
        collect_cubes(self, var, &mut Vec::new(), &mut cubes);
        if std::env::var("FLUX_DEBUG_NONCUT").is_ok() {
            eprintln!("[noncut-v2] ENTER elim1_v2 var={var:?}");
            eprintln!(
                "[noncut-v2] elim {:?}: {} cubes; scope size {}",
                var,
                cubes.len(),
                scope.len()
            );
            for (i, c) in cubes.iter().enumerate() {
                eprintln!(
                    "[noncut-v2]   cube[{i}] binders={} formals={:?}",
                    c.binders.len(),
                    c.formals
                );
                for (j, b) in c.binders.iter().enumerate() {
                    eprintln!("[noncut-v2]     binder[{j}] name={:?} pred={:?}", b.name, b.pred);
                }
            }
        }
        self.substitute_kvar_uses(var, &cubes, &scope, fresh)
    }

    fn substitute_kvar_uses(
        &self,
        var: &T::KVar,
        cubes: &[CollectedCube<T>],
        scope: &HashSet<T::Var>,
        fresh: &mut dyn FnMut() -> T::Var,
    ) -> Self {
        match self {
            Constraint::Conj(cs) => {
                Constraint::Conj(
                    cs.iter()
                        .map(|c| c.substitute_kvar_uses(var, cubes, scope, fresh))
                        .collect(),
                )
            }
            Constraint::ForAll(Bind { name, sort, pred }, inner) => {
                let new_pred = pred.substitute_kvar_use(var, cubes, scope, fresh);
                Constraint::ForAll(
                    Bind { name: name.clone(), sort: sort.clone(), pred: new_pred },
                    Box::new(inner.substitute_kvar_uses(var, cubes, scope, fresh)),
                )
            }
            Constraint::Pred(pred, tag) => {
                let new_pred = pred.substitute_kvar_head(var);
                Constraint::Pred(new_pred, tag.clone())
            }
        }
    }

    fn pred_to_expr(pred: &Pred<T>) -> Option<Expr<T>> {
        match pred {
            Pred::Expr(expr) => Some(expr.clone()),
            Pred::And(preds) => preds
                .iter()
                .map(Self::pred_to_expr)
                .collect::<Option<Vec<_>>>()
                .map(Expr::and),
            Pred::KVar(_, _) => None,
            Pred::Hyp(_) => None,
        }
    }

    fn do_elim(&self, var: &T::KVar, solution: &[Solution<T>]) -> Self {
        match self {
            Constraint::Conj(conjuncts) => {
                Constraint::Conj(
                    conjuncts
                        .iter()
                        .map(|cstr| cstr.do_elim(var, solution))
                        .collect(),
                )
            }
            Constraint::ForAll(Bind { name, sort, pred }, inner) => {
                let inner_elimmed = inner.do_elim(var, solution);
                match pred.find_kvar_in_guard(var) {
                    Ok(_) => Constraint::ForAll(
                        Bind { name: name.clone(), sort: sort.clone(), pred: pred.clone() },
                        Box::new(inner_elimmed),
                    ),
                    Err((kvar_instances, preds)) => {
                        // Mirrors Haskell's `demorgan`/`cubeSol`:
                        //
                        //   cubeSol (b:bs, eqs) = All b $ cubeSol (bs, eqs)
                        //   cubeSol ([], eqs)   = All (Bind x t (PAnd (subst su eqs ++ subst su preds))) cstr'
                        //
                        // Extra binders (those not in scope) become nested ForAll wrappers
                        // *outside* the guard binder, not existentials inside the predicate.
                        // When there are multiple cubes they are conjoined (CAnd), not disjuncted.
                        let cube_cstrs: Vec<Constraint<T>> = solution
                            .iter()
                            .map(|Solution { binders, args }| {
                                // Build the guard predicate for the original binder:
                                // equality constraints (guard_arg == sol_arg) plus the remaining
                                // non-kvar predicates from the guard.
                                let mut guard_preds = preds.clone();
                                guard_preds.extend(kvar_instances.iter().flat_map(|(_, eqs)| {
                                    iter::zip(args, eqs).map(|(arg, eq)| {
                                        Pred::Expr(Expr::Atom(
                                            BinRel::Eq,
                                            Box::new([eq.clone(), arg.clone()]),
                                        ))
                                    })
                                }));
                                // The innermost constraint: the original binder with the new guard.
                                let innermost = Constraint::ForAll(
                                    Bind {
                                        name: name.clone(),
                                        sort: sort.clone(),
                                        pred: Pred::and(guard_preds),
                                    },
                                    Box::new(inner_elimmed.clone()),
                                );
                                // Wrap ALL binders from the solution as outer ForAll quantifiers,
                                // matching Haskell's `cubeSol (b:bs, eqs) = All b $ cubeSol (bs, eqs)`.
                                // Because sol1 was called on `scope(var)` (the LCA subtree), the
                                // binders here are exactly those that are "extra" (below the LCA).
                                // KVar binder preds are treated as True (we do not have cut-kvar
                                // solutions on the Rust side).
                                binders.iter().rev().fold(innermost, |acc, binder| {
                                    let guard = if matches!(binder.pred, Pred::KVar(_, _)) {
                                        Pred::TRUE
                                    } else {
                                        binder.pred.clone()
                                    };
                                    Constraint::ForAll(
                                        Bind {
                                            name: binder.name.clone(),
                                            sort: binder.sort.clone(),
                                            pred: guard,
                                        },
                                        Box::new(acc),
                                    )
                                })
                            })
                            .collect();
                        match cube_cstrs.len() {
                            0 => Constraint::ForAll(
                                Bind { name: name.clone(), sort: sort.clone(), pred: Pred::TRUE },
                                Box::new(inner_elimmed),
                            ),
                            1 => cube_cstrs.into_iter().next().unwrap(),
                            _ => Constraint::conj(cube_cstrs),
                        }
                    }
                }
            }
            Constraint::Pred(Pred::KVar(kvid, _args), tag) if var.eq(kvid) => {
                Constraint::Pred(Pred::TRUE, tag.clone())
            }
            cpred => cpred.clone(),
        }
    }
}

/// Collects, for each occurrence (guard or head) of `var` in `cstr`,
/// the set of ForAll binder names that are in scope at that occurrence.
/// Used by `Constraint::kvar_scope` to compute the intersection (sScp[k]).
fn collect_occurrence_binders<T: Types>(
    cstr: &Constraint<T>,
    var: &T::KVar,
    outer: &HashSet<T::Var>,
    paths: &mut Vec<HashSet<T::Var>>,
) {
    match cstr {
        Constraint::ForAll(bind, inner) => {
            if bind.pred.kvars().contains(var) {
                // Guard occurrence: the binders in scope are those *above* this ForAll.
                paths.push(outer.clone());
            }
            let mut new_outer = outer.clone();
            // Skip anonymous binders (e.g. Flux's `Var::Underscore`): their names
            // collide across distinct binders, so adding them to the scope set would
            // over-collapse the kvar's common scope and incorrectly drop binders
            // from cube extras.
            if !bind.name.is_anonymous() {
                new_outer.insert(bind.name.clone());
            }
            collect_occurrence_binders(inner, var, &new_outer, paths);
        }
        Constraint::Conj(conjuncts) => {
            for c in conjuncts {
                collect_occurrence_binders(c, var, outer, paths);
            }
        }
        Constraint::Pred(pred, _) => {
            if pred.kvars().contains(var) {
                // Head occurrence.
                paths.push(outer.clone());
            }
        }
    }
}

/// Recursively apply the SCC+rank cut-selection algorithm (mirrors Haskell's
/// `sccElims`/`edgeRankCut` in `Language.Fixpoint.Graph.Deps`).
fn scc_dep<T: Types>(
    scc: &[T::KVar],
    dep_graph: &FxIndexMap<T::KVar, Vec<T::KVar>>,
    rank: &FxIndexMap<T::KVar, usize>,
    n_max: usize,
    non_cuts: &mut Vec<T::KVar>,
) {
    match scc {
        [] => {}
        [k] => {
            let has_self_loop = dep_graph.get(k).map_or(false, |deps| deps.contains(k));
            if !has_self_loop {
                non_cuts.push(k.clone());
            }
        }
        _ => {
            let cut = scc
                .iter()
                .min_by_key(|k| rank.get(*k).copied().unwrap_or(n_max))
                .unwrap()
                .clone();

            let remaining: FxIndexSet<T::KVar> =
                scc.iter().filter(|k| **k != cut).cloned().collect();

            let sub_graph: FxIndexMap<T::KVar, Vec<T::KVar>> = remaining
                .iter()
                .map(|k| {
                    let deps = dep_graph.get(k).map_or(vec![], |d| {
                        d.iter().filter(|dep| remaining.contains(*dep)).cloned().collect()
                    });
                    (k.clone(), deps)
                })
                .collect();

            for sub_scc in topological_sort_sccs(&sub_graph) {
                scc_dep::<T>(&sub_scc, &sub_graph, rank, n_max, non_cuts);
            }
        }
    }
}

impl<T: Types> Pred<T> {
    pub fn contains_kvars(&self) -> bool {
        match self {
            Pred::And(ps) => ps.iter().any(Pred::contains_kvars),
            Pred::KVar(_, _) => true,
            Pred::Expr(_) => false,
            // A Hyp's body may contain residual cut-kvar references.
            Pred::Hyp(cubes) => cubes.iter().any(|c| c.body.contains_kvars()),
        }
    }

    fn free_vars(&self) -> HashSet<T::Var> {
        match self {
            Pred::And(ps) => ps.iter().flat_map(Pred::free_vars).collect(),
            Pred::KVar(_, _) => HashSet::new(),
            Pred::Expr(expr) => expr.free_vars().into_iter().collect(),
            Pred::Hyp(cubes) => {
                let mut out = HashSet::new();
                for c in cubes {
                    let mut body_free = c.body.free_vars();
                    for b in &c.extra_binders {
                        body_free.remove(&b.name);
                    }
                    out.extend(body_free);
                }
                out
            }
        }
    }

    fn kvars(&self) -> Vec<T::KVar> {
        match self {
            Pred::KVar(kvid, _args) => vec![kvid.clone()],
            Pred::Expr(_expr) => vec![],
            Pred::And(conjuncts) => conjuncts.iter().flat_map(Pred::kvars).unique().collect(),
            Pred::Hyp(cubes) => cubes.iter().flat_map(|c| c.body.kvars()).unique().collect(),
        }
    }

    fn scope_help(&self, var: &T::KVar) -> Option<Self> {
        match self {
            Pred::And(conjuncts) => match conjuncts
                .iter()
                .filter_map(|inner| inner.scope_help(var))
                .collect_vec()
                .as_slice()
            {
                [] => None,
                [p] => Some(p.clone()),
                _ => Some(Pred::and(conjuncts.clone())),
            },
            Pred::KVar(kvid, _args) if var.eq(kvid) => Some(self.clone()),
            Pred::KVar(_, _) => None,
            Pred::Expr(_) => None,
            // A Hyp does not contain references to the *non-cut* kvar being
            // scoped (it has already been eliminated). Any kvars inside a Hyp
            // body are cut kvars whose scope we don't compute here.
            Pred::Hyp(_) => None,
        }
    }

    fn sol1(&self, var: &T::KVar) -> Vec<Solution<T>> {
        match self {
            Pred::And(conjuncts) => conjuncts.iter().flat_map(|p| p.sol1(var)).collect(),
            Pred::KVar(kvid, args) if var.eq(kvid) => {
                vec![Solution { binders: vec![], args: args.clone() }]
            }
            Pred::Expr(_) => vec![],
            Pred::KVar(_, _) => vec![],
            // Hyps don't contribute new sol1 entries for the same non-cut kvar.
            Pred::Hyp(_) => vec![],
        }
    }

    pub(crate) fn sub_kvars(&self, assignment: &Assignments<'_, T>) -> Self {
        match self {
            Pred::KVar(kvid, args) => {
                let qualifiers = assignment
                    .get(kvid)
                    .unwrap_or_else(|| panic!("{:#?} should have an assignment", kvid));
                Pred::and(
                    qualifiers
                        .iter()
                        .map(|qualifier| {
                            Pred::Expr(
                                qualifier
                                    .0
                                    .args
                                    .iter()
                                    .map(|arg| &arg.0)
                                    .zip(qualifier.1.iter().map(|arg_idx| &args[*arg_idx]))
                                    .fold(qualifier.0.body.clone(), |acc, e| {
                                        acc.substitute(e.0, e.1)
                                    }),
                            )
                        })
                        .collect(),
                )
            }
            Pred::Expr(expr) => Pred::Expr(expr.clone()),
            Pred::And(conjuncts) => {
                Pred::And(
                    conjuncts
                        .clone()
                        .into_iter()
                        .map(|pred| pred.sub_kvars(assignment))
                        .collect(),
                )
            }
            Pred::Hyp(cubes) => {
                Pred::Hyp(
                    cubes
                        .iter()
                        .map(|c| crate::constraint::Cube {
                            extra_binders: c.extra_binders.clone(),
                            body: Box::new(c.body.sub_kvars(assignment)),
                        })
                        .collect(),
                )
            }
        }
    }

    pub(crate) fn sub_head(&self, assignment: &(&Qualifier<T>, Vec<usize>)) -> Self {
        match self {
            Pred::Expr(expr) => Pred::Expr(expr.clone()),
            Pred::KVar(_kvid, args) => {
                Pred::Expr(
                    assignment
                        .0
                        .args
                        .iter()
                        .map(|arg| &arg.0)
                        .zip(assignment.1.iter().map(|arg_idx| &args[*arg_idx]))
                        .fold(assignment.0.body.clone(), |acc, e| acc.substitute(e.0, e.1)),
                )
            }
            _ => panic!("Conjunctions/Hyps should not occur as a constraint head when sub_head is called"),
        }
    }

    #[allow(clippy::type_complexity)]
    pub fn partition_pred(&self, var: &T::KVar) -> (Vec<(T::KVar, Vec<Expr<T>>)>, Vec<Pred<T>>) {
        let mut kvar_instances = vec![];
        let mut other_preds = vec![];
        self.partition_pred_help(var, &mut kvar_instances, &mut other_preds);
        (kvar_instances, other_preds)
    }

    fn find_kvar_in_guard(
        &self,
        var: &T::KVar,
    ) -> Result<Pred<T>, (Vec<(T::KVar, Vec<Expr<T>>)>, Vec<Pred<T>>)> {
        match self {
            Pred::And(conjuncts) => {
                let mut lefts = vec![];
                let mut rights = vec![];
                for pred in conjuncts {
                    match pred.find_kvar_in_guard(var) {
                        Ok(p) => rights.push(p),
                        Err((kvars, preds)) => {
                            lefts.extend(kvars);
                            rights.extend(preds);
                        }
                    }
                }
                if lefts.is_empty() {
                    Ok(Pred::and(rights))
                } else {
                    Err((lefts, rights))
                }
            }
            Pred::KVar(kvid, args) if var.eq(kvid) => Err((vec![(kvid.clone(), args.clone())], vec![])),
            _ => Ok(self.clone()),
        }
    }

    fn partition_pred_help(
        &self,
        var: &T::KVar,
        kvar_instances: &mut Vec<(T::KVar, Vec<Expr<T>>)>,
        other_preds: &mut Vec<Pred<T>>,
    ) {
        match self {
            Pred::And(conjuncts) => {
                conjuncts
                    .iter()
                    .for_each(|pred| pred.partition_pred_help(var, kvar_instances, other_preds));
            }
            Pred::KVar(kvid, args) if var.eq(kvid) => {
                kvar_instances.push((kvid.clone(), args.clone()));
            }
            _ => {
                other_preds.push(self.clone());
            }
        }
    }
}

impl<T: Types> Expr<T> {
    fn substitute_in_place(&mut self, v_from: &T::Var, v_to: &Expr<T>) {
        match self {
            Expr::Var(v) => {
                if v == v_from {
                    *self = v_to.clone();
                }
            }
            Expr::Iff(exprs)
            | Expr::Imp(exprs)
            | Expr::BinaryOp(_, exprs)
            | Expr::Atom(_, exprs) => {
                let [e1, e2] = &mut **exprs;
                e1.substitute_in_place(v_from, v_to);
                e2.substitute_in_place(v_from, v_to);
            }
            Expr::Let(_, exprs) => {
                // We are assuming there's no shadowing here.
                let [e1, e2] = &mut **exprs;
                e1.substitute_in_place(v_from, v_to);
                e2.substitute_in_place(v_from, v_to);
            }
            Expr::And(exprs) | Expr::Or(exprs) => {
                exprs
                    .iter_mut()
                    .for_each(|expr| expr.substitute_in_place(v_from, v_to));
            }
            Expr::App(func, _sort_args, args, _out_sort) => {
                func.substitute_in_place(v_from, v_to);
                args.iter_mut()
                    .for_each(|expr| expr.substitute_in_place(v_from, v_to));
            }
            Expr::IsCtor(_, e) | Expr::Neg(e) | Expr::Not(e) => {
                e.substitute_in_place(v_from, v_to);
            }
            Expr::IfThenElse(exprs) => {
                let [p, e1, e2] = &mut **exprs;
                p.substitute_in_place(v_from, v_to);
                e1.substitute_in_place(v_from, v_to);
                e2.substitute_in_place(v_from, v_to);
            }
            Expr::Constant(_) | Expr::ThyFunc(_) => {}
            Expr::Exists(..) => {
                todo!("unexpected! exists")
            }
        }
    }

    pub(crate) fn substitute(&self, v_from: &T::Var, v_to: &Expr<T>) -> Self {
        let mut new_expr = self.clone();
        new_expr.substitute_in_place(v_from, v_to);
        new_expr
    }
}

impl<T: Types> Pred<T> {
    /// Substitute the variable `v_from` with the expression `v_to` everywhere
    /// inside this predicate (including kvar arguments and inside `Hyp` cube
    /// bodies / extra-binder preds).
    pub(crate) fn substitute_var(&self, v_from: &T::Var, v_to: &Expr<T>) -> Self {
        match self {
            Pred::And(ps) => {
                Pred::and(ps.iter().map(|p| p.substitute_var(v_from, v_to)).collect())
            }
            Pred::KVar(k, args) => {
                Pred::KVar(
                    k.clone(),
                    args.iter().map(|a| a.substitute(v_from, v_to)).collect(),
                )
            }
            Pred::Expr(e) => Pred::Expr(e.substitute(v_from, v_to)),
            Pred::Hyp(cubes) => {
                Pred::Hyp(
                    cubes
                        .iter()
                        .map(|c| crate::constraint::Cube {
                            extra_binders: c
                                .extra_binders
                                .iter()
                                .map(|b| Bind {
                                    name: b.name.clone(),
                                    sort: b.sort.clone(),
                                    pred: b.pred.substitute_var(v_from, v_to),
                                })
                                .collect(),
                            body: Box::new(c.body.substitute_var(v_from, v_to)),
                        })
                        .collect(),
                )
            }
        }
    }
}

/// A cube collected during walk: the chain of ForAll binders enclosing one
/// occurrence of `KVar(k, formals)` at a *head* position, plus those formals
/// and the in-scope guard predicates already conjoined alongside the kvar at
/// the head (`Pred::And([..., KVar(k,_), ...])`).
struct CollectedCube<T: Types> {
    binders: Vec<Bind<T>>,
    formals: Vec<Expr<T>>,
}

/// Walk `cstr` and collect a cube for each *head* occurrence of `var`.
fn collect_cubes<T: Types>(
    cstr: &Constraint<T>,
    var: &T::KVar,
    binders: &mut Vec<Bind<T>>,
    out: &mut Vec<CollectedCube<T>>,
) {
    match cstr {
        Constraint::Conj(cs) => {
            for c in cs {
                collect_cubes(c, var, binders, out);
            }
        }
        Constraint::ForAll(bind, inner) => {
            binders.push(bind.clone());
            collect_cubes(inner, var, binders, out);
            binders.pop();
        }
        Constraint::Pred(pred, _tag) => {
            collect_cubes_pred(pred, var, binders, out);
        }
    }
}

fn collect_cubes_pred<T: Types>(
    pred: &Pred<T>,
    var: &T::KVar,
    binders: &[Bind<T>],
    out: &mut Vec<CollectedCube<T>>,
) {
    match pred {
        Pred::And(ps) => {
            for p in ps {
                collect_cubes_pred(p, var, binders, out);
            }
        }
        Pred::KVar(kvid, args) if var.eq(kvid) => {
            out.push(CollectedCube { binders: binders.to_vec(), formals: args.clone() });
        }
        Pred::KVar(_, _) | Pred::Expr(_) | Pred::Hyp(_) => {}
    }
}

impl<T: Types> Pred<T> {
    /// Substitute uses of `var` (in *guard* position) with `Pred::Hyp` of
    /// instantiated cubes. Cube bodies preserve cut-kvar references so
    /// fixpoint can resolve them.
    fn substitute_kvar_use(
        &self,
        var: &T::KVar,
        cubes: &[CollectedCube<T>],
        scope: &HashSet<T::Var>,
        fresh: &mut dyn FnMut() -> T::Var,
    ) -> Self {
        match self {
            Pred::And(ps) => {
                Pred::and(
                    ps.iter()
                        .map(|p| p.substitute_kvar_use(var, cubes, scope, fresh))
                        .collect(),
                )
            }
            Pred::KVar(kvid, actuals) if var.eq(kvid) => {
                build_hyp_for_use(cubes, actuals, scope, fresh)
            }
            Pred::KVar(_, _) | Pred::Expr(_) => self.clone(),
            // Recurse into existing Hyp cube bodies (a previously-eliminated
            // non-cut kvar's body might transitively reference `var`).
            Pred::Hyp(inner_cubes) => {
                Pred::Hyp(
                    inner_cubes
                        .iter()
                        .map(|c| crate::constraint::Cube {
                            extra_binders: c.extra_binders.clone(),
                            body: Box::new(
                                c.body.substitute_kvar_use(var, cubes, scope, fresh),
                            ),
                        })
                        .collect(),
                )
            }
        }
    }

    /// In *head* position, replace `KVar(var, _)` with `True`.
    /// (The corresponding obligation is discharged by substitutions at use sites.)
    fn substitute_kvar_head(&self, var: &T::KVar) -> Self {
        match self {
            Pred::And(ps) => Pred::and(ps.iter().map(|p| p.substitute_kvar_head(var)).collect()),
            Pred::KVar(kvid, _) if var.eq(kvid) => Pred::TRUE,
            Pred::KVar(_, _) | Pred::Expr(_) | Pred::Hyp(_) => self.clone(),
        }
    }
}

/// Build a `Pred::Hyp` from cubes for a use site `KVar(k, actuals)`.
///
/// For each cube `c = (binders, formals)`:
///   - `extra_binders` = binders not in `scope` (sScp[k]).
///   - cube body = (⋀ pred(b) for b in extra_binders) ∧ (⋀ formal_i = actual_i).
///
/// Cube body keeps `Pred` shape so cut-kvar references inside extra binders'
/// preds are preserved verbatim for fixpoint to resolve.
fn build_hyp_for_use<T: Types>(
    cubes: &[CollectedCube<T>],
    actuals: &[Expr<T>],
    scope: &HashSet<T::Var>,
    fresh: &mut dyn FnMut() -> T::Var,
) -> Pred<T> {
    let owned: Vec<crate::constraint::Cube<T>> = cubes
        .iter()
        .map(|c| build_cube(c, actuals, scope, fresh))
        .collect();
    Pred::Hyp(owned)
}

fn build_cube<T: Types>(
    cube: &CollectedCube<T>,
    actuals: &[Expr<T>],
    scope: &HashSet<T::Var>,
    fresh: &mut dyn FnMut() -> T::Var,
) -> crate::constraint::Cube<T> {
    // All non-scope binders contribute their `pred` as a conjunct in the cube
    // body, but only `Local` binders are retained as actual existential
    // binders. Non-local placeholders (e.g. `Var::Underscore`) exist solely as
    // a syntactic vehicle for attaching a fact-pred with no real bound name;
    // dropping their pred would lose information.
    let in_cube: Vec<&Bind<T>> = cube
        .binders
        .iter()
        .filter(|b| !scope.contains(&b.name))
        .collect();
    // Freshen each retained `Local` binder. Their original names may collide
    // with free variables at the use site (e.g. when the cube was collected
    // inside the same outer scope as the use site); renaming to globally-fresh
    // names avoids the existential shadowing the outer variable it should be
    // constraining.
    let mut renames: Vec<(T::Var, T::Var)> = Vec::new();
    let extra_binders: Vec<Bind<T>> = in_cube
        .iter()
        .filter(|b| b.name.is_local())
        .map(|b| {
            let new_name = fresh();
            renames.push((b.name.clone(), new_name.clone()));
            Bind { name: new_name, sort: b.sort.clone(), pred: b.pred.clone() }
        })
        .collect();
    // Apply renames to: each in_cube binder's pred (so non-Local extras' preds
    // that reference renamed locals still resolve), each formal in
    // cube.formals, and each retained extra binder's pred.
    let apply_renames_pred = |p: &Pred<T>| -> Pred<T> {
        let mut acc = p.clone();
        for (from, to) in &renames {
            acc = acc.substitute_var(from, &Expr::Var(to.clone()));
        }
        acc
    };
    let apply_renames_expr = |e: &Expr<T>| -> Expr<T> {
        let mut acc = e.clone();
        for (from, to) in &renames {
            acc = acc.substitute(from, &Expr::Var(to.clone()));
        }
        acc
    };

    let mut conjuncts: Vec<Pred<T>> = Vec::new();
    for b in &in_cube {
        if !b.pred.is_trivially_true() {
            conjuncts.push(apply_renames_pred(&b.pred));
        }
    }
    for (formal, actual) in iter::zip(&cube.formals, actuals) {
        conjuncts.push(Pred::Expr(Expr::Atom(
            BinRel::Eq,
            Box::new([apply_renames_expr(formal), actual.clone()]),
        )));
    }
    let extra_binders: Vec<Bind<T>> = extra_binders
        .into_iter()
        .map(|b| Bind { name: b.name, sort: b.sort, pred: apply_renames_pred(&b.pred) })
        .collect();
    crate::constraint::Cube {
        extra_binders,
        body: Box::new(Pred::and(conjuncts)),
    }
}
