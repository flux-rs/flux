use std::{collections::HashSet, iter};

use itertools::Itertools;

use crate::{
    Assignments, BinRel, Identifier, Types,
    constraint::{Bind, Constraint, Expr, Pred, Qualifier},
    constraint_fragments::ConstraintFragments,
    graph::{FxIndexMap, FxIndexSet, topological_sort_sccs},
};

impl<T: Types> Constraint<T> {
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
        let mut non_cuts = self.compute_non_cuts();
        non_cuts.sort_by_key(|k| k.display().to_string());
        eprintln!(
            "[flux noncut elim] non_cuts ({}): {}",
            non_cuts.len(),
            non_cuts.iter().map(|k| k.display().to_string()).collect::<Vec<_>>().join(", "),
        );
        non_cuts.iter().fold(self.clone(), |mut acc, var| {
            acc = acc.elim1_v2(var, fresh);
            acc.simplify();
            acc
        })
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

    fn kvars(&self) -> Vec<T::KVar> {
        match self {
            Pred::KVar(kvid, _args) => vec![kvid.clone()],
            Pred::Expr(_expr) => vec![],
            Pred::And(conjuncts) => conjuncts.iter().flat_map(Pred::kvars).unique().collect(),
            Pred::Hyp(cubes) => cubes.iter().flat_map(|c| c.body.kvars()).unique().collect(),
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
            Expr::WKVar(wkvar) => {
                wkvar
                    .args
                    .iter_mut()
                    .for_each(|expr| expr.substitute_in_place(v_from, v_to));
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
