use std::{collections::{HashMap, HashSet}, iter};

use itertools::Itertools;

use crate::{
    Assignments, BinRel, Identifier, Types,
    constraint::{Bind, Constant, Constraint, Expr, Pred, Qualifier},
    constraint_fragments::ConstraintFragments,
    graph::topological_sort_sccs,
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
    pub(crate) fn kvar_ranks(&self, n_max: usize) -> HashMap<T::KVar, usize> {
        let mut rank: HashMap<T::KVar, usize> = HashMap::new();
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

    pub(crate) fn kvar_mappings(&self) -> HashMap<T::KVar, Vec<Constraint<T>>> {
        let mut kvar_to_fragments: HashMap<T::KVar, Vec<Constraint<T>>> = HashMap::new();
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
    pub(crate) fn kvar_dep_graph(&self) -> HashMap<T::KVar, Vec<T::KVar>> {
        fn go<T: Types>(
            cstr: &Constraint<T>,
            deps: &mut Vec<T::KVar>,
            graph: &mut HashMap<T::KVar, Vec<T::KVar>>,
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
    pub fn elim_non_cut_kvars(&mut self) -> Self {
        self.simplify();
        let non_cuts = self.compute_non_cuts();
        let mut non_cuts = non_cuts;
        non_cuts.sort_by_key(|k| k.display().to_string());
        if std::env::var("FLUX_DEBUG_NONCUT").is_ok() {
            eprintln!("[noncut] vars={non_cuts:?}\n[noncut] before={:#?}", self);
        }
        let out = self.elim(&non_cuts);
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

    pub fn elim(&self, vars: &[T::KVar]) -> Self {
        vars.iter().fold(self.clone(), |mut acc, var| {
            acc = acc.elim1(var);
            acc.simplify();
            acc
        })
    }

    fn elim1(&self, var: &T::KVar) -> Self {
        let solution = self.sol1(var);
        let scope = self.kvar_scope(var);
        if std::env::var("FLUX_DEBUG_NONCUT").is_ok() {
            eprintln!("[noncut] elim var={var:?} scope={scope:?} solution_count={}", solution.len());
            for (i, sol) in solution.iter().enumerate() {
                eprintln!("[noncut] solution[{i}] {}", self.fmt_cube_pred(sol, &scope));
            }
        }
        self.do_elim(var, &solution, &scope)
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
        let body_parts: Vec<_> = equalities.iter().chain(binder_preds.iter()).collect();
        let body = body_parts.join(" /\\ ");
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

    fn pred_to_expr(pred: &Pred<T>) -> Option<Expr<T>> {
        match pred {
            Pred::Expr(expr) => Some(expr.clone()),
            Pred::And(preds) => preds
                .iter()
                .map(Self::pred_to_expr)
                .collect::<Option<Vec<_>>>()
                .map(Expr::and),
            Pred::KVar(_, _) => None,
        }
    }

    fn do_elim(&self, var: &T::KVar, solution: &[Solution<T>], scope: &HashSet<T::Var>) -> Self {
        match self {
            Constraint::Conj(conjuncts) => {
                Constraint::Conj(
                    conjuncts
                        .iter()
                        .map(|cstr| cstr.do_elim(var, solution, scope))
                        .collect(),
                )
            }
            Constraint::ForAll(Bind { name, sort, pred }, inner) => {
                let inner_elimmed = inner.do_elim(var, solution, scope);
                match pred.find_kvar_in_guard(var) {
                    Ok(_) => Constraint::ForAll(
                        Bind { name: name.clone(), sort: sort.clone(), pred: pred.clone() },
                        Box::new(inner_elimmed),
                    ),
                    Err((kvar_instances, preds)) => {
                        let cube_preds: Vec<Pred<T>> = solution
                            .iter()
                            .map(|Solution { binders, args }| {
                                let mut body_preds = preds.clone();
                                body_preds.extend(kvar_instances.iter().flat_map(|(_, eqs)| {
                                    iter::zip(args, eqs).map(|(arg, eq)| {
                                        Pred::Expr(Expr::Atom(
                                            BinRel::Eq,
                                            Box::new([eq.clone(), arg.clone()]),
                                        ))
                                    })
                                }));
                                // Include non-kvar predicates from extra binders (not in scope).
                                // KVar binder preds are skipped (treated as True, since cut-kvar
                                // solutions are not available on the Rust side).
                                for binder in binders {
                                    if !scope.contains(&binder.name) {
                                        if matches!(binder.pred, Pred::Expr(_)) {
                                            body_preds.push(binder.pred.clone());
                                        }
                                    }
                                }
                                let body = Pred::and(body_preds);
                                if let Some(body_expr) = Self::pred_to_expr(&body) {
                                    let free_vars = body_expr.free_vars();
                                    let exist_binders = binders
                                        .iter()
                                        .filter(|binder| {
                                            free_vars.contains(&binder.name)
                                                && !scope.contains(&binder.name)
                                        })
                                        .map(|binder| (binder.name.clone(), binder.sort.clone()))
                                        .collect_vec();
                                    if exist_binders.is_empty() {
                                        body
                                    } else {
                                        Pred::Expr(Expr::Exists(exist_binders, Box::new(body_expr)))
                                    }
                                } else {
                                    body
                                }
                            })
                            .collect();
                        // Take the disjunction of all cube predicates when possible,
                        // otherwise fall back to a conjunction of separate ForAll constraints.
                        let new_pred = match cube_preds.len() {
                            0 => Pred::TRUE,
                            1 => cube_preds.into_iter().next().unwrap(),
                            _ => {
                                let exprs: Option<Vec<Expr<T>>> =
                                    cube_preds.iter().map(Self::pred_to_expr).collect();
                                if let Some(exprs) = exprs {
                                    Pred::Expr(Expr::Or(exprs))
                                } else {
                                    // Cannot form disjunction; build a conjunction of constraints.
                                    let cstrs: Vec<Constraint<T>> = cube_preds
                                        .into_iter()
                                        .map(|p| {
                                            Constraint::ForAll(
                                                Bind {
                                                    name: name.clone(),
                                                    sort: sort.clone(),
                                                    pred: p,
                                                },
                                                Box::new(inner_elimmed.clone()),
                                            )
                                        })
                                        .collect();
                                    return Constraint::conj(cstrs);
                                }
                            }
                        };
                        Constraint::ForAll(
                            Bind { name: name.clone(), sort: sort.clone(), pred: new_pred },
                            Box::new(inner_elimmed),
                        )
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
            new_outer.insert(bind.name.clone());
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
    dep_graph: &HashMap<T::KVar, Vec<T::KVar>>,
    rank: &HashMap<T::KVar, usize>,
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

            let remaining: HashSet<T::KVar> = scc.iter().filter(|k| **k != cut).cloned().collect();

            let sub_graph: HashMap<T::KVar, Vec<T::KVar>> = remaining
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
        }
    }

    fn kvars(&self) -> Vec<T::KVar> {
        match self {
            Pred::KVar(kvid, _args) => vec![kvid.clone()],
            Pred::Expr(_expr) => vec![],
            Pred::And(conjuncts) => conjuncts.iter().flat_map(Pred::kvars).unique().collect(),
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
            _ => panic!("Conjunctions should not occur here"),
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
