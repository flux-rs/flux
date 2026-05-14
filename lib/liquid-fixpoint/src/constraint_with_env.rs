use derive_where::derive_where;
#[cfg(feature = "rust-fixpoint")]
use {
    crate::{
        FixpointStatus, Sort, SortCtor,
        cstr2smt2::{Env, is_constraint_satisfiable, new_binding, new_datatype},
        graph,
    },
    itertools::Itertools,
    std::collections::{HashMap, HashSet, VecDeque},
    z3::Solver,
};

#[allow(unused)]
#[derive_where(Hash)]
pub struct ConstraintWithEnv<T: Types> {
    datatype_decls: Vec<DataDecl<T>>,
    kvar_decls: Vec<KVarDecl<T>>,
    qualifiers: Vec<Qualifier<T>>,
    constants: Vec<ConstDecl<T>>,
    constraint: Constraint<T>,
}
#[cfg(feature = "rust-fixpoint")]
use crate::Assignments;
use crate::{
    ConstDecl, DataDecl, KVarDecl, Types,
    constraint::{Constraint, Qualifier},
};

#[cfg(not(feature = "rust-fixpoint"))]
impl<T: Types> ConstraintWithEnv<T> {
    #[allow(unused)]
    pub fn new(
        datatype_decls: Vec<DataDecl<T>>,
        kvar_decls: Vec<KVarDecl<T>>,
        qualifiers: Vec<Qualifier<T>>,
        constants: Vec<ConstDecl<T>>,
        constraint: Constraint<T>,
    ) -> Self {
        Self { datatype_decls, kvar_decls, qualifiers, constants, constraint }
    }
}

#[cfg(feature = "rust-fixpoint")]
impl<T: Types> ConstraintWithEnv<T> {
    pub fn new(
        datatype_decls: Vec<DataDecl<T>>,
        kvar_decls: Vec<KVarDecl<T>>,
        qualifiers: Vec<Qualifier<T>>,
        constants: Vec<ConstDecl<T>>,
        constraint: Constraint<T>,
    ) -> Self {
        let datatype_decls = Self::topo_sort_data_declarations(datatype_decls);
        Self { datatype_decls, kvar_decls, qualifiers, constants, constraint }
    }

    pub fn compute_initial_assignments(&self) -> Assignments<'_, T> {
        let mut assignments = HashMap::new();

        for decl in &self.kvar_decls {
            let kvar_arg_count = decl.sorts.len();
            assignments.insert(decl.kvid.clone(), vec![]);
            for qualifier in &self.qualifiers {
                let qualifier_arg_count = qualifier.args.len();
                for argument_combination in (0..kvar_arg_count).combinations(qualifier_arg_count) {
                    assignments.get_mut(&decl.kvid).unwrap().extend(
                        argument_combination
                            .into_iter()
                            .permutations(qualifier_arg_count)
                            .filter(|arg_permutation| {
                                type_signature_matches(arg_permutation, decl, qualifier)
                            })
                            .map(|arg_permutation| (qualifier, arg_permutation)),
                    );
                }
            }
        }

        assignments
    }

    fn solve_for_kvars(&self, solver: &Solver, env: &mut Env<T>) -> Assignments<'_, T> {
        let mut assignments = self.compute_initial_assignments();
        let kvars_to_fragments = self.constraint.kvar_mappings();
        let topo_order_fragments = self.constraint.topo_order_fragments();
        let mut work_list = VecDeque::from_iter(topo_order_fragments.iter());
        while let Some(fragment) = work_list.pop_front() {
            if let Some(kvar_name) = fragment.fragment_kvar_head()
                && let subbed = fragment.sub_kvars_except_head(&assignments)
                && let Some(assignment) = assignments.get_mut(&kvar_name)
            {
                let initial_length = assignment.len();
                assignment.retain(|assignment| {
                    let vc = subbed.sub_head(assignment);
                    is_constraint_satisfiable(&vc, solver, env).is_safe()
                });
                if initial_length > assignment.len() {
                    work_list.extend(
                        fragment
                            .kvar_deps()
                            .iter()
                            .flat_map(|kvar| kvars_to_fragments.get(kvar).unwrap().iter()),
                    );
                }
            }
        }
        assignments
    }

    pub fn is_satisfiable(&mut self) -> FixpointStatus<T::Tag> {
        self.solve_by_fusion()
    }

    /// Eliminate KVars that are acyclic (have no dependencies) from the
    /// constraint by repeatedly removing KVars with empty dependency lists.
    /// Returns the list of KVars that were eliminated (in the order they were
    /// discovered).
    pub(crate) fn eliminate_acyclic_kvars(&mut self) -> Vec<T::KVar> {
        let mut removed: Vec<T::KVar> = Vec::new();
        let mut dep_graph = self.constraint.kvar_dep_graph();
        let mut acyclic_kvars: Vec<T::KVar> = dep_graph
            .into_iter()
            .filter(|(_, dependencies)| dependencies.is_empty())
            .map(|(kvar, _)| kvar)
            .collect();
        while !acyclic_kvars.is_empty() {
            // record
            for k in &acyclic_kvars {
                removed.push(k.clone());
            }
            // eliminate from constraint
            self.constraint = self.constraint.elim(&acyclic_kvars);
            // recompute
            dep_graph = self.constraint.kvar_dep_graph();
            acyclic_kvars = dep_graph
                .into_iter()
                .filter(|(_, dependencies)| dependencies.is_empty())
                .map(|(kvar, _)| kvar)
                .collect();
        }
        removed
    }

    fn simplify(&mut self) {
        self.constraint.simplify();
    }

    pub fn solve_by_fusion(&mut self) -> FixpointStatus<T::Tag> {
        self.simplify();
        self.eliminate_acyclic_kvars();
        self.solve_by_predicate_abstraction()
    }

    pub fn solve_by_predicate_abstraction(&mut self) -> FixpointStatus<T::Tag> {
        let solver = Solver::new();
        let mut vars: Env<T> = Env::new();
        self.constants.iter().for_each(|const_decl| {
            vars.insert(
                const_decl.name.clone(),
                new_binding(&const_decl.name, &const_decl.sort, &vars),
            );
        });
        self.datatype_decls.iter().for_each(|data_decl| {
            let datatype_sort = new_datatype(&data_decl.name, data_decl, &mut vars);
            vars.insert_data_decl(data_decl.name.clone(), datatype_sort);
        });
        let kvar_assignment = self.solve_for_kvars(&solver, &mut vars);
        self.constraint = self.constraint.sub_all_kvars(&kvar_assignment);
        is_constraint_satisfiable(&self.constraint, &solver, &mut vars)
    }

    /// Compute the set of non-cut KVars using the SCC+rank algorithm that mirrors
    /// the Haskell fixpoint `elimVars`/`sccElims`/`edgeRankCut` logic in
    /// `Language.Fixpoint.Graph.Deps`.
    ///
    /// For each SCC of the KVar dependency graph:
    ///   - Singleton without a self-loop → non-cut (can be eliminated).
    ///   - Singleton with self-loop, or multi-node SCC → pick the KVar with the
    ///     minimum rank (= smallest fragment index where it appears as an LHS
    ///     assumption) as a cut, remove it, recompute SCCs on the remaining
    ///     sub-graph, and recurse.
    #[cfg(feature = "rust-fixpoint")]
    pub fn compute_non_cuts(&mut self) -> Vec<String> {
        use crate::Identifier;

        let n_max = self.constraint.depth_first_fragments().count();
        let rank = self.constraint.kvar_ranks(n_max);
        let dep_graph = self.constraint.kvar_dep_graph();
        let sccs = graph::topological_sort_sccs(&dep_graph);

        let mut non_cuts: Vec<T::KVar> = Vec::new();
        for scc in sccs {
            scc_dep::<T>(&scc, &dep_graph, &rank, n_max, &mut non_cuts);
        }
        non_cuts.into_iter().map(|k| format!("{}", k.display())).collect()
    }

    fn topo_sort_data_declarations(datatype_decls: Vec<DataDecl<T>>) -> Vec<DataDecl<T>> {
        let mut datatype_dependencies: HashMap<T::Sort, Vec<T::Sort>> = HashMap::new();
        for datatype_decl in &datatype_decls {
            datatype_dependencies.insert(datatype_decl.name.clone(), vec![]);
        }
        let mut data_decls_by_name = HashMap::new();
        for datatype_decl in datatype_decls {
            for data_constructor in &datatype_decl.ctors {
                for accessor in &data_constructor.fields {
                    if let Sort::App(ctor, _) = &accessor.sort
                        && let SortCtor::Data(data_ctor) = &ctor
                    {
                        datatype_dependencies
                            .get_mut(&datatype_decl.name)
                            .unwrap()
                            .push(data_ctor.clone());
                    }
                }
            }
            data_decls_by_name.insert(datatype_decl.name.clone(), datatype_decl);
        }
        graph::topological_sort_sccs(&datatype_dependencies)
            .into_iter()
            .flatten()
            .rev()
            .map(|datatype_decl_name| data_decls_by_name.remove(&datatype_decl_name).unwrap())
            .collect_vec()
    }
}

#[cfg(feature = "rust-fixpoint")]
fn type_signature_matches<T: Types>(
    argument_permutation: &[usize],
    kvar_decl: &KVarDecl<T>,
    qualifier: &Qualifier<T>,
) -> bool {
    if argument_permutation.len() != qualifier.args.len() {
        return false;
    }

    for (qs, ks) in qualifier.args.iter().map(|arg| arg.1.clone()).zip(
        argument_permutation
            .iter()
            .map(|arg_idx| kvar_decl.sorts[*arg_idx].clone()),
    ) {
        if qs.to_string().ne(&ks.to_string()) {
            return false;
        }
    }

    true
}

/// Recursively apply the SCC+rank cut-selection algorithm (mirrors Haskell's
/// `sccElims`/`edgeRankCut` in `Language.Fixpoint.Graph.Deps`).
///
/// `scc`       – the nodes of one SCC (from `topological_sort_sccs`).
/// `dep_graph` – the *current* sub-graph being processed (not the original).
/// `rank`      – pre-computed minimum fragment index per KVar (from `kvar_ranks`).
/// `n_max`     – fallback rank for KVars not seen as assumptions (treated as ∞).
/// `non_cuts`  – accumulator; KVars that can be eliminated are pushed here.
#[cfg(feature = "rust-fixpoint")]
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
            // Singleton SCC: non-cut iff no self-loop.
            let has_self_loop = dep_graph.get(k).map_or(false, |deps| deps.contains(k));
            if !has_self_loop {
                non_cuts.push(k.clone());
            }
        }
        _ => {
            // Multi-node SCC (cycle): pick the KVar with the minimum rank as
            // the cut variable, remove it, recompute SCCs on the remaining
            // sub-graph, and recurse.
            let cut = scc
                .iter()
                .min_by_key(|k| rank.get(*k).copied().unwrap_or(n_max))
                .unwrap()
                .clone();

            let remaining: HashSet<T::KVar> =
                scc.iter().filter(|k| **k != cut).cloned().collect();

            let sub_graph: HashMap<T::KVar, Vec<T::KVar>> = remaining
                .iter()
                .map(|k| {
                    let deps = dep_graph.get(k).map_or(vec![], |d| {
                        d.iter().filter(|dep| remaining.contains(*dep)).cloned().collect()
                    });
                    (k.clone(), deps)
                })
                .collect();

            for sub_scc in graph::topological_sort_sccs(&sub_graph) {
                scc_dep::<T>(&sub_scc, &sub_graph, rank, n_max, non_cuts);
            }
        }
    }
}
