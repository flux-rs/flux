use std::collections::HashMap;

use derive_where::derive_where;
#[cfg(feature = "rust-fixpoint")]
use {
    crate::{
        FixpointStatus, Sort, SortCtor, cstr2smt2::{Env, is_constraint_satisfiable, new_binding, new_datatype}, graph,
    },
    itertools::Itertools,
    std::collections::{HashMap, VecDeque},
    z3::Solver,
};

use crate::{
    constraint::{Constraint, Qualifier}, ConstDecl, DataDecl, KVarDecl, Sort, SortCtor, Types, graph,
};
use itertools::Itertools;

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
        let datatype_decls = topo_sort_data_declarations(datatype_decls);
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

    pub(crate) fn eliminate_acyclic_kvars(&mut self) {
        let mut dep_graph = self.constraint.kvar_dep_graph();
        let mut acyclic_kvars: Vec<T::KVar> = dep_graph
            .into_iter()
            .filter(|(_, dependencies)| dependencies.is_empty())
            .map(|(kvar, _)| kvar)
            .collect();
        while !acyclic_kvars.is_empty() {
            self.constraint = self.constraint.elim(&acyclic_kvars);
            dep_graph = self.constraint.kvar_dep_graph();
            acyclic_kvars = dep_graph
                .into_iter()
                .filter(|(_, dependencies)| dependencies.is_empty())
                .map(|(kvar, _)| kvar)
                .collect();
        }
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
}

pub fn topo_sort_data_declarations<T: Types>(datatype_decls: Vec<DataDecl<T>>) -> Vec<DataDecl<T>> {
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
