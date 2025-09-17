use derive_where::derive_where;
#[cfg(feature = "rust-fixpoint")]
use {
    crate::{FixpointResult, cstr2smt2::is_constraint_satisfiable},
    itertools::Itertools,
    std::collections::{HashMap, VecDeque},
};

use crate::{
    ConstDecl, KVarDecl, Types,
    constraint::{Constraint, Qualifier},
};

#[derive_where(Hash)]
pub struct ConstraintWithEnv<T: Types> {
    pub kvar_decls: Vec<KVarDecl<T>>,
    pub qualifiers: Vec<Qualifier<T>>,
    pub constants: Vec<ConstDecl<T>>,
    pub constraint: Constraint<T>,
}

#[cfg(feature = "rust-fixpoint")]
impl<T: Types> ConstraintWithEnv<T> {
    pub fn compute_initial_assignments<'a>(
        &'a self,
        qualifiers: &'a Vec<Qualifier<T>>,
    ) -> HashMap<T::KVar, Vec<(&'a Qualifier<T>, Vec<usize>)>> {
        let mut assignments = HashMap::new();

        for decl in &self.kvar_decls {
            let kvar_arg_count = decl.sorts.len();
            assignments.insert(decl.kvid.clone(), vec![]);
            for qualifier in qualifiers {
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

    pub fn solve_for_kvars<'a>(
        &'a self,
        qualifiers: &'a Vec<Qualifier<T>>,
    ) -> HashMap<T::KVar, Vec<(&'a Qualifier<T>, Vec<usize>)>> {
        let mut assignments = self.compute_initial_assignments(qualifiers);
        let (kvars_to_fragments, _) = self.constraint.kvar_mappings();
        let topo_order_fragments = self.constraint.topo_order_fragments();
        let mut work_list = VecDeque::from_iter(topo_order_fragments.iter());
        while !work_list.is_empty() {
            if let Some(fragment) = work_list.pop_front() {
                if let Some(kvar_name) = fragment.fragment_kvar_head() {
                    let subbed = fragment.sub_kvars_except_head(&assignments);
                    let assignment = assignments.get_mut(&kvar_name);
                    if let Some(assignment) = assignment {
                        let initial_length = assignment.len();
                        assignment.retain(|assignment| {
                            let vc = subbed.sub_head(assignment);
                            is_constraint_satisfiable(&vc, &self.constants).is_safe()
                        });
                        if initial_length > qualifiers.len() {
                            work_list.extend(
                                fragment
                                    .kvar_deps()
                                    .iter()
                                    .map(|kvar| kvars_to_fragments.get(kvar).unwrap().iter())
                                    .flatten(),
                            );
                        }
                    }
                }
            }
        }
        assignments
    }

    pub fn is_satisfiable(&mut self) -> FixpointResult<T::Tag> {
        self.solve_by_fusion()
    }

    pub fn eliminate_acyclic_kvars(&mut self) {
        let mut dep_map = self.constraint.kvar_mappings().1;
        let mut acyclic_kvars: Vec<T::KVar> = dep_map
            .into_iter()
            .filter(|(_, dependencies)| dependencies.is_empty())
            .map(|(kvar, _)| kvar)
            .collect();
        while !acyclic_kvars.is_empty() {
            self.constraint = self.constraint.elim(&acyclic_kvars);
            dep_map = self.constraint.kvar_mappings().1;
            acyclic_kvars = dep_map
                .into_iter()
                .filter(|(_, dependencies)| dependencies.is_empty())
                .map(|(kvar, _)| kvar)
                .collect();
        }
    }

    fn simplify(&mut self) {
        self.constraint.simplify();
    }

    pub fn solve_by_fusion(&mut self) -> FixpointResult<T::Tag> {
        self.simplify();
        self.eliminate_acyclic_kvars();
        self.solve_by_predicate_abstraction()
    }

    pub fn solve_by_predicate_abstraction(&mut self) -> FixpointResult<T::Tag> {
        let mut qualifiers: Vec<Qualifier<T>> = vec![];
        qualifiers.extend(self.qualifiers.to_vec().into_iter());
        let kvar_assignment = self.solve_for_kvars(&qualifiers);
        self.constraint = self.constraint.sub_all_kvars(&kvar_assignment);
        is_constraint_satisfiable(&self.constraint, &self.constants)
    }
}

#[cfg(feature = "rust-fixpoint")]
fn type_signature_matches<T: Types>(
    argument_permutation: &Vec<usize>,
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
