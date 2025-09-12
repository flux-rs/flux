use std::collections::{HashMap, VecDeque};

use derive_where::derive_where;
use itertools::Itertools;

use crate::{
    KVarDecl, Types,
    constraint::{Constraint, Qualifier},
    is_constraint_satisfiable,
    parser::ParsingTypes,
};

#[derive_where(Hash)]
pub struct ConstraintWithEnv<T: Types> {
    pub kvar_decls: Vec<KVarDecl<T>>,
    pub qualifiers: Vec<Qualifier<T>>,
    pub constraint: Constraint<T>,
}

impl<T: Types> ConstraintWithEnv<T> {
    pub fn compute_initial_assignments<'a>(
        &'a self,
        qualifiers: &'a Vec<Qualifier<T>>,
    ) -> HashMap<T::KVar, Vec<(&'a Qualifier<T>, Vec<usize>)>> {
        let mut assignments = HashMap::new();

        for decl in &self.kvar_decls {
            let kvar_arg_count = decl.sorts.len();
            for qualifier in qualifiers {
                let qualifier_arg_count = qualifier.args.len();
                for argument_combination in (0..kvar_arg_count).combinations(qualifier_arg_count) {
                    assignments
                        .entry(decl.kvid.clone())
                        .or_insert(vec![])
                        .extend(
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
                            is_constraint_satisfiable(&vc)
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

    pub fn is_satisfiable(&self) -> bool {
        if self.kvar_decls.is_empty() {
            self.constraint.is_satisfiable()
        } else {
            self.solve_by_fusion()
        }
    }

    pub fn solve_by_fusion(&self) -> bool {
        let mut cstr = self.constraint.clone();
        let mut dep_map = self.constraint.kvar_mappings().1;
        let mut acyclic_kvars: Vec<T::KVar> = dep_map
            .into_iter()
            .filter(|(_, dependencies)| dependencies.is_empty())
            .map(|(kvar, _)| kvar)
            .collect();
        while !acyclic_kvars.is_empty() {
            cstr = cstr.elim(&acyclic_kvars);
            dep_map = cstr.kvar_mappings().1;
            acyclic_kvars = dep_map
                .into_iter()
                .filter(|(_, dependencies)| dependencies.is_empty())
                .map(|(kvar, _)| kvar)
                .collect();
        }
        ConstraintWithEnv {
            kvar_decls: self.kvar_decls.to_vec(),
            qualifiers: self.qualifiers.to_vec(),
            constraint: cstr,
        }
        .solve_by_predicate_abstraction()
    }

    pub fn solve_by_predicate_abstraction(&self) -> bool {
        let mut qualifiers: Vec<Qualifier<T>> = vec![];
        qualifiers.extend(self.qualifiers.to_vec().into_iter());
        let kvar_assignment = self.solve_for_kvars(&qualifiers);
        let no_kvar_cstr = self.constraint.sub_all_kvars(&kvar_assignment);
        is_constraint_satisfiable(&no_kvar_cstr)
    }
}

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
