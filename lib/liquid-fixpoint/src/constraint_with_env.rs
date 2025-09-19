use derive_where::derive_where;
#[cfg(feature = "rust-fixpoint")]
use {
    crate::{
        FixpointResult,
        cstr2smt2::{Env, is_constraint_satisfiable_inner, new_binding},
    },
    itertools::Itertools,
    std::collections::{HashMap, VecDeque},
    z3::{Config, Context, Solver},
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
use crate::Assignments;

#[cfg(feature = "rust-fixpoint")]
impl<T: Types> ConstraintWithEnv<T> {
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

    fn solve_for_kvars<'ctx>(
        &self,
        ctx: &'ctx Context,
        solver: &Solver<'ctx>,
        env: &mut Env<'ctx, T>,
    ) -> Assignments<'_, T> {
        let mut assignments = self.compute_initial_assignments();
        let (kvars_to_fragments, _) = self.constraint.kvar_mappings();
        let topo_order_fragments = self.constraint.topo_order_fragments();
        let mut work_list = VecDeque::from_iter(topo_order_fragments.iter());
        while !work_list.is_empty() {
            if let Some(fragment) = work_list.pop_front()
                && let Some(kvar_name) = fragment.fragment_kvar_head()
                && let subbed = fragment.sub_kvars_except_head(&assignments)
                && let assignment = assignments.get_mut(&kvar_name)
                && let Some(assignment) = assignment
            {
                let initial_length = assignment.len();
                assignment.retain(|assignment| {
                    let vc = subbed.sub_head(assignment);
                    is_constraint_satisfiable_inner(ctx, &vc, solver, env).is_safe()
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
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let solver = Solver::new(&ctx);
        let mut vars: Env<'_, T> = Env::new();
        self.constants.iter().for_each(|const_decl| {
            vars.insert(
                const_decl.name.clone(),
                new_binding(&ctx, &const_decl.name, &const_decl.sort),
            );
        });
        let kvar_assignment = self.solve_for_kvars(&ctx, &solver, &mut vars);
        self.constraint = self.constraint.sub_all_kvars(&kvar_assignment);
        is_constraint_satisfiable_inner(&ctx, &self.constraint, &solver, &mut vars)
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
