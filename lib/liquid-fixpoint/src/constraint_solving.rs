use std::collections::HashMap;

use itertools::Itertools;

use crate::{
    BinRel, Types,
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

    pub fn kvar_mappings(
        &self,
    ) -> (HashMap<T::KVar, Vec<Constraint<T>>>, HashMap<T::KVar, Vec<T::KVar>>) {
        let mut kvar_to_fragments: HashMap<T::KVar, Vec<Constraint<T>>> = HashMap::new();
        let mut kvar_to_dependencies: HashMap<T::KVar, Vec<T::KVar>> = HashMap::new();
        for frag in self.depth_first_fragments() {
            if let Some(kvar) = frag.fragment_kvar_head() {
                kvar_to_dependencies
                    .entry(kvar.clone())
                    .or_insert_with(Vec::new)
                    .extend_from_slice(&frag.kvar_deps().into_iter().unique().collect::<Vec<_>>());
                kvar_to_fragments
                    .entry(kvar.clone())
                    .or_insert_with(Vec::new)
                    .push(frag);
            }
        }
        (kvar_to_fragments, kvar_to_dependencies)
    }

    pub fn topo_order_fragments(&self) -> Vec<Self> {
        let (mut kvar_to_fragments, kvar_to_dependencies) = self.kvar_mappings();
        let topologically_ordered_kvids = topological_sort_sccs::<T>(&kvar_to_dependencies);
        topologically_ordered_kvids
            .into_iter()
            .rev()
            .flatten()
            .map(|kvid| kvar_to_fragments.remove(&kvid).unwrap())
            .flatten()
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

    pub fn sub_all_kvars(
        &self,
        assignments: &HashMap<T::KVar, Vec<(&Qualifier<T>, Vec<usize>)>>,
    ) -> Self {
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

    pub fn sub_kvars_except_head(
        &self,
        assignments: &HashMap<T::KVar, Vec<(&Qualifier<T>, Vec<usize>)>>,
    ) -> Self {
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

    pub(crate) fn simplify(&mut self) {
        match self {
            Constraint::ForAll(bind, inner) => {
                bind.pred.simplify();
                inner.simplify();
            }
            Constraint::Conj(conjuncts) => {
                if conjuncts.len() == 0 {
                    *self = Constraint::Pred(Pred::TRUE, None);
                } else if conjuncts.len() == 1 {
                    conjuncts[0].simplify();
                    *self = conjuncts[0].clone();
                } else {
                    conjuncts
                        .iter_mut()
                        .for_each(|conjunct| conjunct.simplify());
                }
            }
            Constraint::Pred(p, tag) => {
                match p {
                    Pred::And(conjuncts) => {
                        let mut cstr_conj = Constraint::Conj(
                            conjuncts
                                .iter()
                                .cloned()
                                .map(|pred| Constraint::Pred(pred, tag.clone()))
                                .collect(),
                        );
                        cstr_conj.simplify();
                        *self = cstr_conj;
                    }
                    _ => {
                        p.simplify();
                    }
                }
            }
        }
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
                    .collect::<Vec<Self>>()
                    .as_slice()
                {
                    [] => Some(self.clone()),
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
                        binders.push(bind.clone());
                        Solution { binders, args }
                    })
                    .collect()
            }
            Constraint::Conj(conjuncts) => {
                conjuncts
                    .iter()
                    .map(|cstr| cstr.sol1(var))
                    .flatten()
                    .collect()
            }
            Constraint::Pred(Pred::KVar(kvid, args), _tag) if var.eq(kvid) => {
                let arg_vars = args.iter().map(|arg| Expr::Var(arg.clone())).collect();
                vec![Solution { binders: vec![], args: arg_vars }]
            }
            Constraint::Pred(_, _) => vec![],
        }
    }

    pub(crate) fn elim(&self, vars: &Vec<T::KVar>) -> Self {
        vars.iter().fold(self.clone(), |acc, var| acc.elim1(var))
    }

    fn elim1(&self, var: &T::KVar) -> Self {
        let solution = self.scope(var).sol1(var);
        self.do_elim(var, &solution)
    }

    fn do_elim(&self, var: &T::KVar, solution: &Vec<Solution<T>>) -> Self {
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
                if pred.kvars().contains(var) {
                    let cstrs: Vec<Constraint<T>> = solution
                        .iter()
                        .map(|Solution { binders, args }| {
                            let (kvar_instances, other_preds) = pred.partition_pred(var);
                            let kvar_instances_subbed: Vec<Pred<T>> = {
                                kvar_instances
                                    .into_iter()
                                    .map(|(_kvid, eqs)| {
                                        args.iter()
                                            .zip(eqs.iter())
                                            .map(|(arg, eq)| {
                                                Pred::Expr(Expr::Atom(
                                                    BinRel::Eq,
                                                    Box::new([Expr::Var(eq.clone()), arg.clone()]),
                                                ))
                                            })
                                            .collect::<Vec<_>>()
                                    })
                                    .flatten()
                                    .collect()
                            };
                            let mut preds = kvar_instances_subbed;
                            preds.extend(other_preds.into_iter());
                            let init = Constraint::ForAll(
                                Bind {
                                    name: name.clone(),
                                    sort: sort.clone(),
                                    pred: Pred::And(preds),
                                },
                                Box::new(inner_elimmed.clone()),
                            );
                            binders.iter().fold(init, |acc, binder| {
                                Constraint::ForAll(binder.clone(), Box::new(acc))
                            })
                        })
                        .collect();
                    if cstrs.len() == 1 { cstrs[0].clone() } else { Constraint::Conj(cstrs) }
                } else {
                    Constraint::ForAll(
                        Bind { name: name.clone(), sort: sort.clone(), pred: pred.clone() },
                        Box::new(inner_elimmed),
                    )
                }
            }
            Constraint::Pred(Pred::KVar(kvid, _args), tag) if var.eq(kvid) => {
                Constraint::Pred(Pred::TRUE, tag.clone())
            }
            cpred => cpred.clone(),
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
            Pred::And(conjuncts) => {
                conjuncts
                    .iter()
                    .map(Pred::kvars)
                    .flatten()
                    .unique()
                    .collect()
            }
        }
    }

    pub(crate) fn sub_kvars(
        &self,
        assignment: &HashMap<T::KVar, Vec<(&Qualifier<T>, Vec<usize>)>>,
    ) -> Self {
        match self {
            Pred::KVar(kvid, args) => {
                let qualifiers = assignment
                    .get(kvid)
                    .expect(format!("{:#?} should have an assignment", kvid).as_str());
                if qualifiers.len() == 0 {
                    return Pred::Expr(Expr::Constant(Constant::Boolean(false)));
                }
                if qualifiers.len() == 1 {
                    let qualifier = qualifiers[0].0;
                    return Pred::Expr(
                        qualifier
                            .args
                            .iter()
                            .map(|arg| &arg.0)
                            .zip(qualifiers[0].1.iter().map(|arg_idx| &args[*arg_idx]))
                            .fold(qualifier.body.clone(), |acc, e| acc.substitute(e.0, e.1)),
                    );
                } else {
                    return Pred::And(
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
                    );
                }
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

    pub(crate) fn partition_pred(
        &self,
        var: &T::KVar,
    ) -> (Vec<(T::KVar, Vec<T::Var>)>, Vec<Pred<T>>) {
        let mut kvar_instances = vec![];
        let mut other_preds = vec![];
        self.partition_pred_help(var, &mut kvar_instances, &mut other_preds);
        (kvar_instances, other_preds)
    }

    fn partition_pred_help(
        &self,
        var: &T::KVar,
        kvar_instances: &mut Vec<(T::KVar, Vec<T::Var>)>,
        other_preds: &mut Vec<Pred<T>>,
    ) {
        match self {
            Pred::And(conjuncts) => {
                conjuncts
                    .iter()
                    .for_each(|pred| pred.partition_pred_help(var, kvar_instances, other_preds));
            }
            Pred::KVar(kvid, args) if var.eq(kvid) => {
                kvar_instances.push((kvid.clone(), args.to_vec()));
            }
            _ => {
                other_preds.push(self.clone());
            }
        }
    }
}

impl<T: Types> Expr<T> {
    fn substitute_in_place(&mut self, v_from: &T::Var, v_to: &T::Var) {
        match self {
            Expr::Var(v) => {
                if v == v_from {
                    *v = v_to.clone();
                }
            }
            Expr::Constant(_) => {}
            Expr::BinaryOp(_, operands) => {
                operands[0].substitute_in_place(v_from, v_to);
                operands[1].substitute_in_place(v_from, v_to);
            }
            Expr::Atom(_, operands) => {
                operands[0].substitute_in_place(v_from, v_to);
                operands[1].substitute_in_place(v_from, v_to);
            }
            Expr::And(conjuncts) => {
                conjuncts
                    .iter_mut()
                    .for_each(|expr| expr.substitute_in_place(v_from, v_to));
            }
            Expr::App(func, args) => {
                func.substitute_in_place(v_from, v_to);
                args.iter_mut()
                    .for_each(|expr| expr.substitute_in_place(v_from, v_to));
            }
            _ => panic!("Not supported yet; implement as needed"),
        }
    }

    pub(crate) fn substitute(&self, v_from: &T::Var, v_to: &T::Var) -> Self {
        let mut new_expr = self.clone();
        new_expr.substitute_in_place(v_from, v_to);
        new_expr
    }
}
