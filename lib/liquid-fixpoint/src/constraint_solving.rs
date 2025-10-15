use std::{collections::HashMap, iter};

use itertools::Itertools;

use crate::{
    Assignments, BinRel, Types,
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

    pub(crate) fn simplify(&mut self) {
        match self {
            Constraint::ForAll(bind, inner) => {
                bind.pred.simplify();
                inner.simplify();
            }
            Constraint::Conj(conjuncts) => {
                if conjuncts.is_empty() {
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
                    .collect_vec()
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
                conjuncts.iter().flat_map(|cstr| cstr.sol1(var)).collect()
            }
            Constraint::Pred(Pred::KVar(kvid, args), _tag) if var.eq(kvid) => {
                let arg_vars = args.iter().map(|arg| Expr::Var(arg.clone())).collect();
                vec![Solution { binders: vec![], args: arg_vars }]
            }
            Constraint::Pred(_, _) => vec![],
        }
    }

    pub fn elim(&self, vars: &[T::KVar]) -> Self {
        vars.iter().fold(self.clone(), |acc, var| acc.elim1(var))
    }

    fn elim1(&self, var: &T::KVar) -> Self {
        let solution = self.scope(var).sol1(var);
        self.do_elim(var, &solution)
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
                if pred.kvars().contains(var) {
                    let cstrs: Vec<Constraint<T>> = solution
                        .iter()
                        .map(|Solution { binders, args }| {
                            let (kvar_instances, mut preds) = pred.partition_pred(var);
                            preds.extend(kvar_instances.into_iter().flat_map(|(_, eqs)| {
                                iter::zip(args, eqs).map(|(arg, eq)| {
                                    Pred::Expr(Expr::Atom(
                                        BinRel::Eq,
                                        Box::new([Expr::Var(eq), arg.clone()]),
                                    ))
                                })
                            }));
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
                    Constraint::conj(cstrs)
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
            Pred::And(conjuncts) => conjuncts.iter().flat_map(Pred::kvars).unique().collect(),
        }
    }

    pub(crate) fn sub_kvars(&self, assignment: &Assignments<'_, T>) -> Self {
        match self {
            Pred::KVar(kvid, args) => {
                let qualifiers = assignment
                    .get(kvid)
                    .unwrap_or_else(|| panic!("{:#?} should have an assignment", kvid));
                if qualifiers.is_empty() {
                    return Pred::Expr(Expr::Constant(Constant::Boolean(false)));
                }
                if qualifiers.len() == 1 {
                    let qualifier = qualifiers[0].0;
                    Pred::Expr(
                        qualifier
                            .args
                            .iter()
                            .map(|arg| &arg.0)
                            .zip(qualifiers[0].1.iter().map(|arg_idx| &args[*arg_idx]))
                            .fold(qualifier.body.clone(), |acc, e| acc.substitute(e.0, e.1)),
                    )
                } else {
                    Pred::And(
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
    pub fn partition_pred(&self, var: &T::KVar) -> (Vec<(T::KVar, Vec<T::Var>)>, Vec<Pred<T>>) {
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
                kvar_instances.push((kvid.clone(), args.clone()));
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
            Expr::App(func, args) => {
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
        }
    }

    pub(crate) fn substitute(&self, v_from: &T::Var, v_to: &T::Var) -> Self {
        let mut new_expr = self.clone();
        new_expr.substitute_in_place(v_from, v_to);
        new_expr
    }
}
