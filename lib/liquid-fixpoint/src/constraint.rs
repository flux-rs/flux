use core::panic;
use std::{
    collections::{HashMap, VecDeque},
    hash::Hash,
    sync::LazyLock,
    vec,
};

use derive_where::derive_where;
use itertools::Itertools;

use crate::{
    DefaultTypes, KVarDecl, Types, graph::topological_sort_sccs, is_constraint_satisfiable,
    parser::ParsingTypes,
};

pub(crate) static DEFAULT_QUALIFIERS: LazyLock<[Qualifier<DefaultTypes>; 13]> =
    LazyLock::new(|| {
        // -----
        // UNARY
        // -----
        // (qualif EqTrue ((v bool)) (v))
        let eqtrue = Qualifier {
            args: vec![("v", Sort::Bool)],
            body: Expr::Var("v"),
            name: String::from("EqTrue"),
        };
        // (qualif EqFalse ((v bool)) (!v))
        let eqfalse = Qualifier {
            args: vec![("v", Sort::Bool)],
            body: Expr::Neg(Box::new(Expr::Var("v"))),
            name: String::from("EqFalse"),
        };
        // (qualif EqZero ((v int)) (v == 0))
        let eqzero = Qualifier {
            args: vec![("v", Sort::Int)],
            body: Expr::Atom(BinRel::Eq, Box::new([Expr::Var("v"), Expr::int(0)])),
            name: String::from("EqZero"),
        };

        // (qualif GtZero ((v int)) (v > 0))
        let gtzero = Qualifier {
            args: vec![("v", Sort::Int)],
            body: Expr::Atom(BinRel::Gt, Box::new([Expr::Var("v"), Expr::int(0)])),
            name: String::from("GtZero"),
        };

        // (qualif GeZero ((v int)) (v >= 0))
        let gezero = Qualifier {
            args: vec![("v", Sort::Int)],
            body: Expr::Atom(BinRel::Ge, Box::new([Expr::Var("v"), Expr::int(0)])),
            name: String::from("GeZero"),
        };

        // (qualif LtZero ((v int)) (v < 0))
        let ltzero = Qualifier {
            args: vec![("v", Sort::Int)],
            body: Expr::Atom(BinRel::Lt, Box::new([Expr::Var("v"), Expr::int(0)])),
            name: String::from("LtZero"),
        };

        // (qualif LeZero ((v int)) (v <= 0))
        let lezero = Qualifier {
            args: vec![("v", Sort::Int)],
            body: Expr::Atom(BinRel::Le, Box::new([Expr::Var("v"), Expr::int(0)])),
            name: String::from("LeZero"),
        };

        // ------
        // BINARY
        // ------

        // (qualif Eq ((a int) (b int)) (a == b))
        let eq = Qualifier {
            args: vec![("a", Sort::Int), ("b", Sort::Int)],
            body: Expr::Atom(BinRel::Eq, Box::new([Expr::Var("a"), Expr::Var("b")])),
            name: String::from("Eq"),
        };

        // (qualif Gt ((a int) (b int)) (a > b))
        let gt = Qualifier {
            args: vec![("a", Sort::Int), ("b", Sort::Int)],
            body: Expr::Atom(BinRel::Gt, Box::new([Expr::Var("a"), Expr::Var("b")])),
            name: String::from("Gt"),
        };

        // (qualif Lt ((a int) (b int)) (a < b))
        let ge = Qualifier {
            args: vec![("a", Sort::Int), ("b", Sort::Int)],
            body: Expr::Atom(BinRel::Ge, Box::new([Expr::Var("a"), Expr::Var("b")])),
            name: String::from("Ge"),
        };

        // (qualif Ge ((a int) (b int)) (a >= b))
        let lt = Qualifier {
            args: vec![("a", Sort::Int), ("b", Sort::Int)],
            body: Expr::Atom(BinRel::Lt, Box::new([Expr::Var("a"), Expr::Var("b")])),
            name: String::from("Lt"),
        };

        // (qualif Le ((a int) (b int)) (a <= b))
        let le = Qualifier {
            args: vec![("a", Sort::Int), ("b", Sort::Int)],
            body: Expr::Atom(BinRel::Le, Box::new([Expr::Var("a"), Expr::Var("b")])),
            name: String::from("Le"),
        };

        // (qualif Le1 ((a int) (b int)) (a < b - 1))
        let le1 = Qualifier {
            args: vec![("a", Sort::Int), ("b", Sort::Int)],
            body: Expr::Atom(
                BinRel::Le,
                Box::new([
                    Expr::Var("a"),
                    Expr::BinaryOp(BinOp::Sub, Box::new([Expr::Var("b"), Expr::int(1)])),
                ]),
            ),
            name: String::from("Le1"),
        };

        [eqtrue, eqfalse, eqzero, gtzero, gezero, ltzero, lezero, eq, gt, ge, lt, le, le1]
    });

#[derive_where(Hash, Clone, Debug)]
pub struct Bind<T: Types> {
    pub name: T::Var,
    pub sort: Sort<T>,
    pub pred: Pred<T>,
}

#[derive_where(Hash, Clone, Debug)]
pub enum Constraint<T: Types> {
    Pred(Pred<T>, #[derive_where(skip)] Option<T::Tag>),
    Conj(Vec<Self>),
    ForAll(Bind<T>, Box<Self>),
}

impl<T: Types> Constraint<T> {
    pub const TRUE: Self = Self::Pred(Pred::TRUE, None);

    pub fn foralls(bindings: Vec<Bind<T>>, c: Self) -> Self {
        bindings
            .into_iter()
            .rev()
            .fold(c, |c, bind| Constraint::ForAll(bind, Box::new(c)))
    }

    pub fn conj(mut cstrs: Vec<Self>) -> Self {
        if cstrs.len() == 1 { cstrs.remove(0) } else { Self::Conj(cstrs) }
    }

    /// Returns true if the constraint has at least one concrete RHS ("head") predicates.
    /// If `!c.is_concrete` then `c` is trivially satisfiable and we can avoid calling fixpoint.
    pub fn is_concrete(&self) -> bool {
        match self {
            Constraint::Conj(cs) => cs.iter().any(Constraint::is_concrete),
            Constraint::ForAll(_, c) => c.is_concrete(),
            Constraint::Pred(p, _) => p.is_concrete() && !p.is_trivially_true(),
        }
    }

    fn contains_kvars(&self) -> bool {
        match self {
            Constraint::Conj(cs) => cs.iter().any(Constraint::contains_kvars),
            Constraint::ForAll(_bind, inner) => inner.contains_kvars(),
            Constraint::Pred(p, _tag) => p.contains_kvars(),
        }
    }

    pub fn depth_first_fragments(&self) -> ConstraintFragments<T> {
        ConstraintFragments { stack: vec![(Fragment::Constraint(self), vec![])] }
    }

    fn kvar_deps(&self) -> Vec<T::KVar> {
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

    fn fragment_kvar_head(&self) -> Option<T::KVar> {
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
            Constraint::Pred(pred, _tag) => Constraint::Pred(pred.sub_kvars(assignments), None),
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
            Constraint::Pred(pred, _tag) => Constraint::Pred(pred.clone(), None),
            _ => panic!("Conjunctions should not occur in constraint fragments"),
        }
    }

    pub fn sub_head(&self, assignment: &(&Qualifier<T>, Vec<usize>)) -> Self {
        match self {
            Constraint::ForAll(bind, inner) => {
                Constraint::ForAll(bind.clone(), Box::new(inner.sub_head(assignment)))
            }
            Constraint::Pred(pred, _tag) => Constraint::Pred(pred.sub_head(assignment), None),
            _ => panic!("Conjunctions should not occur in constraint fragments"),
        }
    }

    pub fn scope(&self, var: &T::KVar) -> Self {
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
}

impl Constraint<ParsingTypes> {
    pub fn uniquify(&mut self) {
        let mut used_names = HashMap::new();
        self.uniquify_help(&mut used_names);
    }

    fn uniquify_help(&mut self, used_names: &mut HashMap<String, u32>) {
        match self {
            Constraint::ForAll(bind, inner) => {
                let bound_name = &bind.name;
                if let Some(count) = used_names.get_mut(bound_name) {
                    *count += 1;
                    let new_name = format!("{}#{}", bind.name, count);
                    used_names.insert(new_name.clone(), 0);
                    inner.rename(bound_name, &new_name);
                    bind.pred.rename(bound_name, &new_name);
                    bind.name = new_name
                } else {
                    used_names.insert(bind.name.clone(), 0);
                }
                inner.uniquify_help(used_names);
            }
            Constraint::Conj(conjuncts) => {
                conjuncts.iter_mut().for_each(|cstr| {
                    cstr.uniquify_help(used_names);
                });
            }
            Constraint::Pred(_, _) => {}
        }
    }

    fn rename(&mut self, from: &String, to: &String) {
        match self {
            Constraint::ForAll(bind, inner) => {
                if !bind.name.eq(from) {
                    bind.name = to.clone();
                    bind.pred.rename(from, to);
                    inner.rename(from, to);
                }
            }
            Constraint::Conj(conjuncts) => {
                conjuncts.iter_mut().for_each(|cstr| {
                    cstr.rename(from, to);
                });
            }
            Constraint::Pred(pred, _tag) => pred.rename(from, to),
        }
    }

    pub fn is_satisfiable(&self) -> bool {
        is_constraint_satisfiable(self)
    }

    pub fn sol1(&self, var: &String) -> Vec<(Vec<Bind<ParsingTypes>>, Vec<Expr<ParsingTypes>>)> {
        match self {
            Constraint::ForAll(bind, inner) => {
                inner
                    .sol1(var)
                    .into_iter()
                    .map(|(mut binders, exprs)| {
                        binders.push(bind.clone());
                        (binders, exprs)
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
                let args_eq: Vec<Expr<ParsingTypes>> = (0..)
                    .zip(args.iter())
                    .map(|(idx, arg)| {
                        Expr::Atom(
                            BinRel::Eq,
                            Box::new([
                                Expr::Var(format!("karg${}#{}", kvid, idx).to_string()),
                                Expr::Var(arg.clone()),
                            ]),
                        )
                    })
                    .collect();
                vec![(vec![], args_eq)]
            }
            Constraint::Pred(_, _) => vec![],
        }
    }

    pub fn elim(&self, vars: &Vec<String>) -> Self {
        vars.iter().fold(self.clone(), |acc, var| acc.elim1(var))
    }

    pub fn elim1(&self, var: &String) -> Self {
        let solution = self.scope(var).sol1(var);
        self.do_elim(var, &solution)
    }

    fn do_elim(
        &self,
        var: &String,
        solution: &Vec<(Vec<Bind<ParsingTypes>>, Vec<Expr<ParsingTypes>>)>,
    ) -> Self {
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
                    let cstrs: Vec<Constraint<ParsingTypes>> = solution
                        .iter()
                        .map(|(binders, eqs)| {
                            let (kvar_instances, other_preds) = pred.partition_pred(var);
                            let kvar_instances_subbed: Vec<Pred<ParsingTypes>> = {
                                kvar_instances
                                    .into_iter()
                                    .map(|(kvid, args)| {
                                        eqs.iter()
                                            .enumerate()
                                            .zip(args.iter())
                                            .map(|((i, eq), arg)| {
                                                Pred::Expr(eq.clone().substitute(
                                                    &format!("karg${}#{}", &kvid, i),
                                                    arg,
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
            Constraint::Pred(Pred::KVar(kvid, _args), _tag) if var.eq(kvid) => {
                Constraint::Pred(Pred::TRUE, None)
            }
            cpred => cpred.clone(),
        }
    }
}

enum Fragment<'a, T: Types> {
    Constraint(&'a Constraint<T>),
    Predicate(&'a Pred<T>),
}

pub struct ConstraintFragments<'a, T: Types> {
    stack: Vec<(Fragment<'a, T>, Vec<Bind<T>>)>,
}

impl<T: Types> Iterator for ConstraintFragments<'_, T> {
    type Item = Constraint<T>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((node, binders)) = self.stack.pop() {
            match node {
                Fragment::Predicate(Pred::And(preds)) => {
                    for p in preds.into_iter().rev() {
                        self.stack.push((Fragment::Predicate(&p), binders.clone()));
                    }
                }
                Fragment::Predicate(pred) => {
                    let mut result = Constraint::Pred(pred.clone(), None);
                    for b in binders.iter().rev() {
                        result = Constraint::ForAll(b.clone(), Box::new(result));
                    }
                    return Some(result);
                }
                Fragment::Constraint(Constraint::Pred(pred, _tag)) => {
                    self.stack
                        .push((Fragment::Predicate(pred), binders.clone()));
                }
                Fragment::Constraint(Constraint::Conj(children)) => {
                    for child in children.into_iter().rev() {
                        self.stack
                            .push((Fragment::Constraint(child), binders.clone()));
                    }
                }
                Fragment::Constraint(Constraint::ForAll(bind, inner)) => {
                    let mut new_binders = binders.clone();
                    new_binders.push(bind.clone());
                    self.stack
                        .push((Fragment::Constraint(&**inner), new_binders));
                }
            }
        }
        None
    }
}

#[derive_where(Hash)]
pub struct ConstraintWithEnv<T: Types> {
    pub kvar_decls: Vec<KVarDecl<T>>,
    pub qualifiers: Vec<Qualifier<T>>,
    pub constraint: Constraint<T>,
}

impl ConstraintWithEnv<ParsingTypes> {
    pub fn is_satisfiable(&self) -> bool {
        if self.kvar_decls.is_empty() {
            self.constraint.is_satisfiable()
        } else {
            self.solve_by_fusion()
        }
    }

    pub fn uniquify(&mut self) {
        self.constraint.uniquify();
    }

    pub fn solve_by_fusion(&self) -> bool {
        let mut cstr = self.constraint.clone();
        let mut dep_map = self.constraint.kvar_mappings().1;
        let mut acyclic_kvars: Vec<String> = dep_map
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
        let mut qualifiers: Vec<Qualifier<ParsingTypes>> = vec![];
        qualifiers.extend(self.qualifiers.to_vec().into_iter());
        let kvar_assignment = self.solve_for_kvars(&qualifiers);
        let no_kvar_cstr = self.constraint.sub_all_kvars(&kvar_assignment);
        is_constraint_satisfiable(&no_kvar_cstr)
    }

    pub fn compute_initial_assignments<'a>(
        &'a self,
        qualifiers: &'a Vec<Qualifier<ParsingTypes>>,
    ) -> HashMap<String, Vec<(&'a Qualifier<ParsingTypes>, Vec<usize>)>> {
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
        qualifiers: &'a Vec<Qualifier<ParsingTypes>>,
    ) -> HashMap<String, Vec<(&'a Qualifier<ParsingTypes>, Vec<usize>)>> {
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
}

fn type_signature_matches(
    argument_permutation: &Vec<usize>,
    kvar_decl: &KVarDecl<ParsingTypes>,
    qualifier: &Qualifier<ParsingTypes>,
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

#[derive_where(Hash)]
pub struct DataDecl<T: Types> {
    pub name: T::Sort,
    pub vars: usize,
    pub ctors: Vec<DataCtor<T>>,
}

#[derive_where(Hash)]
pub struct DataCtor<T: Types> {
    pub name: T::Var,
    pub fields: Vec<DataField<T>>,
}

#[derive_where(Hash)]
pub struct DataField<T: Types> {
    pub name: T::Var,
    pub sort: Sort<T>,
}

#[derive_where(Hash, Clone, Debug)]
pub enum Sort<T: Types> {
    Int,
    Bool,
    Real,
    Str,
    BitVec(Box<Sort<T>>),
    BvSize(u32),
    Var(usize),
    Func(Box<[Self; 2]>),
    Abs(usize, Box<Self>),
    App(SortCtor<T>, Vec<Self>),
}

impl<T: Types> Sort<T> {
    pub fn mk_func<I>(params: usize, inputs: I, output: Sort<T>) -> Sort<T>
    where
        I: IntoIterator<Item = Sort<T>>,
        I::IntoIter: DoubleEndedIterator,
    {
        let sort = inputs
            .into_iter()
            .rev()
            .fold(output, |output, input| Sort::Func(Box::new([input, output])));

        (0..params)
            .rev()
            .fold(sort, |sort, i| Sort::Abs(i, Box::new(sort)))
    }

    pub(crate) fn peel_out_abs(&self) -> (usize, &Sort<T>) {
        let mut n = 0;
        let mut curr = self;
        while let Sort::Abs(i, sort) = curr {
            assert_eq!(*i, n);
            n += 1;
            curr = sort;
        }
        (n, curr)
    }
}

#[derive_where(Hash, Clone, Debug)]
pub enum SortCtor<T: Types> {
    Set,
    Map,
    Data(T::Sort),
}

#[derive_where(Hash, Clone, Debug)]
pub enum Pred<T: Types> {
    And(Vec<Self>),
    KVar(T::KVar, Vec<T::Var>),
    Expr(Expr<T>),
}

impl<T: Types> Pred<T> {
    pub const TRUE: Self = Pred::Expr(Expr::Constant(Constant::Boolean(true)));

    pub fn and(mut preds: Vec<Self>) -> Self {
        if preds.len() == 1 { preds.remove(0) } else { Self::And(preds) }
    }

    pub fn is_trivially_true(&self) -> bool {
        match self {
            Pred::Expr(Expr::Constant(Constant::Boolean(true))) => true,
            Pred::And(ps) => ps.is_empty(),
            _ => false,
        }
    }

    pub fn is_concrete(&self) -> bool {
        match self {
            Pred::And(ps) => ps.iter().any(Pred::is_concrete),
            Pred::KVar(_, _) => false,
            Pred::Expr(_) => true,
        }
    }

    pub fn contains_kvars(&self) -> bool {
        match self {
            Pred::And(ps) => ps.iter().any(Pred::contains_kvars),
            Pred::KVar(_, _) => true,
            Pred::Expr(_) => false,
        }
    }

    pub fn kvars(&self) -> Vec<T::KVar> {
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

    pub fn sub_kvars(
        &self,
        assignment: &HashMap<T::KVar, Vec<(&Qualifier<T>, Vec<usize>)>>,
    ) -> Self {
        match self {
            Pred::KVar(kvid, args) => {
                let qualifiers = assignment.get(kvid).unwrap();
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

    pub fn sub_head(&self, assignment: &(&Qualifier<T>, Vec<usize>)) -> Self {
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
                kvar_instances.push((kvid.clone(), args.to_vec()));
            }
            _ => {
                other_preds.push(self.clone());
            }
        }
    }

    pub fn rename(&mut self, from: &T::Var, to: &T::Var) {
        match self {
            Pred::Expr(expr) => {
                expr.substitute_in_place(from, to);
            }
            Pred::KVar(_kvid, args) => {
                args.iter_mut().for_each(|arg| {
                    if from.eq(arg) {
                        *arg = to.clone();
                    }
                });
            }
            Pred::And(conjuncts) => {
                conjuncts.iter_mut().for_each(|pred| pred.rename(from, to));
            }
        }
    }
}

#[derive(Hash, Debug, Copy, Clone, PartialEq, Eq)]
pub enum BinRel {
    Eq,
    Ne,
    Gt,
    Ge,
    Lt,
    Le,
}

impl BinRel {
    pub const INEQUALITIES: [BinRel; 4] = [BinRel::Gt, BinRel::Ge, BinRel::Lt, BinRel::Le];
}

#[derive_where(Hash, Clone, Debug)]
pub enum Expr<T: Types> {
    Constant(Constant<T>),
    Var(T::Var),
    App(Box<Self>, Vec<Self>),
    Neg(Box<Self>),
    BinaryOp(BinOp, Box<[Self; 2]>),
    IfThenElse(Box<[Self; 3]>),
    And(Vec<Self>),
    Or(Vec<Self>),
    Not(Box<Self>),
    Imp(Box<[Self; 2]>),
    Iff(Box<[Self; 2]>),
    Atom(BinRel, Box<[Self; 2]>),
    Let(T::Var, Box<[Self; 2]>),
}

impl<T: Types> From<Constant<T>> for Expr<T> {
    fn from(v: Constant<T>) -> Self {
        Self::Constant(v)
    }
}

impl<T: Types> Expr<T> {
    pub const fn int(val: u128) -> Expr<T> {
        Expr::Constant(Constant::Numeral(val))
    }

    pub fn eq(self, other: Self) -> Self {
        Expr::Atom(BinRel::Eq, Box::new([self, other]))
    }

    pub fn and(mut exprs: Vec<Self>) -> Self {
        if exprs.len() == 1 { exprs.remove(0) } else { Self::And(exprs) }
    }

    pub fn substitute_in_place(&mut self, v_from: &T::Var, v_to: &T::Var) {
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

    pub fn substitute(&self, v_from: &T::Var, v_to: &T::Var) -> Self {
        let mut new_expr = self.clone();
        new_expr.substitute_in_place(v_from, v_to);
        new_expr
    }
}

#[derive_where(Hash, Clone, Debug)]
pub enum Constant<T: Types> {
    Numeral(u128),
    Decimal(T::Decimal),
    Boolean(bool),
    String(T::String),
    BitVec(u128, u32),
}

#[derive_where(Debug, Clone, Hash)]
pub struct Qualifier<T: Types> {
    pub name: String,
    pub args: Vec<(T::Var, Sort<T>)>,
    pub body: Expr<T>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}
