use std::{collections::HashSet, hash::Hash};

use derive_where::derive_where;
use itertools::Itertools;
use rustc_data_structures::fx::{FxIndexMap, FxIndexSet};

use crate::{ConstDecl, ThyFunc, Types};

#[derive_where(Hash, Clone, Debug)]
pub struct Bind<T: Types> {
    pub name: T::Var,
    pub sort: Sort<T>,
    pub preds: Vec<Pred<T>>,
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
    /// Returns the number of concrete, non-trivial head predicates in the constraint.
    pub fn concrete_head_count(&self) -> usize {
        fn go<T: Types>(c: &Constraint<T>, count: &mut usize) {
            match c {
                Constraint::Conj(cs) => cs.iter().for_each(|c| go(c, count)),
                Constraint::ForAll(_, c) => go(c, count),
                Constraint::Pred(head, _) => {
                    if head.is_concrete() && !head.is_trivially_true() {
                        *count += 1;
                    }
                }
            }
        }
        let mut count = 0;
        go(self, &mut count);
        count
    }

    /// Flattens a single constraint into a list of individual constraints which
    /// may be checked for satisfiability.
    ///
    /// NOTE: Assumes and requires that all binder names are unique, i.e.
    /// there is no shadowing (it is OK to have multiple binders of the same
    /// name so long as they never are used, e.g. UNDERSCORE).
    pub fn flatten<F1>(&self, is_underscore: F1) -> Vec<FlatConstraint<T>>
    where
        F1: Copy + Fn(&T::Var) -> bool,
    {
        match self {
            Constraint::Pred(pred, tag) => {
                vec![FlatConstraint {
                    binders: vec![],
                    assumptions: Default::default(),
                    head: pred.clone(),
                    tag: tag.clone(),
                }]
            }
            Constraint::Conj(constrs) => {
                constrs
                    .iter()
                    .flat_map(|constr| constr.flatten(is_underscore))
                    .collect_vec()
            }
            Constraint::ForAll(bind, constr) => {
                let mut flat_constrs = constr.flatten(is_underscore);
                for constr in &mut flat_constrs {
                    if !is_underscore(&bind.name) {
                        constr.binders.push((bind.name.clone(), bind.sort.clone()));
                    }
                    for pred in &bind.preds {
                        constr.add_assumption(pred.clone());
                    }
                    // if is_invariant(&bind.name) {
                    //     constr.add_invariant(bind.pred.clone());
                    // } else {
                    //     constr.add_assumption(bind.pred.clone());
                    // }
                }
                flat_constrs
            }
        }
    }
}

pub type WKVarAndConstrs<T> = (WKVar<T>, FlatConstraint<T>, Vec<FlatConstraint<T>>);
pub type VarSorts<T> = (<T as Types>::Var, Sort<T>);

#[derive_where(Clone, Debug)]
pub struct FlatConstraint<T: Types> {
    /// All of the binders that come before the head.
    ///
    /// NOTE: There should be no duplicates among the binders which are used (so
    /// e.g. UNDERSCORE appearing multiple times is OK).
    pub binders: Vec<(T::Var, Sort<T>)>,
    /// All of the assumptions (i.e. a flattened conjunction of predicates from
    /// all of the binders)
    pub assumptions: FxIndexSet<Pred<T>>,
    pub head: Pred<T>,
    #[derive_where(skip)]
    pub tag: Option<T::Tag>,
}

impl<T: Types> FlatConstraint<T> {
    /// Removes any binder corresponding to a given var. Returns the new
    /// constraint along with the removed binders and their sorts.
    ///
    /// NOTE: Assumes that all binders are unique and therefore there are no
    /// name clashes.
    pub fn remove_binders(&self, vars: &HashSet<T::Var>) -> (Vec<ConstDecl<T>>, FlatConstraint<T>) {
        let mut new_binders = self.binders.clone();
        let removed_binders = new_binders
            .extract_if(.., |(var, _sort)| vars.contains(var))
            .map(|(var, sort)| ConstDecl { name: var, sort, comment: None })
            .collect_vec();
        let new_constraint = FlatConstraint {
            binders: new_binders,
            assumptions: self.assumptions.clone(),
            head: self.head.clone(),
            tag: self.tag.clone(),
        };
        (removed_binders, new_constraint)
    }

    pub fn add_assumption(&mut self, assumption: Pred<T>) {
        match assumption {
            a @ Pred::KVar(_, _) => {
                self.assumptions.insert(a);
            }
            Pred::Expr(e) => {
                self.assumptions
                    .extend(e.as_conjunction().into_iter().map(|e| Pred::Expr(e)));
            }
        }
    }

    pub fn preconditions(&self) -> FxIndexSet<Pred<T>> {
        // If we add invariants, this becomes the union of both invariatns and
        // assumptions
        self.assumptions.clone()
    }

    /// Each element of the output is a wkvar, the constraint it corresponds to,
    /// and the other constraints which must also hold.
    ///
    /// We essentially "decompose" each assumption which contains a wkvar in
    /// order to transform the constraint into one in which that wkvar is
    /// exposed.
    ///
    /// These decompositions are of two forms.
    /// 1. Hoisting existentials to the top level.
    /// 2. Splitting disjuncts using the below property. When we split a
    ///    disjunct, we generate other constraints. A more sophisticated
    ///    analysis might try and solve multiple constraints simultaneously; if
    ///    we were to do this, we would probably want to change how this
    ///    algorithm works to avoid redundancy, e.g. by instead of generating
    ///    ((wkvar, constr, other_constrs) outputs generating (all_constrs)
    ///    outputs and letting consumers choose which wkvars to solve in each
    ///    constr.
    ///
    /// ```
    /// (p || q) => c
    /// ==
    /// (p => c) && (q => c)
    /// ```
    pub fn wkvars_and_constrs(&self) -> Vec<WKVarAndConstrs<T>> {
        let mut wkvars_and_constraints = self
            .assumptions
            .iter()
            .flat_map(|assumption| {
                assumption
                    .wkvars_in_conj()
                    .into_iter()
                    .map(|wkvar| (wkvar, self.clone(), vec![]))
            })
            .collect_vec();
        // Frontier elements:
        //   (current assumption, current constraint, other constraints)
        let mut frontier: Vec<_> = self
            .assumptions
            .iter()
            .enumerate()
            .filter_map(|(i, assumption)| {
                if let Pred::Expr(assumption_expr) = assumption
                    && assumption_expr.has_wkvar_reachable_by_split()
                {
                    let mut flat_constraint = self.clone();
                    flat_constraint.assumptions.shift_remove_index(i);
                    Some((assumption_expr.clone(), flat_constraint, vec![]))
                } else {
                    None
                }
            })
            .collect_vec();
        while let Some((e, mut constr, other_constrs)) = frontier.pop() {
            match e {
                // Base case: we reached a wkvar.
                //   Record it alongside the constraint it is associated with
                //   and the other constraints.
                //
                // NOTE: we don't need wkvars_in_conj because we explicitly
                //       handle the And.
                Expr::WKVar(wkvar) => {
                    // NOTE: Technically this isn't necessary, so we don't add
                    // the wkvar back to the assumptions. But for completeness
                    // we might want to.
                    //
                    // constr.add_assumption(Pred::Expr(e));
                    wkvars_and_constraints.push((wkvar, constr, other_constrs));
                }
                // In the And case, we add to the frontier each expression that
                // is a wkvar or can reach a wkvar; whenever we do so, we also
                // take all of the other expressions in the And and put them
                // into the current constr's assumptions.
                //
                // We do this kind of annoying filter rather than just adding
                // everything because it prevents us from cloning a bunch.
                Expr::And(conjs) => {
                    for (i, new_assumption) in conjs.iter().enumerate() {
                        if !(matches!(new_assumption, Expr::WKVar(..))
                            || new_assumption.has_wkvar_reachable_by_split())
                        {
                            continue;
                        }
                        let mut new_constr = constr.clone();
                        for (j, other_new_assumption) in conjs.iter().enumerate() {
                            if i == j {
                                continue;
                            }
                            new_constr.add_assumption(Pred::Expr(other_new_assumption.clone()));
                        }
                        frontier.push((new_assumption.clone(), new_constr, other_constrs.clone()));
                    }
                }
                // Hoist the exists and add it to the frontier.
                //
                // We assume that there is a wkvar reachable here, so we don't check.
                Expr::Quantifier(Quantifier::Exists, _, _) => {
                    let (new_vars, hoisted_e) = e.hoist_exists();
                    constr.binders.extend(new_vars);
                    frontier.push((hoisted_e, constr, other_constrs));
                }
                // This is where things get kind of complicated.
                //
                // Morally speaking what we are doing is translating the constraint
                //     (disjunct1 || disjunct2 || ...) => constr
                // into multiple constraints
                //     disjunct1 => constr
                //     disjunct2 => constr
                //     ...
                // but our frontier looks like
                //     (current assumption, constr without that assumption, other constrs we're no longer looking at)
                // So if there are N disjuncts, we'll push N items to the frontier:
                //     (disjunct1, constr, (disjunct2 => constr) + (disjunct3 => constr) + ... + other_constrs)
                // Except the same optimization applies where we won't consider a case where the disjunct
                // has no wkvars in it.
                Expr::Or(disjuncts) => {
                    for (i, disjunct) in disjuncts.iter().enumerate() {
                        if !(matches!(disjunct, Expr::WKVar(..))
                            || disjunct.has_wkvar_reachable_by_split())
                        {
                            continue;
                        }
                        let mut new_other_constrs = other_constrs.clone();
                        for (j, other_disjunct) in disjuncts.iter().enumerate() {
                            if i == j {
                                continue;
                            }
                            let mut new_other_constr = constr.clone();
                            new_other_constr.add_assumption(Pred::Expr(other_disjunct.clone()));
                            new_other_constrs.push(new_other_constr);
                        }
                        frontier.push((disjunct.clone(), constr.clone(), new_other_constrs));
                    }
                }
                _ => {}
            }
        }
        wkvars_and_constraints
    }
}

#[derive_where(Hash, Clone, Debug)]
pub struct DataDecl<T: Types> {
    pub name: T::Sort,
    pub vars: usize,
    pub ctors: Vec<DataCtor<T>>,
}

impl<T: Types> DataDecl<T> {
    pub fn deps(&self, acc: &mut Vec<T::Sort>) {
        for ctor in &self.ctors {
            for field in &ctor.fields {
                field.sort.deps(acc);
            }
        }
    }
}

#[derive_where(Hash, Clone, Debug)]
pub struct SortDecl<T: Types> {
    pub name: T::Sort,
    pub vars: usize,
}

#[derive_where(Hash, Clone, Debug)]
pub struct DataCtor<T: Types> {
    pub name: T::Var,
    pub fields: Vec<DataField<T>>,
}

#[derive_where(Hash, Clone, Debug)]
pub struct DataField<T: Types> {
    pub name: T::Var,
    pub sort: Sort<T>,
}

#[derive_where(PartialEq, Eq, Hash, Clone, Debug)]
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
    pub fn deps(&self, acc: &mut Vec<T::Sort>) {
        match self {
            Sort::App(SortCtor::Data(dt_name), args) => {
                acc.push(dt_name.clone());
                for arg in args {
                    arg.deps(acc);
                }
            }
            Sort::Func(input_and_output) => {
                let [input, output] = &**input_and_output;
                input.deps(acc);
                output.deps(acc);
            }
            Sort::Abs(_, sort) => {
                sort.deps(acc);
            }
            _ => {}
        }
    }

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

    fn free_var_sorts_to_int_help(&mut self, bound: &mut HashSet<usize>) {
        match self {
            Sort::Int
            | Sort::Real
            | Sort::Bool
            | Sort::Str
            | Sort::BvSize(..)
            | Sort::BitVec(..) => {}
            Sort::Abs(var, inner) => {
                bound.insert(*var);
                inner.free_var_sorts_to_int_help(bound);
                bound.remove(var);
            }
            Sort::App(_, args) => {
                for arg in args {
                    arg.free_var_sorts_to_int_help(bound);
                }
            }
            Sort::Func(inner) => {
                let [arg, out] = &mut **inner;
                arg.free_var_sorts_to_int_help(bound);
                out.free_var_sorts_to_int_help(bound);
            }
            Sort::Var(v) => {
                if !bound.contains(v) {
                    *self = Sort::Int;
                }
            }
        }
    }

    pub(crate) fn free_var_sorts_to_int(&mut self) {
        let mut bound = HashSet::new();
        self.free_var_sorts_to_int_help(&mut bound);
    }
}

#[derive_where(Hash, Debug)]
pub struct FunSort<T: Types> {
    pub params: usize,
    pub inputs: Vec<Sort<T>>,
    pub output: Sort<T>,
}

impl<T: Types> FunSort<T> {
    pub fn deps(&self, acc: &mut Vec<T::Sort>) {
        for sort in &self.inputs {
            sort.deps(acc);
        }
        self.output.deps(acc);
    }

    pub fn into_sort(self) -> Sort<T> {
        Sort::mk_func(self.params, self.inputs, self.output)
    }
}

#[derive_where(PartialEq, Eq, Hash, Clone, Debug)]
pub enum SortCtor<T: Types> {
    Set,
    Map,
    Data(T::Sort),
}

#[derive_where(PartialEq, Eq, Hash, Clone, Debug)]
pub enum Pred<T: Types> {
    KVar(T::KVar, Vec<Expr<T>>),
    Expr(Expr<T>),
}

impl<T: Types> Pred<T> {
    pub const TRUE: Self = Pred::Expr(Expr::TRUE);

    pub fn is_trivially_true(&self) -> bool {
        match self {
            Pred::Expr(e) => e.is_trivially_true(),
            Pred::KVar(..) => false,
        }
    }

    pub fn is_concrete(&self) -> bool {
        matches!(self, Pred::Expr(_))
    }

    // Give all the weak kvars that appear as part of a top-level conjunction.
    // This is a syntactic analysis.
    pub fn wkvars_in_conj(&self) -> Vec<WKVar<T>> {
        match self {
            Pred::Expr(e) => e.wkvars_in_conj(),
            Pred::KVar(..) => vec![],
        }
    }

    /// Remove all wkvars, replacing them with true.
    pub fn strip_wkvars(&self) -> Self {
        match self {
            Pred::Expr(e) => Pred::Expr(e.strip_wkvars()),
            Pred::KVar(..) => self.clone(),
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

#[derive_where(PartialEq, Eq, Hash, Debug, Clone)]
pub struct WKVar<T: Types> {
    pub wkvid: T::Var,
    pub args: Vec<Expr<T>>,
}

#[derive_where(PartialEq, Eq, Hash, Clone, Debug)]
pub enum Expr<T: Types> {
    Constant(Constant<T>),
    Var(T::Var),
    App(Box<Self>, Option<Vec<Sort<T>>>, Vec<Self>, Option<Sort<T>>),
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
    ThyFunc(ThyFunc),
    IsCtor(T::Var, Box<Self>),
    Quantifier(Quantifier, Vec<(T::Var, Sort<T>)>, Box<Self>),
    /// NOTE: WKVars are for internal use and we serialize them as UIFs using
    /// the var argument. We also don't emit WKVars that are in head position
    /// when translating to fixpoint.
    ///
    /// In an ideal world fixpoint would deal with weak kvars itself.
    WKVar(WKVar<T>),
}

impl<T: Types> From<Constant<T>> for Expr<T> {
    fn from(v: Constant<T>) -> Self {
        Self::Constant(v)
    }
}

impl<T: Types> Expr<T> {
    pub const FALSE: Self = Expr::Constant(Constant::Boolean(false));
    pub const TRUE: Self = Expr::Constant(Constant::Boolean(true));

    pub const fn int(val: u128) -> Expr<T> {
        Expr::Constant(Constant::Numeral(val))
    }

    pub fn eq(self, other: Self) -> Self {
        Expr::Atom(BinRel::Eq, Box::new([self, other]))
    }

    pub fn and(mut exprs: Vec<Self>) -> Self {
        if exprs.len() == 1 { exprs.remove(0) } else { Self::And(exprs) }
    }

    pub fn var_sorts_to_int(&mut self) {
        match self {
            Expr::Constant(_) | Expr::ThyFunc(_) | Expr::Var(_) => {}
            Expr::App(func, sort_args, args, out_sort) => {
                func.var_sorts_to_int();
                for arg in args {
                    arg.var_sorts_to_int();
                }
                if let Some(sort_args) = sort_args {
                    for sort_arg in sort_args {
                        sort_arg.free_var_sorts_to_int();
                    }
                }
                if let Some(out_sort) = out_sort {
                    out_sort.free_var_sorts_to_int();
                }
            }
            Expr::Neg(e) | Expr::Not(e) => {
                e.var_sorts_to_int();
            }
            Expr::BinaryOp(_, exprs)
            | Expr::Imp(exprs)
            | Expr::Iff(exprs)
            | Expr::Atom(_, exprs) => {
                let [e1, e2] = &mut **exprs;
                e1.var_sorts_to_int();
                e2.var_sorts_to_int();
            }
            Expr::IfThenElse(exprs) => {
                let [p, e1, e2] = &mut **exprs;
                p.var_sorts_to_int();
                e1.var_sorts_to_int();
                e2.var_sorts_to_int();
            }
            Expr::And(exprs) | Expr::Or(exprs) => {
                for e in exprs {
                    e.var_sorts_to_int();
                }
            }
            Expr::Let(_, exprs) => {
                let [var_e, body_e] = &mut **exprs;
                var_e.var_sorts_to_int();
                body_e.var_sorts_to_int();
            }
            Expr::IsCtor(_v, expr) => {
                expr.var_sorts_to_int();
            }
            Expr::Quantifier(_, binder, expr) => {
                for (_, sort) in binder {
                    sort.free_var_sorts_to_int();
                }
                expr.var_sorts_to_int();
            }
            Expr::WKVar(_) => {
                unimplemented!()
            }
        }
    }

    pub fn free_vars(&self) -> FxIndexSet<T::Var> {
        let mut vars = FxIndexSet::default();
        match self {
            Expr::Constant(_) | Expr::ThyFunc(_) => {}
            Expr::Var(x) => {
                vars.insert(x.clone());
            }
            Expr::App(func, _sort_args, args, _out_sort) => {
                vars.extend(func.free_vars());
                for arg in args {
                    vars.extend(arg.free_vars());
                }
            }
            Expr::Neg(e) | Expr::Not(e) => {
                vars = e.free_vars();
            }
            Expr::BinaryOp(_, exprs)
            | Expr::Imp(exprs)
            | Expr::Iff(exprs)
            | Expr::Atom(_, exprs) => {
                let [e1, e2] = &**exprs;
                vars.extend(e1.free_vars());
                vars.extend(e2.free_vars());
            }
            Expr::IfThenElse(exprs) => {
                let [p, e1, e2] = &**exprs;
                vars.extend(p.free_vars());
                vars.extend(e1.free_vars());
                vars.extend(e2.free_vars());
            }
            Expr::And(exprs) | Expr::Or(exprs) => {
                for e in exprs {
                    vars.extend(e.free_vars());
                }
            }
            Expr::Let(name, exprs) => {
                // Fixpoint only support one binder per let expressions, but it parses a singleton
                // list of binders to be forward-compatible
                let [var_e, body_e] = &**exprs;
                vars.extend(var_e.free_vars());
                let mut body_vars = body_e.free_vars();
                body_vars.swap_remove(name);
                vars.extend(body_vars);
            }
            Expr::IsCtor(_v, expr) => {
                // NOTE: (ck) I'm pretty sure this isn't a binder so I'm not going to
                // bother with `v`.
                vars.extend(expr.free_vars());
            }
            Expr::Quantifier(_, binder, expr) => {
                let mut inner = expr.free_vars();
                for (var, _sort) in binder {
                    inner.swap_remove(var);
                }
                vars.extend(inner);
            }
            Expr::WKVar(WKVar { wkvid: _, args }) => {
                for e in args {
                    vars.extend(e.free_vars());
                }
            }
        };
        vars
    }

    pub fn is_trivially_true(&self) -> bool {
        matches!(self, Expr::Constant(Constant::Boolean(true)))
    }

    pub fn substitute(&self, subst: &FxIndexMap<T::Var, Self>) -> Self {
        match self {
            Expr::Var(v) => subst.get(v).cloned().unwrap_or_else(|| self.clone()),
            Expr::Constant(_) | Expr::ThyFunc(_) => self.clone(),
            Expr::App(expr, sort_args, exprs, out_sort) => {
                Expr::App(
                    Box::new(expr.substitute(subst)),
                    sort_args.clone(),
                    exprs.iter().map(|e| e.substitute(subst)).collect_vec(),
                    out_sort.clone(),
                )
            }
            Expr::Neg(expr) => Expr::Neg(Box::new(expr.substitute(subst))),
            Expr::BinaryOp(bin_op, args) => {
                Expr::BinaryOp(
                    *bin_op,
                    Box::new([args[0].substitute(subst), args[1].substitute(subst)]),
                )
            }
            Expr::IfThenElse(args) => {
                Expr::IfThenElse(Box::new([
                    args[0].substitute(subst),
                    args[1].substitute(subst),
                    args[2].substitute(subst),
                ]))
            }
            Expr::And(exprs) => Expr::And(exprs.iter().map(|e| e.substitute(subst)).collect_vec()),
            Expr::Or(exprs) => Expr::Or(exprs.iter().map(|e| e.substitute(subst)).collect_vec()),
            Expr::Not(expr) => Expr::Not(Box::new(expr.substitute(subst))),
            Expr::Imp(args) => {
                Expr::Imp(Box::new([args[0].substitute(subst), args[1].substitute(subst)]))
            }
            Expr::Iff(args) => {
                Expr::Iff(Box::new([args[0].substitute(subst), args[1].substitute(subst)]))
            }
            Expr::Atom(bin_rel, args) => {
                Expr::Atom(
                    *bin_rel,
                    Box::new([args[0].substitute(subst), args[1].substitute(subst)]),
                )
            }
            Expr::Let(var, args) => {
                Expr::Let(
                    var.clone(),
                    Box::new([args[0].substitute(subst), args[1].substitute(subst)]),
                )
            }
            Expr::IsCtor(var, expr) => Expr::IsCtor(var.clone(), Box::new(expr.substitute(subst))),
            Expr::Quantifier(q, sorts, expr) => {
                Expr::Quantifier(*q, sorts.clone(), Box::new(expr.substitute(subst)))
            }
            Expr::WKVar(WKVar { wkvid, args }) => {
                Expr::WKVar(WKVar {
                    wkvid: wkvid.clone(),
                    args: args.iter().map(|e| e.substitute(subst)).collect_vec(),
                })
            }
        }
    }

    // Give all the weak kvars that appear as part of a top-level conjunction.
    // This is a syntactic analysis.
    pub fn wkvars_in_conj(&self) -> Vec<WKVar<T>> {
        match self {
            Expr::WKVar(wkvar) => vec![wkvar.clone()],
            Expr::And(conj) => conj.iter().flat_map(|e| e.wkvars_in_conj()).collect(),
            _ => vec![],
        }
    }

    pub fn uncurry(&self) -> Self {
        match self {
            Expr::App(head, sort_args, args, out_sort) => {
                let uncurried_head = head.uncurry();
                let uncurried_args = args.iter().map(Expr::uncurry).collect_vec();
                match uncurried_head {
                    Expr::App(head_head, head_sort_args, mut head_args, _) => {
                        head_args.extend(uncurried_args);
                        let sort_args = match (head_sort_args, sort_args) {
                            (Some(mut head_sort_args), Some(sort_args)) => {
                                head_sort_args.extend(sort_args.clone());
                                Some(head_sort_args)
                            }
                            _ => None,
                        };
                        Expr::App(head_head, sort_args, head_args, out_sort.clone())
                    }
                    Expr::WKVar(WKVar { wkvid, args: mut wkvar_args }) => {
                        wkvar_args.extend(uncurried_args);
                        Expr::WKVar(WKVar { wkvid, args: wkvar_args })
                    }
                    head => {
                        Expr::App(
                            Box::new(head),
                            sort_args.clone(),
                            uncurried_args,
                            out_sort.clone(),
                        )
                    }
                }
            }
            Expr::Constant(_) | Expr::Var(_) | Expr::ThyFunc(_) => self.clone(),
            Expr::Neg(expr) => Expr::Neg(Box::new(expr.uncurry())),
            Expr::BinaryOp(bin_op, args) => {
                Expr::BinaryOp(*bin_op, Box::new([args[0].uncurry(), args[1].uncurry()]))
            }
            Expr::IfThenElse(args) => {
                Expr::IfThenElse(Box::new([
                    args[0].uncurry(),
                    args[1].uncurry(),
                    args[2].uncurry(),
                ]))
            }
            Expr::And(exprs) => Expr::And(exprs.iter().map(Expr::uncurry).collect_vec()),
            Expr::Or(exprs) => Expr::Or(exprs.iter().map(Expr::uncurry).collect_vec()),
            Expr::Not(expr) => Expr::Not(Box::new(expr.uncurry())),
            Expr::Imp(args) => Expr::Imp(Box::new([args[0].uncurry(), args[1].uncurry()])),
            Expr::Iff(args) => Expr::Iff(Box::new([args[0].uncurry(), args[1].uncurry()])),
            Expr::Atom(bin_rel, args) => {
                Expr::Atom(*bin_rel, Box::new([args[0].uncurry(), args[1].uncurry()]))
            }
            Expr::Let(var, args) => {
                Expr::Let(var.clone(), Box::new([args[0].uncurry(), args[1].uncurry()]))
            }
            Expr::IsCtor(var, expr) => Expr::IsCtor(var.clone(), Box::new(expr.uncurry())),
            Expr::Quantifier(q, sorts, expr) => {
                Expr::Quantifier(*q, sorts.clone(), Box::new(expr.uncurry()))
            }
            Expr::WKVar(WKVar { wkvid, args }) => {
                Expr::WKVar(WKVar {
                    wkvid: wkvid.clone(),
                    args: args.iter().map(|e| e.uncurry()).collect_vec(),
                })
            }
        }
    }

    pub fn has_wkvar_reachable_by_split(&self) -> bool {
        if !matches!(self, Expr::Quantifier(Quantifier::Exists, ..) | Expr::Or(..) | Expr::And(..))
        {
            return false;
        }
        match self {
            Expr::Or(exprs) => {
                exprs.iter().any(|expr| {
                    matches!(expr, Expr::WKVar(..)) || expr.has_wkvar_reachable_by_split()
                })
            }
            Expr::Quantifier(Quantifier::Exists, _sorts, expr) => {
                !expr.wkvars_in_conj().is_empty() || expr.has_wkvar_reachable_by_split()
            }
            Expr::And(exprs) => exprs.iter().any(Expr::has_wkvar_reachable_by_split),
            _ => false,
        }
    }

    pub fn hoist_exists(&self) -> (Vec<VarSorts<T>>, Expr<T>) {
        match self {
            Expr::Quantifier(Quantifier::Exists, var_sorts, inner_e) => {
                let mut vars = var_sorts.clone();
                let (new_vars, hoisted_inner) = inner_e.hoist_exists();
                vars.extend(new_vars);
                (vars, hoisted_inner)
            }
            Expr::And(exprs) => {
                let mut vars = vec![];
                let expr = Expr::And(
                    exprs
                        .iter()
                        .flat_map(|expr| {
                            let (new_vars, hoisted_expr) = expr.hoist_exists();
                            vars.extend(new_vars);
                            match hoisted_expr {
                                Expr::And(exprs) => exprs,
                                expr => vec![expr],
                            }
                        })
                        .collect(),
                );
                (vars, expr)
            }
            _ => (vec![], self.clone()),
        }
    }

    pub fn as_conjunction(self) -> Vec<Self> {
        match self {
            Expr::And(exprs) => exprs,
            expr => vec![expr],
        }
    }

    pub fn strip_wkvars(&self) -> Self {
        match self {
            Expr::Constant(_) | Expr::Var(_) | Expr::ThyFunc(_) => self.clone(),
            Expr::WKVar(..) => Expr::TRUE,
            Expr::App(head, sort_args, args, out_sort) => {
                Expr::App(
                    Box::new(head.strip_wkvars()),
                    sort_args.clone(),
                    args.iter().map(Expr::strip_wkvars).collect(),
                    out_sort.clone(),
                )
            }
            Expr::Neg(expr) => Expr::Neg(Box::new(expr.strip_wkvars())),
            Expr::BinaryOp(bin_op, args) => {
                Expr::BinaryOp(*bin_op, Box::new([args[0].strip_wkvars(), args[1].strip_wkvars()]))
            }
            Expr::IfThenElse(args) => {
                Expr::IfThenElse(Box::new([
                    args[0].strip_wkvars(),
                    args[1].strip_wkvars(),
                    args[2].strip_wkvars(),
                ]))
            }
            Expr::And(exprs) => Expr::And(exprs.iter().map(Expr::strip_wkvars).collect_vec()),
            Expr::Or(exprs) => Expr::Or(exprs.iter().map(Expr::strip_wkvars).collect_vec()),
            Expr::Not(expr) => Expr::Not(Box::new(expr.strip_wkvars())),
            Expr::Imp(args) => {
                Expr::Imp(Box::new([args[0].strip_wkvars(), args[1].strip_wkvars()]))
            }
            Expr::Iff(args) => {
                Expr::Iff(Box::new([args[0].strip_wkvars(), args[1].strip_wkvars()]))
            }
            Expr::Atom(bin_rel, args) => {
                Expr::Atom(*bin_rel, Box::new([args[0].strip_wkvars(), args[1].strip_wkvars()]))
            }
            Expr::Let(var, args) => {
                Expr::Let(var.clone(), Box::new([args[0].strip_wkvars(), args[1].strip_wkvars()]))
            }
            Expr::IsCtor(var, expr) => Expr::IsCtor(var.clone(), Box::new(expr.strip_wkvars())),
            Expr::Quantifier(q, sorts, expr) => {
                Expr::Quantifier(*q, sorts.clone(), Box::new(expr.strip_wkvars()))
            }
        }
    }

    pub fn total_num_disjuncts(&self) -> usize {
        match self {
            Expr::Or(disjuncts) => {
                disjuncts.len()
                    + disjuncts
                        .iter()
                        .map(Expr::total_num_disjuncts)
                        .sum::<usize>()
            }
            Expr::And(conjuncts) => conjuncts.iter().map(Expr::total_num_disjuncts).sum(),
            _ => 0,
        }
    }
}

#[derive_where(PartialEq, Eq, Hash, Clone, Debug)]
pub enum Constant<T: Types> {
    Numeral(u128),
    Real(T::Real),
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

#[derive(Clone, Debug, Copy, PartialEq, Eq, Hash)]
pub enum Quantifier {
    Exists,
    Forall,
}
