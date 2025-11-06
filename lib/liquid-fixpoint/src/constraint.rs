use std::{collections::HashSet, hash::Hash};

use derive_where::derive_where;
use itertools::Itertools;

use crate::{ConstDecl, ThyFunc, Types};

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
    /// Returns the number of concrete, non-trivial head predicates in the constraint.
    pub fn concrete_head_count(&self) -> usize {
        fn go<T: Types>(c: &Constraint<T>, count: &mut usize) {
            match c {
                Constraint::Conj(cs) => cs.iter().for_each(|c| go(c, count)),
                Constraint::ForAll(_, c) => go(c, count),
                Constraint::Pred(p, _) => {
                    if p.is_concrete() && !p.is_trivially_true() {
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
    /// Because this function is generic, it is your responsibility to filter
    /// out UNDERSCORE binders (although it isn't strictly wrong to keep them
    /// in).
    ///
    /// NOTE: Assumes and requires that all binder names are unique, i.e.
    /// there is no shadowing (it is OK to have multiple binders of the same
    /// name so long as they never are used, e.g. UNDERSCORE).
    pub fn flatten(&self) -> Vec<FlatConstraint<T>> {
        match self {
            Constraint::Pred(pred, tag) => {
                vec![FlatConstraint {
                    binders: vec![],
                    assumptions: vec![],
                    head: pred.clone(),
                    tag: tag.clone(),
                }]
            }
            Constraint::Conj(constrs) => {
                constrs.iter().flat_map(|constr| constr.flatten()).collect_vec()
            }
            Constraint::ForAll(bind, constr) => {
                let mut flat_constrs = constr.flatten();
                for constr in &mut flat_constrs {
                    constr.binders.push((bind.name.clone(), bind.sort.clone()));
                    constr.assumptions.extend(bind.pred.as_conjunction())
                }
                flat_constrs
            }
        }
    }
}

#[derive_where(Hash, Clone, Debug)]
pub struct FlatConstraint<T: Types> {
    /// All of the binders that come before the head.
    ///
    /// NOTE: There should be no duplicates among the binders which are used (so
    /// e.g. UNDERSCORE appearing multiple times is OK).
    pub binders: Vec<(T::Var, Sort<T>)>,
    /// All of the assumptions (i.e. a flattened conjunction of predicates from
    /// all of the binders)
    pub assumptions: Vec<Pred<T>>,
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
    pub fn remove_binders(&self, vars: HashSet<T::Var>) -> (Vec<ConstDecl<T>>, FlatConstraint<T>) {
        let mut new_binders = self.binders.clone();
        let removed_binders = new_binders.extract_if(.., |(var, _sort)| vars.contains(var)).map(|(var, sort)| {
            ConstDecl {
                name: var,
                sort,
                comment: None,
            }
        }).collect_vec();
        let new_constraint = FlatConstraint {
            binders: new_binders,
            assumptions: self.assumptions.clone(),
            head: self.head.clone(),
            tag: self.tag.clone(),
        };
        (removed_binders, new_constraint)
    }

    /// Turn this back into a constraint
    pub fn into_constraint(&self, underscore_var: T::Var) -> Constraint<T> {
        let head_constr = Constraint::Pred(self.head.clone(), self.tag.clone());
        let mut constr = Constraint::ForAll(Bind {
            name: underscore_var.clone(),
            sort: Sort::Int,
            pred: Pred::And(self.assumptions.clone()),
        }, Box::new(head_constr));

        for (var, sort) in &self.binders {
            constr = Constraint::ForAll(Bind {
                name: var.clone(),
                sort: sort.clone(),
                pred: Pred::TRUE,
            }, Box::new(constr));
        }
        constr
    }
}

#[derive_where(Hash, Clone)]
pub struct DataDecl<T: Types> {
    pub name: T::Sort,
    pub vars: usize,
    pub ctors: Vec<DataCtor<T>>,
}

#[derive_where(Hash, Clone)]
pub struct SortDecl<T: Types> {
    pub name: T::Sort,
    pub vars: usize,
}

#[derive_where(Hash, Clone)]
pub struct DataCtor<T: Types> {
    pub name: T::Var,
    pub fields: Vec<DataField<T>>,
}

#[derive_where(Hash, Clone)]
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
        if preds.is_empty() {
            Pred::TRUE
        } else if preds.len() == 1 {
            preds.remove(0)
        } else {
            Self::And(preds)
        }
    }

    pub fn is_trivially_true(&self) -> bool {
        match self {
            Pred::Expr(Expr::Constant(Constant::Boolean(true))) => true,
            // FIXME: We do substitue true for wkvars, but is this correct?
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

    #[cfg(feature = "rust-fixpoint")]
    pub(crate) fn simplify(&mut self) {
        if let Pred::And(conjuncts) = self {
            if conjuncts.is_empty() {
                *self = Pred::TRUE;
            } else if conjuncts.len() == 1 {
                *self = conjuncts[0].clone();
            } else {
                conjuncts.iter_mut().for_each(|pred| pred.simplify());
            }
        }
    }

    /// Returns a Vec of Preds whose conjunction is equal to the original Pred.
    ///
    /// This trusts that Pred::Expr(BinOp(BinOp::And, ...) is not possible ---
    /// i.e. Preds are always converted to Pred::And if possible.
    pub fn as_conjunction(&self) -> Vec<Self> {
        match self {
            Pred::And(conjs) => conjs.clone(),
            _ => vec![self.clone()],
        }
    }

    pub fn free_vars(&self) -> HashSet<T::Var> {
        match self {
            Pred::KVar(..) => HashSet::new(),
            Pred::And(preds) => {
                preds.iter().flat_map(|pred| pred.free_vars()).collect()
            }
            Pred::Expr(expr) => {
                expr.free_vars()
            }
        }
    }

    pub fn has_kvar(&self) -> bool {
        match self {
            Pred::KVar(..) => true,
            Pred::And(preds) => preds.iter().any(|pred| pred.has_kvar()),
            _ => false,
        }
    }

    // Give all the weak kvars that appear as part of a top-level conjunction.
    // This is a syntactic analysis.
    pub fn wkvars_in_conj(&self) -> Vec<WKVar<T>> {
        match self {
            Pred::And(preds) => preds.iter().flat_map(|pred| pred.wkvars_in_conj()).collect(),
            Pred::Expr(e) => e.wkvars_in_conj(),
            Pred::KVar(..) => vec![],
        }
    }

    /// Remove all wkvars, replacing them with true.
    pub fn strip_wkvars(&self) -> Self {
        match self {
            Pred::And(preds) => Pred::And(preds.iter().map(|pred| pred.strip_wkvars()).collect()),
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

#[derive(Hash, Debug, Copy, Clone, PartialEq, Eq)]
pub struct BoundVar {
    pub level: usize,
    pub idx: usize,
}

impl BoundVar {
    pub fn new(level: usize, idx: usize) -> Self {
        Self { level, idx }
    }
}

#[derive_where(Hash, Debug, Clone)]
pub struct WKVar<T: Types> {
    pub wkvid: T::Var,
    pub args: Vec<Expr<T>>,
}

#[derive_where(Hash, Clone, Debug)]
pub enum Expr<T: Types> {
    Constant(Constant<T>),
    Var(T::Var),
    // This is kept separate from [`T::Var`] because we need to always support
    // having bound variables for [`Expr::Exists`]. We reuse these as well
    // for kvar solutions, which is a bit of a hack.
    BoundVar(BoundVar),
    App(Box<Self>, Option<Vec<Sort<T>>>, Vec<Self>),
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
    Exists(Vec<Sort<T>>, Box<Self>),
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
    pub const fn int(val: u128) -> Expr<T> {
        Expr::Constant(Constant::Numeral(val))
    }

    pub fn eq(self, other: Self) -> Self {
        Expr::Atom(BinRel::Eq, Box::new([self, other]))
    }

    pub fn and(mut exprs: Vec<Self>) -> Self {
        if exprs.len() == 1 { exprs.remove(0) } else { Self::And(exprs) }
    }

    pub fn free_vars(&self) -> HashSet<T::Var> {
        let mut vars = HashSet::new();
        match self {
            Expr::Constant(_) | Expr::ThyFunc(_) | Expr::BoundVar { .. } => {}
            Expr::Var(x) => {
                vars.insert(x.clone());
            }
            Expr::App(func, _sort_args, args) => {
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
                body_vars.remove(name);
                vars.extend(body_vars);
            }
            Expr::IsCtor(_v, expr) => {
                // NOTE: (ck) I'm pretty sure this isn't a binder so I'm not going to
                // bother with `v`.
                vars.extend(expr.free_vars());
            }
            Expr::Exists(_sorts, expr) => {
                // NOTE: (ck) No variable names here so it seems this is nameless.
                vars.extend(expr.free_vars());
            }
            Expr::WKVar(WKVar { wkvid: _, args }) => {
                for e in args {
                    vars.extend(e.free_vars());
                }
            }
        };
        vars
    }

    pub fn substitute_bvar(&self, subst_layer: &[Expr<T>], current_level: usize) -> Self {
        match self {
            Expr::Constant(_) | Expr::Var(_) | Expr::ThyFunc(_) => self.clone(),
            Expr::BoundVar(bound_var) => {
                if bound_var.level == current_level
                    && let Some(subst) = subst_layer.get(bound_var.idx)
                {
                    subst.clone()
                } else {
                    self.clone()
                }
            }
            Expr::App(expr, sort_args, exprs) => {
                Expr::App(
                    Box::new(expr.substitute_bvar(subst_layer, current_level)),
                    sort_args.clone(),
                    exprs
                        .iter()
                        .map(|e| e.substitute_bvar(subst_layer, current_level))
                        .collect_vec(),
                )
            }
            Expr::Neg(expr) => {
                Expr::Neg(Box::new(expr.substitute_bvar(subst_layer, current_level)))
            }
            Expr::BinaryOp(bin_op, args) => {
                Expr::BinaryOp(
                    *bin_op,
                    Box::new([
                        args[0].substitute_bvar(subst_layer, current_level),
                        args[1].substitute_bvar(subst_layer, current_level),
                    ]),
                )
            }
            Expr::IfThenElse(args) => {
                Expr::IfThenElse(Box::new([
                    args[0].substitute_bvar(subst_layer, current_level),
                    args[1].substitute_bvar(subst_layer, current_level),
                    args[2].substitute_bvar(subst_layer, current_level),
                ]))
            }
            Expr::And(exprs) => {
                Expr::And(
                    exprs
                        .iter()
                        .map(|e| e.substitute_bvar(subst_layer, current_level))
                        .collect_vec(),
                )
            }
            Expr::Or(exprs) => {
                Expr::Or(
                    exprs
                        .iter()
                        .map(|e| e.substitute_bvar(subst_layer, current_level))
                        .collect_vec(),
                )
            }
            Expr::Not(expr) => {
                Expr::Not(Box::new(expr.substitute_bvar(subst_layer, current_level)))
            }
            Expr::Imp(args) => {
                Expr::Imp(Box::new([
                    args[0].substitute_bvar(subst_layer, current_level),
                    args[1].substitute_bvar(subst_layer, current_level),
                ]))
            }
            Expr::Iff(args) => {
                Expr::Iff(Box::new([
                    args[0].substitute_bvar(subst_layer, current_level),
                    args[1].substitute_bvar(subst_layer, current_level),
                ]))
            }
            Expr::Atom(bin_rel, args) => {
                Expr::Atom(
                    *bin_rel,
                    Box::new([
                        args[0].substitute_bvar(subst_layer, current_level),
                        args[1].substitute_bvar(subst_layer, current_level),
                    ]),
                )
            }
            Expr::Let(var, args) => {
                Expr::Let(
                    var.clone(),
                    Box::new([
                        args[0].substitute_bvar(subst_layer, current_level),
                        args[1].substitute_bvar(subst_layer, current_level),
                    ]),
                )
            }
            Expr::IsCtor(var, expr) => {
                Expr::IsCtor(
                    var.clone(),
                    Box::new(expr.substitute_bvar(subst_layer, current_level)),
                )
            }
            Expr::Exists(sorts, expr) => {
                Expr::Exists(
                    sorts.clone(),
                    Box::new(expr.substitute_bvar(subst_layer, current_level + 1)),
                )
            }
            Expr::WKVar(WKVar { wkvid, args }) => {
                Expr::WKVar(WKVar {
                    wkvid: wkvid.clone(),
                    args: args
                        .iter()
                        .map(|e| e.substitute_bvar(subst_layer, current_level))
                        .collect_vec(),
                })
            }
        }
    }

    pub fn disjunctions(&self) -> Vec<Expr<T>> {
        match self {
            Expr::Or(disjuncts) => disjuncts.clone(),
            _ => vec![self.clone()]
        }
    }

    pub fn conjunctions(&self) -> Vec<Expr<T>> {
        match self {
            Expr::And(conjuncts) => conjuncts.clone(),
            _ => vec![self.clone()]
        }
    }

    // Give all the weak kvars that appear as part of a top-level conjunction.
    // This is a syntactic analysis.
    pub fn wkvars_in_conj(&self) -> Vec<WKVar<T>> {
        match self {
            Expr::WKVar(wkvar) => vec![wkvar.clone()],
            Expr::And(conj) => {
                conj.iter().flat_map(|e| {
                    e.wkvars_in_conj()
                }).collect()
            }
            _ => vec![]
        }
    }

    pub fn uncurry(&self) -> Self {
        match self {
            Expr::App(head, sort_args, args) => {
                        let uncurried_head = head.uncurry();
                        let uncurried_args = args.iter().map(|arg| arg.uncurry()).collect_vec();
                        match uncurried_head {
                            Expr::App(head_head, head_sort_args, mut head_args) => {
                                head_args.extend(uncurried_args);
                                let new_sort_args = match (head_sort_args, sort_args) {
                                    (Some(mut head_sort_args), Some(sort_args)) => {
                                        head_sort_args.extend(sort_args.clone());
                                        Some(head_sort_args)
                                    }
                                    _ => {
                                        None
                                    }
                                };
                                Expr::App(head_head, new_sort_args, head_args)
                            }
                            Expr::WKVar(WKVar {wkvid, args: mut wkvar_args}) => {
                                wkvar_args.extend(uncurried_args);
                                Expr::WKVar(WKVar {wkvid, args: wkvar_args})
                            }
                            _ => {
                                Expr::App(Box::new(uncurried_head), sort_args.clone(), uncurried_args)
                            }
                        }
                    }
            Expr::Constant(_) | Expr::Var(_) | Expr::BoundVar(_)
                | Expr::ThyFunc(_) => self.clone(),
            Expr::Neg(expr) => {
                Expr::Neg(Box::new(expr.uncurry()))
            }
            Expr::BinaryOp(bin_op, args) => {
                Expr::BinaryOp(
                    *bin_op,
                    Box::new([
                        args[0].uncurry(),
                        args[1].uncurry(),
                    ]),
                )
            }
            Expr::IfThenElse(args) => {
                Expr::IfThenElse(Box::new([
                    args[0].uncurry(),
                    args[1].uncurry(),
                    args[2].uncurry(),
                ]))
            }
            Expr::And(exprs) => {
                Expr::And(
                    exprs
                        .iter()
                        .map(|e| e.uncurry())
                        .collect_vec(),
                )
            }
            Expr::Or(exprs) => {
                Expr::Or(
                    exprs
                        .iter()
                        .map(|e| e.uncurry())
                        .collect_vec(),
                )
            }
            Expr::Not(expr) => {
                Expr::Not(Box::new(expr.uncurry()))
            }
            Expr::Imp(args) => {
                Expr::Imp(Box::new([
                    args[0].uncurry(),
                    args[1].uncurry(),
                ]))
            }
            Expr::Iff(args) => {
                Expr::Iff(Box::new([
                    args[0].uncurry(),
                    args[1].uncurry(),
                ]))
            }
            Expr::Atom(bin_rel, args) => {
                Expr::Atom(
                    *bin_rel,
                    Box::new([
                        args[0].uncurry(),
                        args[1].uncurry(),
                    ]),
                )
            }
            Expr::Let(var, args) => {
                Expr::Let(
                    var.clone(),
                    Box::new([
                        args[0].uncurry(),
                        args[1].uncurry(),
                    ]),
                )
            }
            Expr::IsCtor(var, expr) => {
                Expr::IsCtor(
                    var.clone(),
                    Box::new(expr.uncurry()),
                )
            }
            Expr::Exists(sorts, expr) => {
                Expr::Exists(
                    sorts.clone(),
                    Box::new(expr.uncurry()),
                )
            }
            Expr::WKVar(WKVar { wkvid, args }) => {
                Expr::WKVar(WKVar {
                    wkvid: wkvid.clone(),
                    args: args
                        .iter()
                        .map(|e| e.uncurry())
                        .collect_vec(),
                })
            }
        }
    }

    /// Are there any weak kvars that are
    ///
    /// 1. Behind an exists
    /// 2. In a disjunction
    ///
    /// which if we removed either (or both),
    /// we would be able to access.
    ///
    /// NOTE: Does not handle cases where the weak
    /// kvar is behind an exists in a conjunction, e.g.
    ///
    ///     x == 1
    ///     && y == 2
    ///     && exists z. $wk0(x, y, z)
    ///
    /// Maybe the correct solution is to hoist all exists
    /// that we can and _then_ check for reachable weak kvars.
    pub fn has_wkvar_reachable_by_split(&self) -> bool {
        if !matches!(self, Expr::Exists(..) | Expr::Or(..)) {
            return false;
        }
        match self.skip_exists() {
            Expr::Or(exprs) => {
                exprs.iter().any(|expr| !expr.skip_exists().wkvars_in_conj().is_empty())
            }
            _ => !self.wkvars_in_conj().is_empty(),
        }
    }

    pub fn skip_exists(&self) -> &Self {
        match self {
            Expr::Exists(_, e) => e.skip_exists(),
            e => e,
        }
    }

    pub fn hoist_exists<F>(&self, fresh_var: &mut F) -> (Vec<(T::Var, Sort<T>)>, Expr<T>)
        where F: FnMut() -> T::Var
    {
        match self {
            Expr::Exists(sorts, inner_e) => {
                // These will have the vars and sorts.
                let mut vars = vec![];
                // These are just the vars wrapped in exprs.
                let mut subst_exprs = vec![];
                for sort in sorts {
                    let var = fresh_var();
                    let fresh_expr = Expr::Var(var.clone());
                    vars.push((var, sort.clone()));
                    subst_exprs.push(fresh_expr);
                }
                let subst_inner = inner_e.substitute_bvar(&subst_exprs, 0);
                let (new_vars, hoisted_inner) = subst_inner.hoist_exists(fresh_var);
                vars.extend(new_vars);
                (vars, hoisted_inner)
            }
            Expr::And(exprs) => {
                let mut vars = vec![];
                let hoisted_e = Expr::And(
                    exprs.iter().flat_map(|expr| {
                        let (new_vars, hoisted_e) = expr.hoist_exists(fresh_var);
                        vars.extend(new_vars);
                        // Flatten any conjunctions
                        match hoisted_e {
                            Expr::And(exprs) => exprs,
                            hoisted_e => vec![hoisted_e],
                        }
                    }).collect()
                );
                (vars, hoisted_e)
            }
            _ => (vec![], self.clone())
        }
    }

    pub fn as_conjunction(self) -> Vec<Self> {
        match self {
            Expr::And(exprs) => exprs,
            _ => vec![self]
        }
    }

    pub fn strip_wkvars(&self) -> Self {
        match self {
            Expr::Constant(_) | Expr::Var(_) | Expr::BoundVar(_)
                | Expr::ThyFunc(_) => self.clone(),
            Expr::WKVar(..) => {
                Expr::Constant(Constant::Boolean(true))
            }
            Expr::App(head, args) => {
                Expr::App(Box::new(head.strip_wkvars()), args.iter().map(|arg| arg.strip_wkvars()).collect())
            }
            Expr::Neg(expr) => {
                Expr::Neg(Box::new(expr.strip_wkvars()))
            }
            Expr::BinaryOp(bin_op, args) => {
                Expr::BinaryOp(
                    *bin_op,
                    Box::new([
                        args[0].strip_wkvars(),
                        args[1].strip_wkvars(),
                    ]),
                )
            }
            Expr::IfThenElse(args) => {
                Expr::IfThenElse(Box::new([
                    args[0].strip_wkvars(),
                    args[1].strip_wkvars(),
                    args[2].strip_wkvars(),
                ]))
            }
            Expr::And(exprs) => {
                Expr::And(
                    exprs
                        .iter()
                        .map(|e| e.strip_wkvars())
                        .collect_vec(),
                )
            }
            Expr::Or(exprs) => {
                Expr::Or(
                    exprs
                        .iter()
                        .map(|e| e.strip_wkvars())
                        .collect_vec(),
                )
            }
            Expr::Not(expr) => {
                Expr::Not(Box::new(expr.strip_wkvars()))
            }
            Expr::Imp(args) => {
                Expr::Imp(Box::new([
                    args[0].strip_wkvars(),
                    args[1].strip_wkvars(),
                ]))
            }
            Expr::Iff(args) => {
                Expr::Iff(Box::new([
                    args[0].strip_wkvars(),
                    args[1].strip_wkvars(),
                ]))
            }
            Expr::Atom(bin_rel, args) => {
                Expr::Atom(
                    *bin_rel,
                    Box::new([
                        args[0].strip_wkvars(),
                        args[1].strip_wkvars(),
                    ]),
                )
            }
            Expr::Let(var, args) => {
                Expr::Let(
                    var.clone(),
                    Box::new([
                        args[0].strip_wkvars(),
                        args[1].strip_wkvars(),
                    ]),
                )
            }
            Expr::IsCtor(var, expr) => {
                Expr::IsCtor(
                    var.clone(),
                    Box::new(expr.strip_wkvars()),
                )
            }
            Expr::Exists(sorts, expr) => {
                Expr::Exists(
                    sorts.clone(),
                    Box::new(expr.strip_wkvars()),
                )
            }
        }
    }
}

#[derive_where(Hash, Clone, Debug)]
pub enum Constant<T: Types> {
    Numeral(u128),
    // Currently we only support parsing integers as decimals. We should extend this to allow
    // rational numbers as a numer/denom.
    //
    // NOTE: If this type is updated, then update parse_expr in the parser
    // (see the unimplemented!() related to float parsing).
    Real(u128),
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
