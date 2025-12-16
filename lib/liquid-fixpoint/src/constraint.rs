use std::{collections::HashSet, hash::Hash};

use derive_where::derive_where;
use itertools::Itertools;

use crate::{ThyFunc, Types};

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
    /// When translating to `Fixpoint`, the arguments should always be `Expr::Var`.
    KVar(T::KVar, Vec<Expr<T>>),
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
