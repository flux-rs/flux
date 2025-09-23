use std::{collections::HashSet, hash::Hash, vec};

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
    pub fn is_concrete(&self) -> bool {
        match self {
            Constraint::Conj(cs) => cs.iter().any(Constraint::is_concrete),
            Constraint::ForAll(_, c) => c.is_concrete(),
            Constraint::Pred(p, _) => p.is_concrete() && !p.is_trivially_true(),
        }
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
    binders: Vec<(T::Var, Sort<T>)>,
    /// All of the assumptions (i.e. a flattened conjunction of predicates from
    /// all of the binders)
    assumptions: Vec<Pred<T>>,
    head: Pred<T>,
    #[derive_where(skip)]
    tag: Option<T::Tag>,
}

impl<T: Types> FlatConstraint<T> {
    /// Removes any binder corresponding to a given var. Returns the new
    /// constraint along with the removed binders and their sorts.
    ///
    /// NOTE: Assumes that all binders are unique and therefore there are no
    /// name clashes.
    pub fn remove_binders(&self, vars: HashSet<T::Var>) -> (Vec<(T::Var, Sort<T>)>, FlatConstraint<T>) {
        let mut new_binders = self.binders.clone();
        let removed_binders = new_binders.extract_if(.., |(var, _sort)| vars.contains(var)).collect_vec();
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
    /// NOTE: WKVars are for internal use and we will serialize them as TRUE.
    ///
    /// In an ideal world we would serialize them too and fixpoint would ignore
    /// them.
    WKVar(T::WKVar),
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
            // FIXME: We do substitue true for wkvars, but is this correct?
            Pred::WKVar(_) => true,
            Pred::And(ps) => ps.is_empty(),
            _ => false,
        }
    }

    pub fn is_concrete(&self) -> bool {
        match self {
            Pred::And(ps) => ps.iter().any(Pred::is_concrete),
            Pred::KVar(_, _) => false,
            Pred::WKVar(_) => false,
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
            Pred::KVar(..) | Pred::WKVar(..) => HashSet::new(),
            Pred::And(preds) => {
                preds.iter().flat_map(|pred| pred.free_vars()).collect()
            }
            Pred::Expr(expr) => {
                expr.free_vars()
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
    ThyFunc(ThyFunc),
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
            Expr::Constant(_) | Expr::ThyFunc(_) => {}
            Expr::Var(x) => {
                vars.insert(x.clone());
            }
            Expr::App(func, args) => {
                vars.extend(func.free_vars().into_iter());
                for arg in args {
                    vars.extend(arg.free_vars().into_iter());
                }
            }
            Expr::Neg(e) | Expr::Not(e) => {
                vars = e.free_vars();
            }
            Expr::BinaryOp(_, exprs) | Expr::Imp(exprs) | Expr::Iff(exprs) | Expr::Atom(_, exprs) => {
                let [e1, e2] = &**exprs;
                vars.extend(e1.free_vars().into_iter());
                vars.extend(e2.free_vars().into_iter());
            }
            Expr::IfThenElse(exprs) => {
                let [p, e1, e2] = &**exprs;
                vars.extend(p.free_vars().into_iter());
                vars.extend(e1.free_vars().into_iter());
                vars.extend(e2.free_vars().into_iter());
            }
            Expr::And(exprs) | Expr::Or(exprs) => {
                for e in exprs {
                    vars.extend(e.free_vars().into_iter());
                }
            }
            Expr::Let(name, exprs) => {
                // Fixpoint only support one binder per let expressions, but it parses a singleton
                // list of binders to be forward-compatible
                let [var_e, body_e] = &**exprs;
                vars.extend(var_e.free_vars().into_iter());
                let mut body_vars = body_e.free_vars();
                body_vars.remove(name);
                vars.extend(body_vars.into_iter());
            }
        };
        vars
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
