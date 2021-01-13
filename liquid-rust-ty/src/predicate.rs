use crate::{
    literal::Literal,
    local::LocalVariable,
    op::{BinOp, UnOp},
    variable::Variable,
    BaseTy,
};

use liquid_rust_common::new_index;

use std::{fmt, ops::BitAnd};

new_index! {
    #[derive(Clone, Copy, Debug)]
    HoleId
}

/// A quantifier-free predicate.
#[derive(Clone, Debug)]
pub enum Predicate<V = LocalVariable> {
    /// A literal.
    Lit(Literal),
    /// A variable.
    Var(Variable<V>),
    /// An unary operation between predicates.
    UnaryOp(UnOp, Box<Self>),
    /// A binary operation between predicates.
    BinaryOp(BinOp, Box<Self>, Box<Self>),
    /// A predicate to be inferred.
    Hole(HoleId),
}

impl Predicate {
    pub(crate) fn replace_variable(&mut self, target: LocalVariable, subst: LocalVariable) {
        match self {
            Self::Lit(_) | Self::Hole(_) => (),
            Self::Var(var) => match var {
                Variable::Bound | Variable::Arg(_) => (),
                Variable::Local(local_var) => {
                    if target == *local_var {
                        *local_var = subst;
                    }
                }
            },
            Self::UnaryOp(_, op) => op.replace_variable(target, subst),
            Self::BinaryOp(_, op1, op2) => {
                op1.replace_variable(target, subst);
                op2.replace_variable(target, subst);
            }
        }
    }
}

impl<V> Predicate<V> {
    /// Map the local variables inside the predicate to produce a new predicate.
    ///
    /// This is used by the `tycheck` crate when emitting constrains to map every local variable to
    /// a globally unique variable.
    pub fn map<W>(self, f: impl Fn(V) -> W + Copy) -> Predicate<W> {
        match self {
            Self::Lit(literal) => Predicate::Lit(literal),
            Self::Var(variable) => Predicate::Var(match variable {
                Variable::Bound => Variable::Bound,
                Variable::Local(var) => Variable::Local(f(var)),
                Variable::Arg(_) => unreachable!(),
            }),
            Self::UnaryOp(un_op, op) => Predicate::UnaryOp(un_op, Box::new(op.map(f))),
            Self::BinaryOp(bin_op, op1, op2) => {
                Predicate::BinaryOp(bin_op, Box::new(op1.map(f)), Box::new(op2.map(f)))
            }
            Self::Hole(hole_id) => Predicate::Hole(hole_id),
        }
    }

    /// Produce a new predicate by comparing two predicates using the equality operation.
    ///
    /// Comparing predicates that do not match the base type in this function's parameter is
    /// unsound.
    pub fn eq(self, base_ty: BaseTy, rhs: impl Into<Self>) -> Self {
        Self::BinaryOp(BinOp::Eq(base_ty), Box::new(self), Box::new(rhs.into()))
    }
    /// Produce a new predicate by comparing two predicates using the "not equal to" operation.
    ///
    /// Comparing predicates that do not match the base type in this function's parameter is
    /// unsound.
    pub fn neq(self, base_ty: BaseTy, rhs: impl Into<Self>) -> Self {
        Self::BinaryOp(BinOp::Neq(base_ty), Box::new(self), Box::new(rhs.into()))
    }

    /// Project the arguments inside the predicate that have a specific index into local variables.
    pub(crate) fn project(&mut self, f: impl Fn(usize) -> Predicate<V> + Copy, index: usize) {
        match self {
            Self::Lit(_) | Self::Hole(_) => (),
            Self::Var(variable) => match variable {
                Variable::Local(_) | Variable::Bound => (),
                Variable::Arg(arg) => {
                    if arg.index() == index {
                        *self = f(arg.pos());
                    }
                }
            },
            Self::UnaryOp(_, op) => op.project(f, index),
            Self::BinaryOp(_, op1, op2) => {
                op1.project(f, index);
                op2.project(f, index);
            }
        }
    }
}

impl<V, Rhs: Into<Predicate<V>>> BitAnd<Rhs> for Predicate<V> {
    type Output = Self;
    /// Produce a new predicate by comparing two predicates using the logical and operation.
    ///
    /// Comparing predicates that are not booleans is unsound.
    fn bitand(self, rhs: Rhs) -> Self {
        match (self, rhs.into()) {
            (Self::Lit(lit), rhs) if lit.is_true() => rhs,
            (lhs, Self::Lit(lit)) if lit.is_true() => lhs,
            (lhs, rhs) => Self::BinaryOp(BinOp::And, Box::new(lhs), Box::new(rhs)),
        }
    }
}

impl<V> From<Variable<V>> for Predicate<V> {
    fn from(variable: Variable<V>) -> Self {
        Self::Var(variable)
    }
}

impl<V> From<bool> for Predicate<V> {
    fn from(b: bool) -> Self {
        Self::Lit(b.into())
    }
}

impl<V> From<Literal> for Predicate<V> {
    fn from(literal: Literal) -> Self {
        Self::Lit(literal)
    }
}

impl<V: fmt::Display> fmt::Display for Predicate<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Lit(literal) => literal.fmt(f),
            Self::Var(variable) => variable.fmt(f),
            Self::UnaryOp(un_op, op) => write!(f, "{}{}", un_op, op),
            Self::BinaryOp(bin_op, op1, op2) => write!(f, "({} {} {})", op1, bin_op, op2),
            Self::Hole(id) => write!(f, "?P{}", id.0),
        }
    }
}
