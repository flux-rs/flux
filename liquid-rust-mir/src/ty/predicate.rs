use crate::{
    ty::{
        argument::Argument,
        literal::Literal,
        op::{BinOp, UnOp},
        variable::Variable,
        BaseTy,
    },
    Operand,
};

use liquid_rust_common::new_index;

use std::{fmt, ops::BitAnd};

new_index! {
    #[derive(Clone, Copy, Debug)]
    HoleId
}

#[derive(Clone, Debug)]
pub struct Hole {
    pub id: HoleId,
    pub substs: Vec<(Variable, Variable)>,
}

impl From<HoleId> for Hole {
    fn from(id: HoleId) -> Self {
        Self { id, substs: vec![] }
    }
}

impl From<Operand> for Predicate {
    fn from(op: Operand) -> Self {
        match op {
            Operand::Literal(literal) => Predicate::Lit(literal),
            Operand::Local(local) => Predicate::Var(local.into()),
        }
    }
}

impl fmt::Display for Hole {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "?P{}", self.id.0)?;

        for (target, replacement) in &self.substs {
            write!(f, "[{} -> {}]", target, replacement)?;
        }

        Ok(())
    }
}

/// A quantifier-free predicate.
#[derive(Clone, Debug)]
pub enum Predicate {
    /// A literal.
    Lit(Literal),
    /// A variable bound by a refined base type, e.g the `b` in `{ b: usize | b > 0 }`.
    Bound,
    /// A variable bound by a dependent function type, e.g the `x` in `fn(x: usize) -> usize`.
    Arg(Argument),
    /// A variable.
    Var(Variable),
    /// An unary operation between predicates.
    UnaryOp(UnOp, Box<Self>),
    /// A binary operation between predicates.
    BinaryOp(BinOp, Box<Self>, Box<Self>),
    /// A predicate to be inferred.
    Hole(Hole),
    /// A disjunction between predicates.
    And(Vec<Self>),
}

impl Predicate {
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
    pub(crate) fn project(&mut self, f: impl Fn(usize) -> Predicate + Copy, index: usize) {
        match self {
            Self::Lit(_) | Self::Hole(_) | Self::Bound | Self::Var(_) => (),
            Self::Arg(arg) => {
                if arg.index() == index {
                    *self = f(arg.pos());
                }
            }
            Self::UnaryOp(_, op) => op.project(f, index),
            Self::BinaryOp(_, op1, op2) => {
                op1.project(f, index);
                op2.project(f, index);
            }
            Self::And(preds) => preds.iter_mut().for_each(|pred| pred.project(f, index)),
        }
    }

    pub(crate) fn replace_variable(&mut self, target: Variable, replacement: Variable) {
        match self {
            Self::Lit(_) | Self::Bound | Self::Arg(_) => (),
            Self::Var(var) => {
                if *var == target {
                    *var = replacement;
                }
            }
            Self::UnaryOp(_, op) => op.replace_variable(target, replacement),
            Self::BinaryOp(_, op1, op2) => {
                op1.replace_variable(target, replacement);
                op2.replace_variable(target, replacement);
            }
            Self::Hole(hole) => {
                hole.substs.push((target, replacement));
            }
            Self::And(preds) => preds
                .iter_mut()
                .for_each(|pred| pred.replace_variable(target, replacement)),
        }
    }
}

impl<Rhs: Into<Predicate>> BitAnd<Rhs> for Predicate {
    type Output = Self;
    /// Produce a new predicate by comparing two predicates using the logical and operation.
    ///
    /// Comparing predicates that are not booleans is unsound.
    fn bitand(self, rhs: Rhs) -> Self {
        match (self, rhs.into()) {
            (Self::Lit(lit), rhs) if lit.is_true() => rhs,
            (lhs, Self::Lit(lit)) if lit.is_true() => lhs,
            (Self::And(mut preds1), Self::And(mut preds2)) => {
                preds1.append(&mut preds2);
                Self::And(preds1)
            }
            (Self::And(mut preds), rhs) => {
                preds.push(rhs);
                Self::And(preds)
            }
            (lhs, Self::And(mut preds)) => {
                preds.insert(0, lhs);
                Self::And(preds)
            }
            (lhs, rhs) => Self::And(vec![lhs, rhs]),
        }
    }
}

impl From<Variable> for Predicate {
    fn from(variable: Variable) -> Self {
        Self::Var(variable)
    }
}

impl From<bool> for Predicate {
    fn from(b: bool) -> Self {
        Self::Lit(b.into())
    }
}

impl From<Literal> for Predicate {
    fn from(literal: Literal) -> Self {
        Self::Lit(literal)
    }
}

impl fmt::Display for Predicate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Lit(literal) => literal.fmt(f),
            Self::Bound => "b".fmt(f),
            Self::Arg(arg) => arg.fmt(f),
            Self::Var(variable) => variable.fmt(f),
            Self::UnaryOp(un_op, op) => write!(f, "{}{}", un_op, op),
            Self::BinaryOp(bin_op, op1, op2) => write!(f, "({} {} {})", op1, bin_op, op2),
            Self::Hole(hole) => hole.fmt(f),
            Self::And(preds) => {
                let mut preds = preds.iter();
                write!(f, "[")?;
                if let Some(pred) = preds.next() {
                    write!(f, "{}", pred)?;
                    for pred in preds {
                        write!(f, "; {}", pred)?;
                    }
                }
                write!(f, "]")
            }
        }
    }
}
