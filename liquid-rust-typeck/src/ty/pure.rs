use std::fmt;

use hashconsing::HConsed;
pub use liquid_rust_fixpoint::{BinOp, Constant, Sort, Var};

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct RType {
    pub sort: Sort,
    pub refine: Refine,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Refine {
    // KVar(KVid),
    Pred(Expr),
}

pub type Expr = HConsed<ExprS>;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct ExprS {
    pub(crate) kind: ExprKind,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum ExprKind {
    Var(Var),
    Constant(Constant),
    BinaryOp(BinOp, Expr, Expr),
}

impl ExprS {
    pub fn kind(&self) -> &ExprKind {
        &self.kind
    }
}

impl From<Expr> for Refine {
    fn from(expr: Expr) -> Self {
        Refine::Pred(expr)
    }
}

impl fmt::Debug for Refine {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            // Self::KVar(kvid) => write!(f, "{:?}", kvid),
            Self::Pred(expr) => write!(f, "{:?}", expr),
        }
    }
}

impl fmt::Debug for RType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{{} | {:?}}}", self.sort, self.refine)
    }
}

impl fmt::Debug for ExprS {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn should_parenthesize(bin_op: BinOp, child: &Expr) -> bool {
            if let ExprKind::BinaryOp(child_op, ..) = child.kind() {
                child_op.precedence() < bin_op.precedence()
                    || (child_op.precedence() == bin_op.precedence()
                        && !BinOp::associative(bin_op.precedence()))
            } else {
                false
            }
        }

        match self.kind() {
            ExprKind::Var(x) => write!(f, "{:?}", x)?,
            ExprKind::BinaryOp(op, e1, e2) => {
                if should_parenthesize(*op, e1) {
                    write!(f, "({:?})", e1)?;
                } else {
                    write!(f, "{:?}", e1)?;
                }
                write!(f, " {} ", op)?;
                if should_parenthesize(*op, e2) {
                    write!(f, "({:?})", e2)?;
                } else {
                    write!(f, "{:?}", e2)?;
                }
            }
            ExprKind::Constant(c) => write!(f, "{}", c)?,
        }
        Ok(())
    }
}
