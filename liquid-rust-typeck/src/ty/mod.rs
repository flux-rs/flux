use std::fmt;

use hashconsing::HConsed;
pub use liquid_rust_common::index::newtype_index;
pub use liquid_rust_core::ty::{BaseTy, TypeLayout};
pub use liquid_rust_fixpoint::{BinOp, Constant, Sort, Var};
pub use rustc_middle::ty::IntTy;

pub mod context;

pub type Ty = HConsed<TyS>;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct TyS {
    kind: TyKind,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum TyKind {
    Refine(BaseTy, Expr),
    Exists(BaseTy, Var, Expr),
    Uninit(TypeLayout),
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Pred {
    // KVar(KVid),
    Expr(Expr),
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

impl TyS {
    pub fn kind(&self) -> &TyKind {
        &self.kind
    }
}

impl ExprS {
    pub fn kind(&self) -> &ExprKind {
        &self.kind
    }
}

impl From<Expr> for Pred {
    fn from(expr: Expr) -> Self {
        Pred::Expr(expr)
    }
}

impl fmt::Debug for Pred {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            // Self::KVar(kvid) => write!(f, "{:?}", kvid),
            Self::Expr(expr) => write!(f, "{:?}", expr),
        }
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
            ExprKind::Var(x) => write!(f, "{:?}", x),
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
                Ok(())
            }
            ExprKind::Constant(c) => write!(f, "{}", c),
        }
    }
}
