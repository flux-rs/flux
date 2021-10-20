use std::fmt;

use hashconsing::HConsed;
pub use liquid_rust_common::index::newtype_index;
pub use liquid_rust_fixpoint::{BinOp, Constant, Sort, Var};
pub use rustc_middle::ty::{IntTy, UintTy};

use self::context::LrCtxt;

pub mod context;

#[derive(Debug)]
pub struct FnSig {
    pub params: Vec<Param>,
    pub args: Vec<Ty>,
    pub ret: Ty,
}

pub type Ty = HConsed<TyS>;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct TyS {
    kind: TyKind,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum TyKind {
    Int(Refine, IntTy),
    Uint(Refine, UintTy),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Refine {
    Expr(Expr),
    EVar(EVar),
}

newtype_index! {
    pub struct EVar {
        DEBUG_FORMAT = "?{}",
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Param {
    pub name: Var,
    pub sort: Sort,
    pub pred: Pred,
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
    EVar(EVar),
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
            ExprKind::EVar(evar) => write!(f, "{:?}", evar),
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

impl From<Expr> for Refine {
    fn from(v: Expr) -> Self {
        Self::Expr(v)
    }
}

impl Refine {
    pub fn to_expr(&self, lr: &LrCtxt) -> Expr {
        match self {
            Self::Expr(expr) => expr.clone(),
            Self::EVar(evar) => lr.mk_evar(*evar),
        }
    }
}
