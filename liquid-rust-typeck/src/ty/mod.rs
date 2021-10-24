use std::{fmt, lazy::SyncOnceCell};

pub use liquid_rust_common::index::newtype_index;
use liquid_rust_core::ir::Local;
pub use liquid_rust_core::ty::{BaseTy, TypeLayout};
pub use liquid_rust_fixpoint::{BinOp, Constant, Sort, UnOp, Var};
pub use rustc_middle::ty::IntTy;

use self::intern::Interned;

mod intern;

pub type Ty = Interned<TyS>;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct TyS {
    kind: TyKind,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum TyKind {
    Refine(BaseTy, Expr),
    Exists(BaseTy, Var, Expr),
    Uninit(TypeLayout),
    MutRef(Region),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Region {
    Concrete(Local),
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Pred {
    // KVar(KVid),
    Expr(Expr),
}

pub type Expr = Interned<ExprS>;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct ExprS {
    kind: ExprKind,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum ExprKind {
    Var(Var),
    Constant(Constant),
    BinaryOp(BinOp, Expr, Expr),
    UnaryOp(UnOp, Expr),
}

impl TyKind {
    pub fn intern(self) -> Ty {
        Interned::new(TyS { kind: self })
    }
}

impl TyS {
    pub fn kind(&self) -> &TyKind {
        &self.kind
    }

    pub fn layout(&self) -> TypeLayout {
        match self.kind() {
            TyKind::Refine(bty, _) | TyKind::Exists(bty, _, _) => TypeLayout::BaseTy(*bty),
            TyKind::Uninit(layout) => layout.clone(),
            TyKind::MutRef(_) => TypeLayout::MutRef,
        }
    }
}

impl ExprKind {
    pub fn intern(self) -> Expr {
        Interned::new(ExprS { kind: self })
    }
}

impl Expr {
    pub fn tt() -> Expr {
        static TRUE: SyncOnceCell<Expr> = SyncOnceCell::new();
        TRUE.get_or_init(|| ExprKind::Constant(Constant::Bool(true)).intern())
            .clone()
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
        fn should_parenthesize(op: BinOp, child: &Expr) -> bool {
            if let ExprKind::BinaryOp(child_op, ..) = child.kind() {
                child_op.precedence() < op.precedence()
                    || (child_op.precedence() == op.precedence()
                        && !BinOp::associative(op.precedence()))
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
            ExprKind::UnaryOp(op, e) => {
                if matches!(e.kind(), ExprKind::Var(_) | ExprKind::Constant(_)) {
                    write!(f, "{}{:?}", op, e)
                } else {
                    write!(f, "{}({:?})", op, e)
                }
            }
        }
    }
}

impl From<Local> for Region {
    fn from(v: Local) -> Self {
        Self::Concrete(v)
    }
}
