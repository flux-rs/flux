use std::{fmt, lazy::SyncOnceCell};

use itertools::Itertools;
use liquid_rust_core::ir::Local;
pub use liquid_rust_core::ty::{BaseTy, TypeLayout};
pub use liquid_rust_fixpoint::{BinOp, Constant, KVid, Sort, UnOp, Var};
pub use rustc_middle::ty::IntTy;

use crate::intern::{impl_internable, Interned};

pub type Ty = Interned<TyS>;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct TyS {
    kind: TyKind,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum TyKind {
    Refine(BaseTy, Expr),
    Exists(BaseTy, Var, Pred),
    Uninit,
    MutRef(Region),
}

pub type Region = Interned<RegionS>;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct RegionS(Vec<Local>);

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Pred {
    KVar(KVar),
    Expr(Expr),
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct KVar {
    pub kvid: KVid,
    pub args: Interned<Vec<Expr>>,
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

    pub fn not(&self) -> Expr {
        ExprKind::UnaryOp(UnOp::Not, self.clone()).intern()
    }

    pub fn neg(&self) -> Expr {
        ExprKind::UnaryOp(UnOp::Neg, self.clone()).intern()
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
            Self::KVar(kvar) => write!(f, "{:?}", kvar),
            Self::Expr(expr) => write!(f, "{:?}", expr),
        }
    }
}

impl fmt::Debug for KVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}({:?})", self.kvid, self.args.iter().format(" "))
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

impl RegionS {
    fn intern(self) -> Region {
        Interned::new(self)
    }

    pub fn subset(&self, other: &RegionS) -> bool {
        self.iter().all(|local| other.iter().contains(&local))
    }
}

impl From<Local> for Region {
    fn from(v: Local) -> Self {
        RegionS(vec![v]).intern()
    }
}

impl_internable!(
    crate::ty::TyS,
    crate::ty::ExprS,
    crate::ty::RegionS,
    Vec<Expr>
);

impl std::ops::Index<usize> for Region {
    type Output = Local;

    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl std::ops::Add<&'_ Region> for &'_ Region {
    type Output = Region;

    fn add(self, rhs: &Region) -> Self::Output {
        self.merge(rhs)
    }
}

impl RegionS {
    fn merge(&self, other: &Region) -> Region {
        RegionS(
            self.0
                .iter()
                .copied()
                .merge(other.0.iter().copied())
                .dedup()
                .collect(),
        )
        .intern()
    }

    pub fn iter(&self) -> impl Iterator<Item = Local> + '_ {
        self.0.iter().copied()
    }
}

impl FromIterator<Local> for Region {
    fn from_iter<T: IntoIterator<Item = Local>>(iter: T) -> Self {
        RegionS(iter.into_iter().collect()).intern()
    }
}

impl fmt::Debug for TyS {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            TyKind::Refine(bty, e) => write!(f, "{:?}@{:?}", bty, e),
            TyKind::Exists(bty, var, e) => write!(f, "{:?}{{{:?}: {:?}}}", bty, var, e),
            TyKind::Uninit => write!(f, "uninit"),
            TyKind::MutRef(region) => write!(f, "ref<{:?}>", region),
        }
    }
}

impl fmt::Debug for RegionS {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0.len() == 1 {
            write!(f, "{:?}", self.0[0])
        } else {
            write!(f, "{{{:?}}}", self.0.iter().format(","))
        }
    }
}

impl KVar {
    pub fn new(kvid: KVid, args: Vec<Expr>) -> Self {
        KVar {
            kvid,
            args: Interned::new(args),
        }
    }
}

impl From<Var> for Expr {
    fn from(var: Var) -> Self {
        ExprKind::Var(var).intern()
    }
}
