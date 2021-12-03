use std::{fmt, lazy::SyncOnceCell};

use itertools::Itertools;
use liquid_rust_common::index::{newtype_index, Idx, IndexGen};
use liquid_rust_core::ir::Local;
pub use liquid_rust_core::ty::ParamTy;
pub use liquid_rust_fixpoint::{BinOp, Constant, KVid, Name, Sort, UnOp};
use rustc_hir::def_id::DefId;
pub use rustc_middle::ty::{IntTy, UintTy};

use crate::intern::{impl_internable, Interned};

pub type Ty = Interned<TyS>;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct TyS {
    kind: TyKind,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum TyKind {
    Refine(BaseTy, Expr),
    Exists(BaseTy, Pred),
    Uninit,
    MutRef(Region),
    Param(ParamTy),
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum BaseTy {
    Int(IntTy),
    Uint(UintTy),
    Bool,
    Adt(DefId, Substs),
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Substs(Interned<Vec<Ty>>);

pub type Region = Interned<RegionS>;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct RegionS(Vec<RVid>);

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Pred {
    KVar(KVid, Expr, Interned<Vec<Expr>>),
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

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Var {
    Bound,
    Free(Name),
}

newtype_index! {
    pub struct RVid {
        DEBUG_FORMAT = "'{}"
    }
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

    pub fn is_uninit(&self) -> bool {
        matches!(self.kind(), TyKind::Uninit)
    }
}

impl Substs {
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn iter(&self) -> std::slice::Iter<Ty> {
        self.0.iter()
    }
}

impl<'a> IntoIterator for &'a Substs {
    type Item = &'a Ty;

    type IntoIter = std::slice::Iter<'a, Ty>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl FromIterator<Ty> for Substs {
    fn from_iter<T: IntoIterator<Item = Ty>>(iter: T) -> Self {
        Substs(Interned::new(iter.into_iter().collect()))
    }
}

impl BaseTy {
    pub fn sort(&self) -> Sort {
        match self {
            BaseTy::Int(_) => Sort::Int,
            BaseTy::Uint(_) => Sort::Int,
            BaseTy::Bool => Sort::Bool,
            BaseTy::Adt(_, _) => Sort::Int,
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

    pub fn zero() -> Expr {
        static ZERO: SyncOnceCell<Expr> = SyncOnceCell::new();
        ZERO.get_or_init(|| ExprKind::Constant(Constant::ZERO).intern())
            .clone()
    }

    pub fn from_bits(bty: &BaseTy, bits: u128) -> Expr {
        // FIXME: We are assuming the higher bits are not set. check this assumption
        match bty {
            BaseTy::Int(_) => {
                let bits = bits as i128;
                ExprKind::Constant(Constant::from(bits)).intern()
            }
            BaseTy::Uint(uint_ty) => {
                let bits = bits as u128;
                ExprKind::Constant(Constant::from(bits)).intern()
            }
            BaseTy::Bool => ExprKind::Constant(Constant::Bool(bits != 0)).intern(),
            BaseTy::Adt(_, _) => panic!(),
        }
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

    pub fn is_true(&self) -> bool {
        matches!(self.kind, ExprKind::Constant(Constant::Bool(true)))
    }

    pub fn is_atom(&self) -> bool {
        matches!(
            self.kind,
            ExprKind::Var(_) | ExprKind::Constant(_) | ExprKind::UnaryOp(..)
        )
    }

    pub fn subst_bound_vars(&self, to: Expr) -> Expr {
        match self.kind() {
            ExprKind::Var(var) => match var {
                Var::Bound => to,
                Var::Free(_) => ExprKind::Var(*var).intern(),
            },
            ExprKind::Constant(c) => ExprKind::Constant(*c).intern(),
            ExprKind::BinaryOp(op, e1, e2) => ExprKind::BinaryOp(
                *op,
                e1.subst_bound_vars(to.clone()),
                e2.subst_bound_vars(to),
            )
            .intern(),
            ExprKind::UnaryOp(op, e) => ExprKind::UnaryOp(*op, e.subst_bound_vars(to)).intern(),
        }
    }
}

impl From<Expr> for Pred {
    fn from(expr: Expr) -> Self {
        Pred::Expr(expr)
    }
}

impl RegionS {
    fn intern(self) -> Region {
        Interned::new(self)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn subset(&self, other: &RegionS) -> bool {
        self.iter().all(|local| other.iter().contains(&local))
    }

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

    pub fn iter(&self) -> std::iter::Copied<std::slice::Iter<'_, RVid>> {
        self.0.iter().copied()
    }
}

impl From<RVid> for Region {
    fn from(rvid: RVid) -> Self {
        RegionS(vec![rvid]).intern()
    }
}

impl FromIterator<RVid> for Region {
    fn from_iter<T: IntoIterator<Item = RVid>>(iter: T) -> Self {
        RegionS(iter.into_iter().collect()).intern()
    }
}

impl<'a> IntoIterator for &'a RegionS {
    type Item = RVid;

    type IntoIter = std::iter::Copied<std::slice::Iter<'a, RVid>>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl std::ops::Index<usize> for RegionS {
    type Output = RVid;

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

impl Pred {
    pub fn kvar(kvid: KVid, e: Expr, args: impl IntoIterator<Item = Expr>) -> Self {
        Pred::KVar(kvid, e, Interned::new(args.into_iter().collect()))
    }

    pub fn is_atom(&self) -> bool {
        matches!(self, Pred::KVar(_, _, _)) || matches!(self, Pred::Expr(e) if e.is_atom())
    }

    pub fn subst_bound_vars(&self, to: Expr) -> Self {
        match self {
            Pred::KVar(kvid, e, args) => Pred::kvar(
                *kvid,
                e.subst_bound_vars(to.clone()),
                args.iter().map(|arg| arg.subst_bound_vars(to.clone())),
            ),
            Pred::Expr(e) => Pred::Expr(e.subst_bound_vars(to)),
        }
    }

    pub fn is_true(&self) -> bool {
        match self {
            Pred::KVar(..) => false,
            Pred::Expr(e) => e.is_true(),
        }
    }
}

impl From<Var> for Expr {
    fn from(var: Var) -> Self {
        ExprKind::Var(var).intern()
    }
}

impl_internable!(
    crate::ty::TyS,
    crate::ty::ExprS,
    crate::ty::RegionS,
    Vec<Expr>,
    Vec<Ty>
);
