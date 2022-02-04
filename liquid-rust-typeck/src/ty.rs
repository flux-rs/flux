use std::{fmt, lazy::SyncOnceCell};

use liquid_rust_common::index::Idx;
use liquid_rust_core::ir::Local;
pub use liquid_rust_core::ty::ParamTy;
pub use liquid_rust_fixpoint::{BinOp, Constant, KVid, Sort, UnOp};
use rustc_hir::def_id::DefId;
use rustc_index::newtype_index;
pub use rustc_middle::ty::{IntTy, UintTy};

use crate::intern::{impl_internable, Interned};

#[derive(Debug)]
pub struct FnSig {
    pub params: Vec<Param>,
    pub requires: Vec<(Name, Ty)>,
    pub args: Vec<Ty>,
    pub ret: Ty,
    pub ensures: Vec<(Name, Ty)>,
}

#[derive(Debug)]
pub struct Param {
    pub name: Name,
    pub sort: Sort,
    pub pred: Pred,
}

pub type Ty = Interned<TyS>;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct TyS {
    kind: TyKind,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum TyKind {
    Refine(BaseTy, Expr),
    Exists(BaseTy, Pred),
    Uninit,
    StrgRef(Loc),
    Ref(Ty),
    Param(ParamTy),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Loc {
    Local(Local),
    Abstract(Name),
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum BaseTy {
    Int(IntTy),
    Uint(UintTy),
    Bool,
    Adt(DefId, Substs),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Substs(Interned<Vec<Ty>>);

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Pred {
    KVar(KVid, Interned<Vec<Expr>>),
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
    pub struct Name {
        DEBUG_FORMAT = "a{}",
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

    pub fn walk(&self, f: &mut impl FnMut(&TyS)) {
        f(self);
        match self.kind() {
            TyKind::Ref(ty) => ty.walk(f),
            TyKind::Refine(bty, _) | TyKind::Exists(bty, _) => bty.walk(f),
            _ => {}
        }
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

    pub fn adt(def_id: DefId, substs: impl IntoIterator<Item = Ty>) -> BaseTy {
        BaseTy::Adt(def_id, Substs::from_iter(substs))
    }

    fn walk(&self, f: &mut impl FnMut(&TyS)) {
        if let BaseTy::Adt(_, substs) = self {
            substs.iter().for_each(|ty| ty.walk(f));
        }
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
            BaseTy::Uint(_) => {
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

    pub fn subst_bound_vars(&self, to: impl Into<Expr>) -> Expr {
        let to = to.into();
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

    /// Simplify expression applying some rules like removing double negation. This is used for pretty
    /// printing.
    pub fn simplify(&self) -> Expr {
        match self.kind() {
            ExprKind::Var(var) => ExprKind::Var(*var).intern(),
            ExprKind::Constant(c) => ExprKind::Constant(*c).intern(),
            ExprKind::BinaryOp(op, e1, e2) => {
                ExprKind::BinaryOp(*op, e1.simplify(), e2.simplify()).intern()
            }
            ExprKind::UnaryOp(UnOp::Not, e) => match e.kind() {
                ExprKind::UnaryOp(UnOp::Not, e) => e.simplify(),
                ExprKind::BinaryOp(BinOp::Eq, e1, e2) => {
                    ExprKind::BinaryOp(BinOp::Ne, e1.simplify(), e2.simplify()).intern()
                }
                _ => ExprKind::UnaryOp(UnOp::Not, e.simplify()).intern(),
            },
            ExprKind::UnaryOp(op, e) => ExprKind::UnaryOp(*op, e.simplify()).intern(),
        }
    }
}

impl From<Expr> for Pred {
    fn from(expr: Expr) -> Self {
        Pred::Expr(expr)
    }
}

impl Pred {
    pub fn kvar(kvid: KVid, args: impl IntoIterator<Item = Expr>) -> Self {
        Pred::KVar(kvid, Interned::new(args.into_iter().collect()))
    }

    pub fn dummy_kvar() -> Pred {
        Pred::kvar(KVid::new(0), [])
    }

    pub fn is_atom(&self) -> bool {
        matches!(self, Pred::KVar(_, _)) || matches!(self, Pred::Expr(e) if e.is_atom())
    }

    pub fn subst_bound_vars(&self, to: impl Into<Expr>) -> Self {
        let to = to.into();
        match self {
            Pred::KVar(kvid, args) => Pred::kvar(
                *kvid,
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

impl PartialOrd for Loc {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (Loc::Local(local1), Loc::Local(local2)) => local1.partial_cmp(local2),
            (Loc::Local(_), Loc::Abstract(_)) => Some(std::cmp::Ordering::Less),
            (Loc::Abstract(_), Loc::Local(_)) => Some(std::cmp::Ordering::Greater),
            (Loc::Abstract(loc1), Loc::Abstract(loc2)) => loc1.partial_cmp(loc2),
        }
    }
}

impl Ord for Loc {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl From<Name> for Var {
    fn from(v: Name) -> Self {
        Self::Free(v)
    }
}

impl<'a> From<&'a Name> for Var {
    fn from(v: &'a Name) -> Self {
        Self::Free(*v)
    }
}

impl_internable!(TyS, ExprS, Vec<Expr>, Vec<Ty>);

mod pretty {
    use rustc_middle::ty::TyCtxt;

    use super::*;
    use crate::pretty::*;

    impl Pretty for TyS {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self.kind() {
                TyKind::Refine(bty, e) => {
                    if matches!(e.kind(), ExprKind::Constant(..) | ExprKind::Var(..)) {
                        w!("{:?}@{:?}", bty, e)
                    } else {
                        w!("{:?}@{{{:?}}}", bty, e)
                    }
                }
                TyKind::Exists(bty, p) => w!("{:?}{{{:?}}}", bty, p),
                TyKind::Uninit => w!("uninit"),
                TyKind::StrgRef(loc) => w!("ref<{:?}>", loc),
                TyKind::Ref(region) => w!("&mut {:?}", region),
                TyKind::Param(ParamTy { name, .. }) => w!("{:?}", ^name),
            }
        }

        fn default_cx(tcx: TyCtxt) -> PPrintCx {
            PPrintCx::default(tcx).kvar_args(Visibility::Hide)
        }
    }

    impl Pretty for BaseTy {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                BaseTy::Int(int_ty) => write!(f, "{}", int_ty.name_str()),
                BaseTy::Uint(uint_ty) => write!(f, "{}", uint_ty.name_str()),
                BaseTy::Bool => w!("bool"),
                BaseTy::Adt(did, args) => {
                    w!("{:?}", did)?;
                    if !args.is_empty() {
                        w!("<{:?}>", join!(", ", args))?;
                    }
                    Ok(())
                }
            }
        }
    }

    impl Pretty for Pred {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                Self::KVar(kvid, args) => {
                    w!("{:?}", ^kvid)?;
                    match cx.kvar_args {
                        Visibility::Show => w!("({:?})", join!(", ", args))?,
                        Visibility::Truncate(n) => w!("({:?})", join!(", ", args.iter().take(n)))?,
                        Visibility::Hide => {}
                    }
                    Ok(())
                }
                Self::Expr(expr) => w!("{:?}", expr),
            }
        }

        fn default_cx(tcx: TyCtxt) -> PPrintCx {
            PPrintCx::default(tcx).fully_qualified_paths(true)
        }
    }

    impl Pretty for ExprS {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            fn should_parenthesize(op: BinOp, child: &ExprS) -> bool {
                if let ExprKind::BinaryOp(child_op, ..) = child.kind() {
                    child_op.precedence() < op.precedence()
                        || (child_op.precedence() == op.precedence()
                            && !op.precedence().is_associative())
                } else {
                    false
                }
            }
            let e = if cx.simplify_exprs {
                self.simplify()
            } else {
                Interned::new(self.clone())
            };
            match e.kind() {
                ExprKind::Var(x) => w!("{:?}", ^x),
                ExprKind::BinaryOp(op, e1, e2) => {
                    if should_parenthesize(*op, e1) {
                        w!("({:?})", e1)?;
                    } else {
                        w!("{:?}", e1)?;
                    }
                    if matches!(op, BinOp::Div) {
                        w!("{:?}", op)?;
                    } else {
                        w!(" {:?} ", op)?;
                    }
                    if should_parenthesize(*op, e2) {
                        w!("({:?})", e2)?;
                    } else {
                        w!("{:?}", e2)?;
                    }
                    Ok(())
                }
                ExprKind::Constant(c) => w!("{}", ^c),
                ExprKind::UnaryOp(op, e) => {
                    if e.is_atom() {
                        w!("{:?}{:?}", op, e)
                    } else {
                        w!("{:?}({:?})", op, e)
                    }
                }
            }
        }
    }

    impl Pretty for Var {
        fn fmt(&self, _cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                Var::Bound => w!("ν"),
                Var::Free(var) => w!("{:?}", ^var),
            }
        }
    }

    impl Pretty for Loc {
        fn fmt(&self, _cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                Loc::Local(local) => w!("{:?}", ^local),
                Loc::Abstract(name) => w!("{:?}", ^name),
            }
        }
    }

    impl Pretty for BinOp {
        fn fmt(&self, _cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                BinOp::Iff => w!("⇔"),
                BinOp::Imp => w!("⇒"),
                BinOp::Or => w!("∨"),
                BinOp::And => w!("∧"),
                BinOp::Eq => w!("="),
                BinOp::Ne => w!("≠"),
                BinOp::Gt => w!(">"),
                BinOp::Ge => w!("≥"),
                BinOp::Lt => w!("<"),
                BinOp::Le => w!("≤"),
                BinOp::Add => w!("+"),
                BinOp::Sub => w!("-"),
                BinOp::Mul => w!("*"),
                BinOp::Div => w!("/"),
            }
        }
    }

    impl Pretty for UnOp {
        fn fmt(&self, _cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                UnOp::Not => w!("¬"),
                UnOp::Neg => w!("-"),
            }
        }
    }

    impl_debug_with_default_cx!(TyS, BaseTy, Pred, ExprS, Var, Loc);
}
