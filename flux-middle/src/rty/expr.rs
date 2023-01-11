use std::{fmt, sync::OnceLock};

use flux_fixpoint::Sign;
pub use flux_fixpoint::{BinOp, Constant, UnOp};
use rustc_hir::def_id::DefId;
use rustc_index::newtype_index;
use rustc_middle::mir::{Field, Local};
use rustc_span::Symbol;

use super::{evars::EVar, BaseTy, KVar};
use crate::{
    intern::{impl_internable, Interned, List},
    rty::fold::{TypeFoldable, TypeFolder},
    rustc::mir::{Place, PlaceElem},
};

pub type Expr = Interned<ExprS>;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct ExprS {
    kind: ExprKind,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum ExprKind {
    FreeVar(Name),
    EVar(EVar),
    BoundVar(BoundVar),
    Local(Local),
    Constant(Constant),
    ConstDefId(DefId),
    BinaryOp(BinOp, Expr, Expr),
    App(Func, List<Expr>),
    UnaryOp(UnOp, Expr),
    TupleProj(Expr, u32),
    Tuple(List<Expr>),
    PathProj(Expr, Field),
    IfThenElse(Expr, Expr, Expr),
    KVar(KVar),
    Hole,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Func {
    Var(Var),
    Uif(Symbol),
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Var {
    Free(Name),
    Bound(BoundVar),
    EVar(EVar),
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Path {
    pub loc: Loc,
    projection: List<Field>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Loc {
    Local(Local),
    Var(Var),
}

/// A bound *var*riable is represented as a debruijn index
/// into a list of [`Binders`] and index into that list.
///
/// [`Binders`]: super::Binders
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BoundVar {
    pub debruijn: DebruijnIndex,
    pub index: usize,
}

newtype_index! {
    #[debug_format = "a{}"]
    pub struct Name {}
}

newtype_index! {
    #[debug_format = "DebruijnIndex({})"]
    pub struct DebruijnIndex {
        const INNERMOST = 0;
    }
}

impl ExprKind {
    fn intern(self) -> Expr {
        Interned::new(ExprS { kind: self })
    }
}

impl Expr {
    pub fn tt() -> Expr {
        static TRUE: OnceLock<Expr> = OnceLock::new();
        TRUE.get_or_init(|| ExprKind::Constant(Constant::Bool(true)).intern())
            .clone()
    }

    pub fn ff() -> Expr {
        static FALSE: OnceLock<Expr> = OnceLock::new();
        FALSE
            .get_or_init(|| ExprKind::Constant(Constant::Bool(false)).intern())
            .clone()
    }

    pub fn and(exprs: impl IntoIterator<Item = Expr>) -> Expr {
        exprs
            .into_iter()
            .reduce(|acc, e| Expr::binary_op(BinOp::And, acc, e))
            .unwrap_or_else(Expr::tt)
    }

    pub fn or(exprs: impl IntoIterator<Item = Expr>) -> Expr {
        exprs
            .into_iter()
            .reduce(|acc, e| Expr::binary_op(BinOp::Or, acc, e))
            .unwrap_or_else(Expr::ff)
    }

    pub fn zero() -> Expr {
        static ZERO: OnceLock<Expr> = OnceLock::new();
        ZERO.get_or_init(|| ExprKind::Constant(Constant::ZERO).intern())
            .clone()
    }

    pub fn one() -> Expr {
        static ONE: OnceLock<Expr> = OnceLock::new();
        ONE.get_or_init(|| ExprKind::Constant(Constant::ONE).intern())
            .clone()
    }

    pub fn nu() -> Expr {
        Expr::bvar(BoundVar::NU)
    }

    pub fn unit() -> Expr {
        Expr::tuple(vec![])
    }

    pub fn fvar(name: Name) -> Expr {
        ExprKind::FreeVar(name).intern()
    }

    pub fn evar(evar: EVar) -> Expr {
        ExprKind::EVar(evar).intern()
    }

    pub fn bvar(bvar: BoundVar) -> Expr {
        ExprKind::BoundVar(bvar).intern()
    }

    pub fn local(local: Local) -> Expr {
        ExprKind::Local(local).intern()
    }

    pub fn constant(c: Constant) -> Expr {
        ExprKind::Constant(c).intern()
    }

    pub fn const_def_id(c: DefId) -> Expr {
        ExprKind::ConstDefId(c).intern()
    }

    pub fn tuple(exprs: impl Into<List<Expr>>) -> Expr {
        ExprKind::Tuple(exprs.into()).intern()
    }

    pub fn from_bits(bty: &BaseTy, bits: u128) -> Expr {
        // FIXME: We are assuming the higher bits are not set. check this assumption
        match bty {
            BaseTy::Int(_) => {
                let bits = bits as i128;
                ExprKind::Constant(Constant::from(bits)).intern()
            }
            BaseTy::Uint(_) => ExprKind::Constant(Constant::from(bits)).intern(),
            BaseTy::Bool => ExprKind::Constant(Constant::Bool(bits != 0)).intern(),
            BaseTy::Adt(_, _)
            | BaseTy::Str
            | BaseTy::Float(_)
            | BaseTy::Slice(_)
            | BaseTy::Char => panic!(),
        }
    }

    pub fn ite(p: impl Into<Expr>, e1: impl Into<Expr>, e2: impl Into<Expr>) -> Expr {
        ExprKind::IfThenElse(p.into(), e1.into(), e2.into()).intern()
    }

    pub fn hole() -> Expr {
        ExprKind::Hole.intern()
    }

    pub fn kvar(kvar: KVar) -> Expr {
        ExprKind::KVar(kvar).intern()
    }

    pub fn binary_op(op: BinOp, e1: impl Into<Expr>, e2: impl Into<Expr>) -> Expr {
        ExprKind::BinaryOp(op, e1.into(), e2.into()).intern()
    }

    pub fn app(func: impl Into<Func>, args: impl Into<List<Expr>>) -> Expr {
        ExprKind::App(func.into(), args.into()).intern()
    }

    pub fn unary_op(op: UnOp, e: impl Into<Expr>) -> Expr {
        ExprKind::UnaryOp(op, e.into()).intern()
    }

    pub fn eq(e1: impl Into<Expr>, e2: impl Into<Expr>) -> Expr {
        ExprKind::BinaryOp(BinOp::Eq, e1.into(), e2.into()).intern()
    }

    pub fn ne(e1: impl Into<Expr>, e2: impl Into<Expr>) -> Expr {
        ExprKind::BinaryOp(BinOp::Ne, e1.into(), e2.into()).intern()
    }

    pub fn ge(e1: impl Into<Expr>, e2: impl Into<Expr>) -> Expr {
        ExprKind::BinaryOp(BinOp::Ge, e1.into(), e2.into()).intern()
    }

    pub fn gt(e1: impl Into<Expr>, e2: impl Into<Expr>) -> Expr {
        ExprKind::BinaryOp(BinOp::Gt, e1.into(), e2.into()).intern()
    }

    pub fn lt(e1: impl Into<Expr>, e2: impl Into<Expr>) -> Expr {
        ExprKind::BinaryOp(BinOp::Lt, e1.into(), e2.into()).intern()
    }

    pub fn le(e1: impl Into<Expr>, e2: impl Into<Expr>) -> Expr {
        ExprKind::BinaryOp(BinOp::Le, e1.into(), e2.into()).intern()
    }

    pub fn implies(e1: impl Into<Expr>, e2: impl Into<Expr>) -> Expr {
        ExprKind::BinaryOp(BinOp::Imp, e1.into(), e2.into()).intern()
    }

    pub fn proj(e: impl Into<Expr>, proj: u32) -> Expr {
        ExprKind::TupleProj(e.into(), proj).intern()
    }

    pub fn path_proj(base: Expr, field: Field) -> Expr {
        ExprKind::PathProj(base, field).intern()
    }

    pub fn not(&self) -> Expr {
        ExprKind::UnaryOp(UnOp::Not, self.clone()).intern()
    }

    pub fn neg(&self) -> Expr {
        ExprKind::UnaryOp(UnOp::Neg, self.clone()).intern()
    }

    pub fn kind(&self) -> &ExprKind {
        &self.kind
    }

    /// An expression is an atom if it "self-delimiting", i.e., it has a clear boundary
    /// when printed. This is used to avoid unnecesary parenthesis when pretty printing.
    pub fn is_atom(&self) -> bool {
        !self.is_binary_op()
    }

    /// Simple syntactic check to see if the expression is a trivially true predicate. This is used
    /// mostly for filtering predicates when pretty printing but also to simplify the constraint
    /// before encoding it into fixpoint.
    pub fn is_trivially_true(&self) -> bool {
        self.is_true()
            || matches!(self.kind(), ExprKind::BinaryOp(BinOp::Eq | BinOp::Iff | BinOp::Imp, e1, e2) if e1 == e2)
    }

    /// Whether the expression is literally the constant true.
    pub fn is_true(&self) -> bool {
        matches!(self.kind, ExprKind::Constant(Constant::Bool(true)))
    }

    pub fn is_binary_op(&self) -> bool {
        matches!(self.kind, ExprKind::BinaryOp(..))
    }

    fn const_op(op: &BinOp, c1: &Constant, c2: &Constant) -> Option<Constant> {
        match op {
            BinOp::Iff => c1.iff(c2),
            BinOp::Imp => c1.imp(c2),
            BinOp::Or => c1.or(c2),
            BinOp::And => c1.and(c2),
            BinOp::Gt => c1.gt(c2),
            BinOp::Ge => c1.ge(c2),
            BinOp::Lt => c2.gt(c1),
            BinOp::Le => c2.ge(c1),
            BinOp::Eq => Some(c1.eq(c2)),
            BinOp::Ne => Some(c1.ne(c2)),
            _ => None,
        }
    }

    /// Simplify expression applying some simple rules like removing double negation. This is
    /// only used for pretty printing.
    pub fn simplify(&self) -> Expr {
        struct Simplify;

        impl TypeFolder for Simplify {
            fn fold_expr(&mut self, expr: &Expr) -> Expr {
                match expr.kind() {
                    ExprKind::BinaryOp(op, e1, e2) => {
                        let e1 = e1.fold_with(self);
                        let e2 = e2.fold_with(self);
                        match (op, e1.kind(), e2.kind()) {
                            (BinOp::And, ExprKind::Constant(Constant::Bool(false)), _)
                            | (BinOp::And, _, ExprKind::Constant(Constant::Bool(false))) => {
                                Expr::constant(Constant::Bool(false))
                            }
                            (BinOp::And, ExprKind::Constant(Constant::Bool(true)), _) => e2,
                            (BinOp::And, _, ExprKind::Constant(Constant::Bool(true))) => e1,
                            (op, ExprKind::Constant(c1), ExprKind::Constant(c2)) => {
                                match Expr::const_op(op, c1, c2) {
                                    Some(c) => Expr::constant(c),
                                    None => Expr::binary_op(*op, e1, e2),
                                }
                            }
                            _ => Expr::binary_op(*op, e1, e2),
                        }
                    }
                    ExprKind::UnaryOp(UnOp::Not, e) => {
                        let e = e.fold_with(self);
                        match e.kind() {
                            ExprKind::Constant(Constant::Bool(b)) => {
                                Expr::constant(Constant::Bool(!b))
                            }
                            ExprKind::UnaryOp(UnOp::Not, e) => e.clone(),
                            ExprKind::BinaryOp(BinOp::Eq, e1, e2) => {
                                Expr::binary_op(BinOp::Ne, e1.clone(), e2.clone())
                            }
                            _ => Expr::unary_op(UnOp::Not, e),
                        }
                    }
                    _ => expr.super_fold_with(self),
                }
            }
        }
        self.fold_with(&mut Simplify)
    }

    pub fn to_loc(&self) -> Option<Loc> {
        match self.kind() {
            ExprKind::Local(local) => Some(Loc::Local(*local)),
            ExprKind::FreeVar(name) => Some(Loc::Var(Var::Free(*name))),
            ExprKind::BoundVar(bvar) => Some(Loc::Var(Var::Bound(*bvar))),
            ExprKind::EVar(evar) => Some(Loc::Var(Var::EVar(*evar))),
            _ => None,
        }
    }

    pub fn to_var(&self) -> Option<Var> {
        match self.kind() {
            ExprKind::FreeVar(name) => Some(Var::Free(*name)),
            ExprKind::BoundVar(bvar) => Some(Var::Bound(*bvar)),
            ExprKind::EVar(evar) => Some(Var::EVar(*evar)),
            _ => None,
        }
    }

    pub fn to_fvar(&self) -> Option<Name> {
        match self.kind() {
            ExprKind::FreeVar(name) => Some(*name),
            _ => None,
        }
    }

    pub fn to_path(&self) -> Option<Path> {
        let mut expr = self;
        let mut proj = vec![];
        let loc = loop {
            match expr.kind() {
                ExprKind::PathProj(e, field) => {
                    proj.push(*field);
                    expr = e;
                }
                ExprKind::FreeVar(name) => break Loc::Var(Var::Free(*name)),
                ExprKind::BoundVar(bvar) => break Loc::Var(Var::Bound(*bvar)),
                ExprKind::EVar(evar) => break Loc::Var(Var::EVar(*evar)),
                ExprKind::Local(local) => break Loc::Local(*local),
                _ => return None,
            }
        };
        proj.reverse();
        Some(Path::new(loc, proj))
    }
}

impl Var {
    pub fn to_expr(&self) -> Expr {
        match self {
            Var::Bound(bvar) => Expr::bvar(*bvar),
            Var::Free(name) => Expr::fvar(*name),
            Var::EVar(evar) => Expr::evar(*evar),
        }
    }

    pub fn to_path(&self) -> Path {
        self.to_loc().into()
    }

    pub fn to_loc(&self) -> Loc {
        Loc::Var(*self)
    }
}

impl Path {
    pub fn new(loc: Loc, projection: impl Into<List<Field>>) -> Path {
        Path { loc, projection: projection.into() }
    }

    pub fn from_place(place: &Place) -> Option<Path> {
        let mut proj = vec![];
        for elem in &place.projection {
            if let PlaceElem::Field(field) = elem {
                proj.push(*field);
            } else {
                return None;
            }
        }
        Some(Path::new(Loc::Local(place.local), proj))
    }

    pub fn projection(&self) -> &[Field] {
        &self.projection[..]
    }

    pub fn to_expr(&self) -> Expr {
        self.projection
            .iter()
            .rev()
            .fold(self.loc.to_expr(), |e, f| Expr::path_proj(e, *f))
    }

    pub fn to_loc(&self) -> Option<Loc> {
        if self.projection.is_empty() {
            Some(self.loc)
        } else {
            None
        }
    }
}

impl Loc {
    pub fn to_expr(&self) -> Expr {
        match self {
            Loc::Local(local) => Expr::local(*local),
            Loc::Var(var) => var.to_expr(),
        }
    }
}

impl BoundVar {
    pub const NU: BoundVar = BoundVar { debruijn: INNERMOST, index: 0 };

    pub fn new(index: usize, debruijn: DebruijnIndex) -> Self {
        BoundVar { debruijn, index }
    }

    pub fn innermost(index: usize) -> BoundVar {
        BoundVar::new(index, INNERMOST)
    }

    pub fn to_expr(self) -> Expr {
        Expr::bvar(self)
    }

    pub fn to_var(self) -> Var {
        Var::Bound(self)
    }
}

impl DebruijnIndex {
    pub fn new(depth: u32) -> DebruijnIndex {
        DebruijnIndex::from_u32(depth)
    }

    pub fn depth(&self) -> u32 {
        self.as_u32()
    }

    /// Returns the resulting index when this value is moved into
    /// `amount` number of new binders. So, e.g., if you had
    ///
    /// ```ignore
    ///    for<a: int> fn(i32[a])
    /// ```
    ///
    /// and you wanted to change it to
    ///
    /// ```ignore
    ///    for<a: int> fn(for<b: int> fn(i32[a]))
    /// ```
    ///
    /// you would need to shift the index for `a` into a new binder.
    #[must_use]
    pub fn shifted_in(self, amount: u32) -> DebruijnIndex {
        DebruijnIndex::from_u32(self.as_u32() + amount)
    }

    /// Update this index in place by shifting it "in" through
    /// `amount` number of binders.
    pub fn shift_in(&mut self, amount: u32) {
        *self = self.shifted_in(amount);
    }

    /// Returns the resulting index when this value is moved out from
    /// `amount` number of new binders.
    #[must_use]
    pub fn shifted_out(self, amount: u32) -> DebruijnIndex {
        DebruijnIndex::from_u32(self.as_u32() - amount)
    }

    /// Update in place by shifting out from `amount` binders.
    pub fn shift_out(&mut self, amount: u32) {
        *self = self.shifted_out(amount);
    }
}

macro_rules! impl_ops {
    ($($op:ident: $method:ident),*) => {$(
        impl<Rhs> std::ops::$op<Rhs> for Expr
        where
            Rhs: Into<Expr>,
        {
            type Output = Expr;

            fn $method(self, rhs: Rhs) -> Self::Output {
                Expr::binary_op(BinOp::$op, self, rhs)
            }
        }

        impl<Rhs> std::ops::$op<Rhs> for &Expr
        where
            Rhs: Into<Expr>,
        {
            type Output = Expr;

            fn $method(self, rhs: Rhs) -> Self::Output {
                Expr::binary_op(BinOp::$op, self, rhs)
            }
        }
    )*};
}
impl_ops!(Add: add, Sub: sub, Mul: mul, Div: div);

impl From<Var> for Func {
    fn from(var: Var) -> Self {
        Func::Var(var)
    }
}

impl From<i32> for Expr {
    fn from(value: i32) -> Self {
        if value < 0 {
            Expr::constant(Constant::Int(Sign::Negative, -(value as i64) as u128))
        } else {
            Expr::constant(Constant::Int(Sign::Positive, value as u128))
        }
    }
}

impl From<&Expr> for Expr {
    fn from(e: &Expr) -> Self {
        e.clone()
    }
}

impl From<Loc> for Expr {
    fn from(loc: Loc) -> Self {
        loc.to_expr()
    }
}

impl From<Path> for Expr {
    fn from(path: Path) -> Self {
        path.to_expr()
    }
}

impl From<Name> for Expr {
    fn from(name: Name) -> Self {
        Expr::fvar(name)
    }
}

impl From<BoundVar> for Expr {
    fn from(bvar: BoundVar) -> Self {
        Expr::bvar(bvar)
    }
}

impl From<Loc> for Path {
    fn from(loc: Loc) -> Self {
        Path::new(loc, vec![])
    }
}

impl From<Name> for Loc {
    fn from(name: Name) -> Self {
        Loc::Var(Var::Free(name))
    }
}

impl From<Local> for Loc {
    fn from(local: Local) -> Self {
        Loc::Local(local)
    }
}

impl_internable!(ExprS, [Expr]);

mod pretty {
    use super::*;
    use crate::pretty::*;

    #[derive(PartialEq, Eq, PartialOrd, Ord)]
    pub enum Precedence {
        Iff,
        Imp,
        Or,
        And,
        Cmp,
        AddSub,
        MulDiv,
    }

    pub fn precedence(bin_op: &BinOp) -> Precedence {
        match bin_op {
            BinOp::Iff => Precedence::Iff,
            BinOp::Imp => Precedence::Imp,
            BinOp::Or => Precedence::Or,
            BinOp::And => Precedence::And,
            BinOp::Eq | BinOp::Ne | BinOp::Gt | BinOp::Lt | BinOp::Ge | BinOp::Le => {
                Precedence::Cmp
            }
            BinOp::Add | BinOp::Sub => Precedence::AddSub,
            BinOp::Mul | BinOp::Div | BinOp::Mod => Precedence::MulDiv,
        }
    }

    impl Precedence {
        pub fn is_associative(&self) -> bool {
            !matches!(self, Precedence::Imp | Precedence::Cmp)
        }
    }

    impl Pretty for Expr {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            fn should_parenthesize(op: &BinOp, child: &Expr) -> bool {
                if let ExprKind::BinaryOp(child_op, ..) = child.kind() {
                    precedence(child_op) < precedence(op)
                        || (precedence(child_op) == precedence(op)
                            && !precedence(op).is_associative())
                } else {
                    false
                }
            }
            let e = if cx.simplify_exprs { self.simplify() } else { self.clone() };
            match e.kind() {
                ExprKind::BoundVar(bvar) => w!("{:?}", bvar),
                ExprKind::FreeVar(name) => w!("{:?}", ^name),
                ExprKind::EVar(evar) => w!("{:?}", evar),
                ExprKind::Local(local) => w!("{:?}", ^local),
                ExprKind::ConstDefId(did) => w!("{:?}", ^did),
                ExprKind::Constant(c) => w!("{}", ^c),
                ExprKind::BinaryOp(op, e1, e2) => {
                    if should_parenthesize(op, e1) {
                        w!("({:?})", e1)?;
                    } else {
                        w!("{:?}", e1)?;
                    }
                    if matches!(op, BinOp::Div) {
                        w!("{:?}", op)?;
                    } else {
                        w!(" {:?} ", op)?;
                    }
                    if should_parenthesize(op, e2) {
                        w!("({:?})", e2)?;
                    } else {
                        w!("{:?}", e2)?;
                    }
                    Ok(())
                }
                ExprKind::UnaryOp(op, e) => {
                    if e.is_binary_op() {
                        w!("{:?}({:?})", op, e)
                    } else {
                        w!("{:?}{:?}", op, e)
                    }
                }
                ExprKind::TupleProj(e, field) => {
                    if e.is_binary_op() {
                        w!("({:?}).{:?}", e, ^field)
                    } else {
                        w!("{:?}.{:?}", e, ^field)
                    }
                }
                ExprKind::Tuple(exprs) => {
                    w!("({:?})", join!(", ", exprs))
                }
                ExprKind::PathProj(e, field) => {
                    if e.is_binary_op() {
                        w!("({:?}).{:?}", e, field)
                    } else {
                        w!("{:?}.{:?}", e, field)
                    }
                }
                ExprKind::App(func, exprs) => {
                    w!("{:?}({:?})", func, join!(", ", exprs))
                }
                ExprKind::IfThenElse(p, e1, e2) => {
                    w!("if {:?} {{ {:?} }} else {{ {:?} }}", p, e1, e2)
                }
                ExprKind::Hole => {
                    w!("*")
                }
                ExprKind::KVar(kvar) => {
                    w!("{:?}", kvar)
                }
            }
        }
    }

    impl Pretty for Func {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                Func::Var(f) => w!("{:?}", f),
                Func::Uif(f) => w!("{}", ^f),
            }
        }
    }

    impl Pretty for Path {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!("{:?}", self.loc)?;
            for field in self.projection.iter() {
                w!(".{}", ^u32::from(*field))?;
            }
            Ok(())
        }
    }

    impl Pretty for Loc {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                Loc::Local(local) => w!("{:?}", ^local),
                Loc::Var(var) => w!("{:?}", var),
            }
        }
    }

    impl Pretty for BoundVar {
        fn fmt(&self, _cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(_cx, f);
            w!("^{}.{:?}", ^self.debruijn.as_u32(), ^self.index)
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
                BinOp::Mod => w!("mod"),
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

    impl_debug_with_default_cx!(Expr, Loc, Path, BoundVar, Var);
}
