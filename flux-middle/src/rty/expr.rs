use std::{fmt, iter, slice, sync::OnceLock};

use flux_common::bug;
use flux_fixpoint::Sign;
pub use flux_fixpoint::{BinOp, Constant, UnOp};
use itertools::Itertools;
use rustc_abi::FieldIdx;
use rustc_hir::def_id::DefId;
use rustc_index::newtype_index;
use rustc_macros::{Decodable, Encodable, TyDecodable, TyEncodable};
use rustc_middle::mir::Local;
use rustc_span::{BytePos, Span, Symbol, SyntaxContext};
use rustc_type_ir::{DebruijnIndex, INNERMOST};

use super::{evars::EVar, BaseTy, Binder, IntTy, Sort, UintTy};
use crate::{
    fhir::FuncKind,
    intern::{impl_internable, Interned, List},
    rty::fold::{TypeFoldable, TypeFolder},
    rustc::mir::{Place, PlaceElem},
};

pub type Expr = Interned<ExprS>;

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub struct ExprS {
    kind: ExprKind,
    fspan: Option<FSpanData>,
}

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub struct FSpanData {
    pub lo: BytePos,
    pub hi: BytePos,
    pub ctxt: SyntaxContext,
}

impl FSpanData {
    pub fn new(span: Span) -> Self {
        let data = span.data();
        Self { lo: data.lo, hi: data.hi, ctxt: data.ctxt }
    }

    pub fn span(&self) -> Span {
        Span::new(self.lo, self.hi, self.ctxt, None)
    }
}

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub enum ExprKind {
    Var(Var),
    Local(Local),
    Constant(Constant),
    ConstDefId(DefId),
    BinaryOp(BinOp, Expr, Expr),
    App(Expr, Expr),
    GlobalFunc(Symbol, FuncKind),
    UnaryOp(UnOp, Expr),
    TupleProj(Expr, u32),
    Tuple(List<Expr>),
    PathProj(Expr, FieldIdx),
    IfThenElse(Expr, Expr, Expr),
    KVar(KVar),
    /// Lambda abstractions. They are purely syntactic and we don't encode them in the logic. As such,
    /// they have some syntactic restrictions that we must carefully maintain:
    ///
    /// 1. They can appear as an index at the top level.
    /// 2. We can only substitute an abstraction for a variable in function position (or as an index).
    ///    More generaly, we need to partially evaluate expressions such that all abstractions in
    ///    non-index position are eliminated before encoding into fixpoint. Right now, the implementation
    ///    only evaluates abstractions that are immediately applied to arguments, thus the restriction.
    Abs(Binder<Expr>),
    Hole,
}

/// In theory a kvar is just an unknown predicate that can use some variables in scope. In practice,
/// fixpoint makes a diference between the first and the rest of the variables, the first one being
/// the kvar's *self argument*. Fixpoint will only instantiate qualifiers that use the self argument.
/// Flux generalizes the self argument to be a list. We call the rest of the arguments the *scope*.
#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub struct KVar {
    pub kvid: KVid,
    /// The number of arguments consider to be *self arguments*.
    pub self_args: usize,
    /// The list of *all* arguments with the self arguments at the beginning, i.e., the
    /// list of self arguments followed by the scope.
    pub args: List<Expr>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Encodable, Decodable)]
pub enum Var {
    Free(Name),
    LateBound(DebruijnIndex),
    EarlyBound(u32),
    EVar(EVar),
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Encodable, Decodable)]
pub struct Path {
    pub loc: Loc,
    projection: List<FieldIdx>,
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Encodable, Decodable)]
pub enum Loc {
    Local(Local),
    TupleProj(Var, List<u32>),
}

newtype_index! {
    #[debug_format = "$k{}"]
    pub struct KVid {}
}

newtype_index! {
    #[debug_format = "a{}"]
    pub struct Name {}
}

impl ExprKind {
    fn intern_at(self, span: Option<Span>) -> Expr {
        Interned::new(ExprS { kind: self, fspan: span.map(FSpanData::new) })
    }

    fn intern(self) -> Expr {
        Interned::new(ExprS { kind: self, fspan: None })
    }
}

impl Expr {
    pub fn span(&self) -> Option<Span> {
        self.fspan.as_ref().map(|fspan| fspan.span())
    }

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
            .reduce(|acc, e| Expr::binary_op(BinOp::And, acc, e, None))
            .unwrap_or_else(Expr::tt)
    }

    pub fn or(exprs: impl IntoIterator<Item = Expr>) -> Expr {
        exprs
            .into_iter()
            .reduce(|acc, e| Expr::binary_op(BinOp::Or, acc, e, None))
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

    pub fn int_max(int_ty: IntTy) -> Expr {
        let bit_width: u64 = int_ty
            .bit_width()
            .unwrap_or(flux_config::pointer_width().bits());
        Expr::constant(Constant::int_max(bit_width.try_into().unwrap()))
    }

    pub fn int_min(int_ty: IntTy) -> Expr {
        let bit_width: u64 = int_ty
            .bit_width()
            .unwrap_or(flux_config::pointer_width().bits());
        Expr::constant(Constant::int_min(bit_width.try_into().unwrap()))
    }

    pub fn uint_max(uint_ty: UintTy) -> Expr {
        let bit_width: u64 = uint_ty
            .bit_width()
            .unwrap_or(flux_config::pointer_width().bits());
        Expr::constant(Constant::uint_max(bit_width.try_into().unwrap()))
    }

    pub fn nu() -> Expr {
        Expr::late_bvar(INNERMOST)
    }

    pub fn as_tuple(&self) -> &[Expr] {
        if let ExprKind::Tuple(tup) = self.kind() {
            tup
        } else {
            slice::from_ref(self)
        }
    }

    pub fn expect_tuple(&self) -> &[Expr] {
        if let ExprKind::Tuple(tup) = self.kind() {
            tup
        } else {
            bug!("expected tuple")
        }
    }

    pub fn unit() -> Expr {
        Expr::tuple(vec![])
    }

    pub fn var(var: Var, span: Option<Span>) -> Expr {
        ExprKind::Var(var).intern_at(span)
    }

    pub fn fvar(name: Name) -> Expr {
        Var::Free(name).to_expr()
    }

    pub fn evar(evar: EVar) -> Expr {
        Var::EVar(evar).to_expr()
    }

    pub fn late_bvar(bvar: DebruijnIndex) -> Expr {
        Var::LateBound(bvar).to_expr()
    }

    pub fn early_bvar(idx: u32) -> Expr {
        Var::EarlyBound(idx).to_expr()
    }

    pub fn local(local: Local, span: Option<Span>) -> Expr {
        ExprKind::Local(local).intern_at(span)
    }

    pub fn constant(c: Constant) -> Expr {
        ExprKind::Constant(c).intern()
    }

    pub fn constant_at(c: Constant, span: Option<Span>) -> Expr {
        ExprKind::Constant(c).intern_at(span)
    }

    pub fn const_def_id(c: DefId, span: Option<Span>) -> Expr {
        ExprKind::ConstDefId(c).intern_at(span)
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
            BaseTy::Adt(..)
            | BaseTy::Ref(..)
            | BaseTy::Str
            | BaseTy::Float(_)
            | BaseTy::Slice(_)
            | BaseTy::Char
            | BaseTy::RawPtr(_, _)
            | BaseTy::Tuple(_)
            | BaseTy::Array(_, _)
            | BaseTy::Closure(_, _)
            | BaseTy::Never
            | BaseTy::Param(_) => bug!(),
        }
    }

    pub fn ite(
        p: impl Into<Expr>,
        e1: impl Into<Expr>,
        e2: impl Into<Expr>,
        span: Option<Span>,
    ) -> Expr {
        ExprKind::IfThenElse(p.into(), e1.into(), e2.into()).intern_at(span)
    }

    pub fn abs(body: Binder<Expr>) -> Expr {
        ExprKind::Abs(body).intern()
    }

    pub fn hole() -> Expr {
        ExprKind::Hole.intern()
    }

    pub fn kvar(kvar: KVar) -> Expr {
        ExprKind::KVar(kvar).intern()
    }

    pub fn binary_op(
        op: BinOp,
        e1: impl Into<Expr>,
        e2: impl Into<Expr>,
        span: Option<Span>,
    ) -> Expr {
        ExprKind::BinaryOp(op, e1.into(), e2.into()).intern_at(span)
    }

    pub fn app(func: impl Into<Expr>, arg: impl Into<Expr>, span: Option<Span>) -> Expr {
        ExprKind::App(func.into(), arg.into()).intern_at(span)
    }

    pub fn global_func(func: Symbol, kind: FuncKind) -> Expr {
        ExprKind::GlobalFunc(func, kind).intern()
    }

    pub fn unary_op(op: UnOp, e: impl Into<Expr>, span: Option<Span>) -> Expr {
        ExprKind::UnaryOp(op, e.into()).intern_at(span)
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

    pub fn tuple_proj(e: impl Into<Expr>, proj: u32, span: Option<Span>) -> Expr {
        ExprKind::TupleProj(e.into(), proj).intern_at(span)
    }

    pub fn tuple_projs(e: impl Into<Expr>, projs: &[u32]) -> Expr {
        projs
            .iter()
            .copied()
            .fold(e.into(), |e, p| Expr::tuple_proj(e, p, None))
    }

    pub fn path_proj(base: Expr, field: FieldIdx) -> Expr {
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

    /// An expression is an *atom* if it is "self-delimiting", i.e., it has a clear boundary
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

    /// Whether the expression is *literally* the constant true.
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

    /// Simplify the expression by removing double negations, short-circuiting boolean connectives and
    /// doing constant folding. Note that we also have [`TypeFoldable::normalize`] which applies beta
    /// reductions for tuples and abstractions.
    pub fn simplify(&self) -> Expr {
        struct Simplify;

        impl TypeFolder for Simplify {
            fn fold_expr(&mut self, expr: &Expr) -> Expr {
                let span = expr.span();
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
                                    None => Expr::binary_op(*op, e1, e2, None),
                                }
                            }
                            _ => Expr::binary_op(*op, e1, e2, span),
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
                                Expr::binary_op(BinOp::Ne, e1.clone(), e2.clone(), span)
                            }
                            _ => Expr::unary_op(UnOp::Not, e, span),
                        }
                    }
                    _ => expr.super_fold_with(self),
                }
            }
        }
        self.fold_with(&mut Simplify)
    }

    pub fn to_var(&self) -> Option<Var> {
        if let ExprKind::Var(var) = self.kind() {
            Some(*var)
        } else {
            None
        }
    }

    pub fn to_loc(&self) -> Option<Loc> {
        if let ExprKind::Local(local) = self.kind() {
            return Some(Loc::Local(*local));
        }

        let mut proj = vec![];
        let mut expr = self;
        while let ExprKind::TupleProj(e, field) = expr.kind() {
            proj.push(*field);
            expr = e;
        }
        proj.reverse();
        let proj = List::from(proj);

        if let ExprKind::Var(var) = expr.kind() {
            Some(Loc::TupleProj(*var, proj))
        } else {
            None
        }
    }

    pub fn to_path(&self) -> Option<Path> {
        let mut expr = self;
        let mut proj = vec![];
        while let ExprKind::PathProj(e, field) = expr.kind() {
            proj.push(*field);
            expr = e;
        }
        proj.reverse();
        Some(Path::new(expr.to_loc()?, proj))
    }

    pub fn is_abs(&self) -> bool {
        matches!(self.kind(), ExprKind::Abs(..))
    }

    pub fn is_tuple(&self) -> bool {
        matches!(self.kind(), ExprKind::Tuple(..))
    }

    pub fn eta_expand_abs(&self, sort: &Sort) -> Binder<Expr> {
        Binder::with_sort(Expr::app(self, Expr::nu(), None), sort.clone())
    }

    pub fn eta_expand_tuple(&self, sort: &Sort) -> Expr {
        fn go(sort: &Sort, projs: &mut Vec<u32>, f: &impl Fn(&[u32]) -> Expr) -> Expr {
            if let Sort::Tuple(sorts) = sort {
                Expr::tuple(
                    sorts
                        .iter()
                        .enumerate()
                        .map(|(i, sort)| {
                            projs.push(i as u32);
                            let e = go(sort, projs, f);
                            projs.pop();
                            e
                        })
                        .collect_vec(),
                )
            } else {
                f(projs)
            }
        }
        if let (ExprKind::Tuple(exprs), Sort::Tuple(sorts)) = (self.kind(), sort) {
            Expr::tuple(
                iter::zip(exprs, sorts)
                    .map(|(e, s)| e.eta_expand_tuple(s))
                    .collect_vec(),
            )
        } else {
            go(sort, &mut vec![], &|projs| Expr::tuple_projs(self, projs))
        }
    }

    pub fn fold_sort(sort: &Sort, mut f: impl FnMut(&Sort) -> Expr) -> Expr {
        fn go(sort: &Sort, f: &mut impl FnMut(&Sort) -> Expr) -> Expr {
            if let Sort::Tuple(sorts) = sort {
                Expr::tuple(sorts.iter().map(|sort| go(sort, f)).collect_vec())
            } else {
                f(sort)
            }
        }
        go(sort, &mut f)
    }
}

impl KVar {
    pub fn new(kvid: KVid, self_args: usize, args: Vec<Expr>) -> Self {
        KVar { kvid, self_args, args: List::from_vec(args) }
    }

    fn self_args(&self) -> &[Expr] {
        &self.args[..self.self_args]
    }

    fn scope(&self) -> &[Expr] {
        &self.args[self.self_args..]
    }
}

impl Var {
    pub fn to_expr(&self) -> Expr {
        Expr::var(*self, None)
    }
}

impl Path {
    pub fn new(loc: Loc, projection: impl Into<List<FieldIdx>>) -> Path {
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

    pub fn projection(&self) -> &[FieldIdx] {
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
            Some(self.loc.clone())
        } else {
            None
        }
    }
}

impl Loc {
    pub fn to_expr(&self) -> Expr {
        match self {
            Loc::Local(local) => Expr::local(*local, None),
            Loc::TupleProj(var, proj) => {
                proj.iter()
                    .copied()
                    .fold(var.to_expr(), |e, p| Expr::tuple_proj(e, p, None))
            }
        }
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
                Expr::binary_op(BinOp::$op, self, rhs, None)
            }
        }

        impl<Rhs> std::ops::$op<Rhs> for &Expr
        where
            Rhs: Into<Expr>,
        {
            type Output = Expr;

            fn $method(self, rhs: Rhs) -> Self::Output {
                Expr::binary_op(BinOp::$op, self, rhs, None)
            }
        }
    )*};
}
impl_ops!(Add: add, Sub: sub, Mul: mul, Div: div);

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

impl From<DebruijnIndex> for Expr {
    fn from(bvar: DebruijnIndex) -> Self {
        Expr::late_bvar(bvar)
    }
}

impl From<Loc> for Path {
    fn from(loc: Loc) -> Self {
        Path::new(loc, vec![])
    }
}

impl From<Name> for Loc {
    fn from(name: Name) -> Self {
        Loc::TupleProj(Var::Free(name), List::from(vec![]))
    }
}

impl From<Local> for Loc {
    fn from(local: Local) -> Self {
        Loc::Local(local)
    }
}

impl_internable!(ExprS, [Expr], [KVar], [u32], [FieldIdx]);

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
                ExprKind::Var(var) => w!("{:?}", var),
                ExprKind::Local(local) => w!("{:?}", ^local),
                ExprKind::ConstDefId(did) => w!("{}", ^pretty::def_id_to_string(*did)),
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
                    if let [e] = &exprs[..] {
                        w!("({:?},)", e)
                    } else {
                        w!("({:?})", join!(", ", exprs))
                    }
                }
                ExprKind::PathProj(e, field) => {
                    if e.is_binary_op() {
                        w!("({:?}).{:?}", e, field)
                    } else {
                        w!("{:?}.{:?}", e, field)
                    }
                }
                ExprKind::App(func, arg) => {
                    w!("{:?}({:?})", func, arg)
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
                ExprKind::Abs(body) => {
                    w!("{:?}", body)
                }
                ExprKind::GlobalFunc(func, _) => w!("{}", ^func),
            }
        }
    }

    impl Pretty for Var {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                Var::LateBound(bvar) => w!("{:?}", bvar),
                Var::EarlyBound(idx) => w!("#{}", ^idx),
                Var::Free(name) => w!("{:?}", ^name),
                Var::EVar(evar) => w!("{:?}", evar),
            }
        }
    }

    impl Pretty for KVar {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!("{:?}", ^self.kvid)?;
            match cx.kvar_args {
                KVarArgs::All => {
                    w!("({:?})[{:?}]", join!(", ", self.self_args()), join!(", ", self.scope()))?;
                }
                KVarArgs::SelfOnly => w!("({:?})", join!(", ", self.self_args()))?,
                KVarArgs::Hide => {}
            }
            Ok(())
        }
    }

    impl Pretty for Path {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!("{:?}", &self.loc)?;
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
                Loc::TupleProj(var, proj) => {
                    w!("{:?}", var)?;
                    for field in proj.iter() {
                        w!(".{}", ^field)?;
                    }
                    Ok(())
                }
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

    impl_debug_with_default_cx!(Expr, Loc, Path, Var, KVar);
}
