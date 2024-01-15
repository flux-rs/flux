use std::{fmt, sync::OnceLock};

use flux_common::bug;
pub use flux_fixpoint::{BinOp, Constant, UnOp};
use itertools::Itertools;
use rustc_hir::def_id::DefId;
use rustc_index::newtype_index;
use rustc_macros::{Decodable, Encodable, TyDecodable, TyEncodable};
use rustc_middle::mir::Local;
use rustc_span::{BytePos, Span, Symbol, SyntaxContext};
use rustc_target::abi::FieldIdx;
use rustc_type_ir::{DebruijnIndex, INNERMOST};

use super::{evars::EVar, AliasPred, BaseTy, Binder, IntTy, Sort, UintTy};
use crate::{
    fhir::FuncKind,
    intern::{impl_internable, impl_slice_internable, Interned, List},
    rty::fold::{TypeFoldable, TypeFolder, TypeSuperFoldable},
};

pub type Expr = Interned<ExprS>;

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub struct ExprS {
    kind: ExprKind,
    espan: Option<ESpan>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, TyEncodable, TyDecodable, Debug)]
pub struct ESpan {
    /// The top-level span information
    span: SpanData,
    /// The span for the (base) call-site for def-expanded spans
    base: Option<SpanData>,
}

impl ESpan {
    pub fn new(span: Span) -> Self {
        Self { span: SpanData::new(span), base: None }
    }

    pub fn span(&self) -> Span {
        self.span.span()
    }

    pub fn base(&self) -> Option<Span> {
        self.base.as_ref().map(SpanData::span)
    }

    pub fn with_base(&self, espan: ESpan) -> Self {
        Self { span: self.span, base: Some(espan.span) }
    }
}

// NOTE: we make our own "version" of `rustc`'s SpanData as we cannot `TyEncode/Decode`
// the original one...
#[derive(Clone, Copy, PartialEq, Eq, Hash, TyEncodable, TyDecodable, Debug)]
pub struct SpanData {
    pub lo: BytePos,
    pub hi: BytePos,
}

impl SpanData {
    pub fn new(span: Span) -> Self {
        let data = span.data();
        Self { lo: data.lo, hi: data.hi }
    }

    pub fn span(&self) -> Span {
        Span::new(self.lo, self.hi, SyntaxContext::root(), None)
    }
}

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub enum ExprKind {
    Var(Var),
    Local(Local),
    Constant(Constant),
    ConstDefId(DefId),
    BinaryOp(BinOp, Expr, Expr),
    App(Expr, List<Expr>),
    GlobalFunc(Symbol, FuncKind),
    UnaryOp(UnOp, Expr),
    FieldProj(Expr, FieldProj),
    Aggregate(AggregateKind, List<Expr>),
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
    /// A hole is an expression that must be inferred either *semantically* by generating a kvar or
    /// *syntactically* by generating an evar. Whether a hole can be inferred semantically or syntactically
    /// depends on the position it appears: only holes appearing in predicate position can be inferred
    /// with a kvar (provided it satisfy the fixpoint horn constraints) and only holes used as a refinement
    /// argument or index (a position that fully determines their value) can be inferred with an evar.
    ///
    /// Holes are implicitly defined in a scope, i.e., their solution could mention free and bound variables
    /// in this scope. This must be considered when generating an inference variables for them (either evar or kvar).
    /// In fact, the main reason we have holes is that we want to decouple the places where we generate them,
    /// (where we don't want to worry about the scope) and the places where we infer them (where we do need to worry
    /// about the scope).
    Hole(HoleKind),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, TyEncodable, TyDecodable, Debug)]
pub enum AggregateKind {
    Tuple,
    Adt(DefId),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, TyEncodable, TyDecodable, Debug)]
pub enum FieldProj {
    Tuple { arity: usize, field: u32 },
    Adt { def_id: DefId, field: u32 },
}

impl FieldProj {
    pub fn field(&self) -> u32 {
        match self {
            FieldProj::Tuple { field, .. } | FieldProj::Adt { field, .. } => *field,
        }
    }
}

/// The position where a hole appears. This determines how it will be inferred. This is related but not
/// quite the same as the [`InferMode`].
///
/// [`InferMode`]: super::InferMode
#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable, Debug)]
pub enum HoleKind {
    /// A hole in predicate position (e.g., the predicate in a [`TyKind::Constr`]). It will be inferred by
    /// generating a kvar.
    ///
    /// [`TyKind::Constr`]: super::TyKind::Constr
    Pred,
    /// A hole used as a refinement argument or index. It will be inferred by generating an evar. The
    /// expression filling the hole must have the provided sort.
    Expr(Sort),
}

/// In theory a kvar is just an unknown predicate that can use some variables in scope. In practice,
/// fixpoint makes a diference between the first and the rest of the arguments, the first one being
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
    LateBound(DebruijnIndex, u32),
    EarlyBound(u32),
    EVar(EVar),
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Encodable, Decodable)]
pub struct Path {
    pub loc: Loc,
    projection: List<FieldIdx>,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Encodable, Decodable)]
pub enum Loc {
    Local(Local),
    Var(Var),
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
    fn intern_at(self, espan: Option<ESpan>) -> Expr {
        Interned::new(ExprS { kind: self, espan })
    }

    fn intern(self) -> Expr {
        Interned::new(ExprS { kind: self, espan: None })
    }
}

impl Expr {
    pub fn at_base(self, base: Option<ESpan>) -> Expr {
        let kind = self.kind();
        if let Some(espan) = self.espan
            && let Some(base) = base
        {
            kind.clone().intern_at(Some(espan.with_base(base)))
        } else {
            self
        }
    }

    pub fn span(&self) -> Option<ESpan> {
        self.espan.as_ref().copied()
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
        Expr::late_bvar(INNERMOST, 0)
    }

    #[track_caller]
    pub fn expect_adt(&self) -> (DefId, List<Expr>) {
        if let ExprKind::Aggregate(AggregateKind::Adt(def_id), flds) = self.kind() {
            (*def_id, flds.clone())
        } else {
            bug!("expected record, found {self:?}")
        }
    }

    pub fn unit() -> Expr {
        Expr::tuple(List::empty())
    }

    pub fn var(var: Var, espan: Option<ESpan>) -> Expr {
        ExprKind::Var(var).intern_at(espan)
    }

    pub fn fvar(name: Name) -> Expr {
        Var::Free(name).to_expr()
    }

    pub fn evar(evar: EVar) -> Expr {
        Var::EVar(evar).to_expr()
    }

    pub fn late_bvar(bvar: DebruijnIndex, idx: u32) -> Expr {
        Var::LateBound(bvar, idx).to_expr()
    }

    pub fn early_bvar(idx: u32) -> Expr {
        Var::EarlyBound(idx).to_expr()
    }

    pub fn local(local: Local, espan: Option<ESpan>) -> Expr {
        ExprKind::Local(local).intern_at(espan)
    }

    pub fn constant(c: Constant) -> Expr {
        ExprKind::Constant(c).intern()
    }

    pub fn constant_at(c: Constant, espan: Option<ESpan>) -> Expr {
        ExprKind::Constant(c).intern_at(espan)
    }

    pub fn const_def_id(c: DefId, espan: Option<ESpan>) -> Expr {
        ExprKind::ConstDefId(c).intern_at(espan)
    }

    pub fn aggregate(kind: AggregateKind, flds: List<Expr>) -> Expr {
        ExprKind::Aggregate(kind, flds).intern()
    }

    pub fn tuple(flds: List<Expr>) -> Expr {
        Expr::aggregate(AggregateKind::Tuple, flds)
    }

    pub fn record(def_id: DefId, flds: List<Expr>) -> Expr {
        ExprKind::Aggregate(AggregateKind::Adt(def_id), flds).intern()
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
            _ => bug!(),
        }
    }

    pub fn ite(
        p: impl Into<Expr>,
        e1: impl Into<Expr>,
        e2: impl Into<Expr>,
        espan: Option<ESpan>,
    ) -> Expr {
        ExprKind::IfThenElse(p.into(), e1.into(), e2.into()).intern_at(espan)
    }

    pub fn abs(body: Binder<Expr>) -> Expr {
        ExprKind::Abs(body).intern()
    }

    pub fn hole(kind: HoleKind) -> Expr {
        ExprKind::Hole(kind).intern()
    }

    pub fn kvar(kvar: KVar) -> Expr {
        ExprKind::KVar(kvar).intern()
    }

    pub fn binary_op(
        op: BinOp,
        e1: impl Into<Expr>,
        e2: impl Into<Expr>,
        espan: Option<ESpan>,
    ) -> Expr {
        ExprKind::BinaryOp(op, e1.into(), e2.into()).intern_at(espan)
    }

    pub fn unit_adt(def_id: DefId) -> Expr {
        Expr::record(def_id, List::empty())
    }

    pub fn app(func: impl Into<Expr>, args: impl Into<List<Expr>>, espan: Option<ESpan>) -> Expr {
        ExprKind::App(func.into(), args.into()).intern_at(espan)
    }

    pub fn global_func(func: Symbol, kind: FuncKind) -> Expr {
        ExprKind::GlobalFunc(func, kind).intern()
    }

    pub fn unary_op(op: UnOp, e: impl Into<Expr>, espan: Option<ESpan>) -> Expr {
        ExprKind::UnaryOp(op, e.into()).intern_at(espan)
    }

    pub fn eq_at(e1: impl Into<Expr>, e2: impl Into<Expr>, espan: Option<ESpan>) -> Expr {
        ExprKind::BinaryOp(BinOp::Eq, e1.into(), e2.into()).intern_at(espan)
    }

    pub fn eq(e1: impl Into<Expr>, e2: impl Into<Expr>) -> Expr {
        Self::eq_at(e1, e2, None)
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

    pub fn field_proj(e: impl Into<Expr>, proj: FieldProj, espan: Option<ESpan>) -> Expr {
        ExprKind::FieldProj(e.into(), proj).intern_at(espan)
    }

    pub fn field_projs(e: impl Into<Expr>, projs: &[FieldProj]) -> Expr {
        projs
            .iter()
            .copied()
            .fold(e.into(), |e, p| Expr::field_proj(e, p, None))
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
        !matches!(self.kind, ExprKind::Abs(..) | ExprKind::BinaryOp(..))
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
                        let e1_span = e1.span();
                        let e2_span = e2.span();
                        match (op, e1.kind(), e2.kind()) {
                            (BinOp::And, ExprKind::Constant(Constant::Bool(false)), _) => {
                                Expr::constant_at(Constant::Bool(false), e1_span)
                            }
                            (BinOp::And, _, ExprKind::Constant(Constant::Bool(false))) => {
                                Expr::constant_at(Constant::Bool(false), e2_span)
                            }
                            (BinOp::And, ExprKind::Constant(Constant::Bool(true)), _) => e2,
                            (BinOp::And, _, ExprKind::Constant(Constant::Bool(true))) => e1,
                            (op, ExprKind::Constant(c1), ExprKind::Constant(c2)) => {
                                let e2_span = e2.span();
                                match Expr::const_op(op, c1, c2) {
                                    Some(c) => Expr::constant_at(c, span.or(e2_span)),
                                    None => Expr::binary_op(*op, e1, e2, span),
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

    pub fn to_loc(&self) -> Option<Loc> {
        match self.kind() {
            ExprKind::Local(local) => Some(Loc::Local(*local)),
            ExprKind::Var(var) => Some(Loc::Var(*var)),
            _ => None,
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

    pub fn eta_expand_abs(&self, sorts: &[Sort]) -> Binder<Expr> {
        let args = (0..sorts.len())
            .map(|idx| Expr::late_bvar(INNERMOST, idx as u32))
            .collect_vec();
        Binder::with_sorts(Expr::app(self, args, None), sorts.iter().cloned())
    }

    pub fn fold_sort(sort: &Sort, mut f: impl FnMut(&Sort) -> Expr) -> Expr {
        fn go(sort: &Sort, f: &mut impl FnMut(&Sort) -> Expr) -> Expr {
            match sort {
                Sort::Tuple(sorts) => Expr::tuple(sorts.iter().map(|sort| go(sort, f)).collect()),
                Sort::Adt(adt_sort_def, args) => {
                    let flds = adt_sort_def.sorts(args);
                    Expr::record(adt_sort_def.did(), flds.iter().map(|sort| go(sort, f)).collect())
                }
                _ => f(sort),
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

    pub fn projection(&self) -> &[FieldIdx] {
        &self.projection[..]
    }

    pub fn to_expr(&self) -> Expr {
        self.projection
            .iter()
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
            Loc::Local(local) => Expr::local(*local, None),
            Loc::Var(var) => Expr::var(*var, None),
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
        Expr::constant(Constant::from(value))
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

impl From<AliasPred> for Expr {
    fn from(pred: AliasPred) -> Self {
        Expr::global_func(pred.name, FuncKind::Asp)
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

impl_internable!(ExprS);
impl_slice_internable!(Expr, KVar, u32, FieldIdx);

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
                    if e.is_atom() {
                        w!("{:?}{:?}", op, e)
                    } else {
                        w!("{:?}({:?})", op, e)
                    }
                }
                ExprKind::FieldProj(e, proj) => {
                    if e.is_atom() {
                        w!("{:?}.{:?}", e, ^proj.field())
                    } else {
                        w!("({:?}).{:?}", e, ^proj.field())
                    }
                }
                ExprKind::Aggregate(AggregateKind::Tuple, flds) => {
                    if let [e] = &flds[..] {
                        w!("({:?},)", e)
                    } else {
                        w!("({:?})", join!(", ", flds))
                    }
                }
                ExprKind::Aggregate(AggregateKind::Adt(def_id), flds) => {
                    w!("{:?} {{ {:?} }}", def_id, join!(", ", flds))
                }
                ExprKind::PathProj(e, field) => {
                    if e.is_atom() {
                        w!("{:?}.{:?}", e, field)
                    } else {
                        w!("({:?}).{:?}", e, field)
                    }
                }
                ExprKind::App(func, args) => {
                    w!("{:?}({})",
                        func,
                        ^args
                            .iter()
                            .format_with(", ", |arg, f| f(&format_args_cx!("{:?}", arg)))
                    )
                }
                ExprKind::IfThenElse(p, e1, e2) => {
                    w!("if {:?} {{ {:?} }} else {{ {:?} }}", p, e1, e2)
                }
                ExprKind::Hole(_) => {
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
                Var::LateBound(bvar, idx) => w!("{:?}#{}", bvar, ^idx),
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
            for field in &self.projection {
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
