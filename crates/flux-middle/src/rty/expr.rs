use std::{fmt, sync::OnceLock};

use flux_common::bug;
pub use flux_fixpoint::Constant;
use itertools::Itertools;
use rustc_hir::def_id::DefId;
use rustc_index::newtype_index;
use rustc_macros::{Decodable, Encodable, TyDecodable, TyEncodable};
use rustc_middle::{
    mir::Local,
    ty::{ParamConst, TyCtxt},
};
use rustc_span::{Span, Symbol};
use rustc_target::abi::FieldIdx;
use rustc_type_ir::{BoundVar, DebruijnIndex, INNERMOST};

use super::{
    evars::EVar, BaseTy, Binder, BoundReftKind, BoundVariableKind, FuncSort, GenericArgs, IntTy,
    Sort, UintTy,
};
use crate::{
    const_eval,
    fhir::SpecFuncKind,
    global_env::GlobalEnv,
    intern::{impl_internable, impl_slice_internable, Interned, List},
    queries::QueryResult,
    rty::{
        fold::{TypeFoldable, TypeFolder, TypeSuperFoldable},
        SortCtor,
    },
    rustc::ty::{Const, ConstKind},
};

/// A lambda abstraction with an elaborated output sort
#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub struct Lambda {
    pub(super) body: Binder<Expr>,
    pub(super) output: Sort,
}

impl Lambda {
    pub fn with_vars(body: Expr, inputs: List<BoundVariableKind>, output: Sort) -> Self {
        Self { body: Binder::new(body, inputs), output }
    }

    pub fn with_sorts(body: Expr, inputs: &[Sort], output: Sort) -> Self {
        Self { body: Binder::with_sorts(body, inputs), output }
    }

    pub fn apply(&self, args: &[Expr]) -> Expr {
        self.body.replace_bound_refts(args)
    }

    pub fn inputs(&self) -> List<Sort> {
        self.body.vars().to_sort_list()
    }

    pub fn output(&self) -> Sort {
        self.output.clone()
    }

    pub fn sort(&self) -> FuncSort {
        FuncSort::new(self.inputs().to_vec(), self.output())
    }
}

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub struct AliasReft {
    pub trait_id: DefId,
    pub name: Symbol,
    pub args: GenericArgs,
}

impl AliasReft {
    pub fn to_rustc_trait_ref<'tcx>(&self, tcx: TyCtxt<'tcx>) -> rustc_middle::ty::TraitRef<'tcx> {
        let trait_def_id = self.trait_id;
        let args = self
            .args
            .to_rustc(tcx)
            .truncate_to(tcx, tcx.generics_of(trait_def_id));
        rustc_middle::ty::TraitRef::new(tcx, trait_def_id, args)
    }
}

pub type Expr = Interned<ExprS>;

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub struct ExprS {
    kind: ExprKind,
    espan: Option<ESpan>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, TyEncodable, TyDecodable, Debug)]
pub struct ESpan {
    /// The top-level span information
    pub span: Span,
    /// The span for the (base) call-site for def-expanded spans
    pub base: Option<Span>,
}

impl ESpan {
    pub fn new(span: Span) -> Self {
        Self { span, base: None }
    }

    pub fn with_base(&self, espan: ESpan) -> Self {
        Self { span: self.span, base: Some(espan.span) }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub enum BinOp {
    Iff,
    Imp,
    Or,
    And,
    Eq,
    Ne,
    Gt(Sort),
    Ge(Sort),
    Lt(Sort),
    Le(Sort),
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Encodable, Decodable)]
pub enum UnOp {
    Not,
    Neg,
}

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub enum ExprKind {
    Var(Var),
    Local(Local),
    Constant(Constant),
    ConstDefId(DefId),
    BinaryOp(BinOp, Expr, Expr),
    GlobalFunc(Symbol, SpecFuncKind),
    UnaryOp(UnOp, Expr),
    FieldProj(Expr, FieldProj),
    Aggregate(AggregateKind, List<Expr>),
    PathProj(Expr, FieldIdx),
    IfThenElse(Expr, Expr, Expr),
    KVar(KVar),
    Alias(AliasReft, List<Expr>),
    /// Function application. The syntax allows arbitrary expressions in function position, but in
    /// practice we are restricted by what's possible to encode in fixpoint. In a nutshell, we need
    /// to make sure that expressions that can't be encoded are eliminated before we generate the
    /// fixpoint constraint. Most notably, lambda abstractions have to be fully applied before
    /// encoding into fixpoint (except when they appear as an index at the top-level).
    App(Expr, List<Expr>),
    /// Lambda abstractions. They are purely syntactic and we don't encode them in the logic. As such,
    /// they have some syntactic restrictions that we must carefully maintain:
    ///
    /// 1. They can appear as an index at the top level.
    /// 2. We can only substitute an abstraction for a variable in function position (or as an index).
    ///    More generaly, we need to partially evaluate expressions such that all abstractions in
    ///    non-index position are eliminated before encoding into fixpoint. Right now, the
    ///    implementation only evaluates abstractions that are immediately applied to arguments,
    ///    thus the restriction.
    Abs(Lambda),
    /// A hole is an expression that must be inferred either *semantically* by generating a kvar or
    /// *syntactically* by generating an evar. Whether a hole can be inferred semantically or
    /// syntactically depends on the position it appears: only holes appearing in predicate position
    /// can be inferred with a kvar (provided it satisfies the fixpoint horn constraints) and only
    /// holes used as an index (a position that fully determines their value) can be inferred with
    /// an evar.
    ///
    /// Holes are implicitly defined in a scope, i.e., their solution could mention free and bound
    /// variables in this scope. This must be considered when generating an inference variables for
    /// them (either evar or kvar). In fact, the main reason we have holes is that we want to
    /// decouple the places where we generate holes (where we don't want to worry about the scope),
    /// and the places where we generate inference variable for them (where we do need to worry
    /// about the scope).
    Hole(HoleKind),
    ForAll(Binder<Expr>),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, TyEncodable, TyDecodable, Debug)]
pub enum AggregateKind {
    Tuple(usize),
    Adt(DefId),
}

impl AggregateKind {
    pub fn to_proj(self, field: u32) -> FieldProj {
        match self {
            AggregateKind::Tuple(arity) => FieldProj::Tuple { arity, field },
            AggregateKind::Adt(def_id) => FieldProj::Adt { def_id, field },
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, TyEncodable, TyDecodable, Debug)]
pub enum FieldProj {
    Tuple { arity: usize, field: u32 },
    Adt { def_id: DefId, field: u32 },
}

impl FieldProj {
    pub fn arity(&self, genv: GlobalEnv) -> QueryResult<usize> {
        match self {
            FieldProj::Tuple { arity, .. } => Ok(*arity),
            FieldProj::Adt { def_id, .. } => Ok(genv.adt_sort_def_of(*def_id)?.fields()),
        }
    }

    pub fn field_idx(&self) -> u32 {
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
pub struct EarlyReftParam {
    pub index: u32,
    pub name: Symbol,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Encodable, Decodable, Debug)]
pub struct BoundReft {
    pub var: BoundVar,
    pub kind: BoundReftKind,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, TyEncodable, TyDecodable)]
pub enum Var {
    Free(Name),
    Bound(DebruijnIndex, BoundReft),
    EarlyParam(EarlyReftParam),
    EVar(EVar),
    ConstGeneric(ParamConst),
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, TyEncodable, TyDecodable)]
pub struct Path {
    pub loc: Loc,
    projection: List<FieldIdx>,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, TyEncodable, TyDecodable)]
pub enum Loc {
    Local(Local),
    Var(Var),
}

newtype_index! {
    #[debug_format = "$k{}"]
    #[encodable]
    pub struct KVid {}
}

newtype_index! {
    #[debug_format = "a{}"]
    #[orderable]
    #[encodable]
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

    pub fn and_iter(exprs: impl IntoIterator<Item = Expr>) -> Expr {
        exprs
            .into_iter()
            .reduce(|acc, e| Expr::binary_op(BinOp::And, acc, e, None))
            .unwrap_or_else(Expr::tt)
    }

    pub fn and(e1: impl Into<Expr>, e2: impl Into<Expr>) -> Expr {
        Expr::and_iter([e1.into(), e2.into()])
    }

    pub fn or_from_iter(exprs: impl IntoIterator<Item = Expr>) -> Expr {
        exprs
            .into_iter()
            .reduce(|acc, e| Expr::binary_op(BinOp::Or, acc, e, None))
            .unwrap_or_else(Expr::ff)
    }

    pub fn or(e1: impl Into<Expr>, e2: impl Into<Expr>) -> Expr {
        Expr::or_from_iter([e1.into(), e2.into()])
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
        Expr::bvar(INNERMOST, BoundVar::ZERO, BoundReftKind::Annon)
    }

    pub fn is_nu(&self) -> bool {
        if let ExprKind::Var(Var::Bound(INNERMOST, var)) = self.kind()
            && var.var == BoundVar::ZERO
        {
            true
        } else {
            false
        }
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

    pub fn bvar(debruijn: DebruijnIndex, var: BoundVar, kind: BoundReftKind) -> Expr {
        Var::Bound(debruijn, BoundReft { var, kind }).to_expr()
    }

    pub fn early_param(index: u32, name: Symbol) -> Expr {
        Var::EarlyParam(EarlyReftParam { index, name }).to_expr()
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

    pub fn const_generic(param: ParamConst, espan: Option<ESpan>) -> Expr {
        ExprKind::Var(Var::ConstGeneric(param)).intern_at(espan)
    }

    pub fn aggregate(kind: AggregateKind, flds: List<Expr>) -> Expr {
        ExprKind::Aggregate(kind, flds).intern()
    }

    pub fn tuple(flds: List<Expr>) -> Expr {
        Expr::aggregate(AggregateKind::Tuple(flds.len()), flds)
    }

    pub fn adt(def_id: DefId, flds: List<Expr>) -> Expr {
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

    pub fn abs(lam: Lambda) -> Expr {
        ExprKind::Abs(lam).intern()
    }

    pub fn hole(kind: HoleKind) -> Expr {
        ExprKind::Hole(kind).intern()
    }

    pub fn kvar(kvar: KVar) -> Expr {
        ExprKind::KVar(kvar).intern()
    }

    pub fn alias(alias: AliasReft, args: List<Expr>) -> Expr {
        ExprKind::Alias(alias, args).intern()
    }

    pub fn forall(expr: Binder<Expr>) -> Expr {
        ExprKind::ForAll(expr).intern()
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
        Expr::adt(def_id, List::empty())
    }

    pub fn app(func: impl Into<Expr>, args: impl Into<List<Expr>>, espan: Option<ESpan>) -> Expr {
        ExprKind::App(func.into(), args.into()).intern_at(espan)
    }

    pub fn global_func(func: Symbol, kind: SpecFuncKind) -> Expr {
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
        ExprKind::BinaryOp(BinOp::Ge(Sort::Int), e1.into(), e2.into()).intern()
    }

    pub fn gt(e1: impl Into<Expr>, e2: impl Into<Expr>) -> Expr {
        ExprKind::BinaryOp(BinOp::Gt(Sort::Int), e1.into(), e2.into()).intern()
    }

    pub fn lt(e1: impl Into<Expr>, e2: impl Into<Expr>) -> Expr {
        ExprKind::BinaryOp(BinOp::Lt(Sort::Int), e1.into(), e2.into()).intern()
    }

    pub fn le(e1: impl Into<Expr>, e2: impl Into<Expr>) -> Expr {
        ExprKind::BinaryOp(BinOp::Le(Sort::Int), e1.into(), e2.into()).intern()
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
        !matches!(self.kind, ExprKind::Abs(..) | ExprKind::BinaryOp(..) | ExprKind::ForAll(..))
    }

    /// Simple syntactic check to see if the expression is a trivially true predicate. This is used
    /// mostly for filtering predicates when pretty printing but also to simplify types in general.
    pub fn is_trivially_true(&self) -> bool {
        self.is_true()
            || matches!(self.kind(), ExprKind::BinaryOp(BinOp::Eq | BinOp::Iff | BinOp::Imp, e1, e2) if e1 == e2)
    }

    /// Whether the expression is *literally* the constant true.
    fn is_true(&self) -> bool {
        matches!(self.kind, ExprKind::Constant(Constant::Bool(true)))
    }

    pub fn from_const(tcx: TyCtxt, c: &Const) -> Expr {
        match &c.kind {
            ConstKind::Param(param_const) => Expr::const_generic(*param_const, None),
            ConstKind::Value(ty, scalar) => {
                let val = const_eval::scalar_int_to_rty_constant2(tcx, *scalar, ty).unwrap();
                Expr::constant(val)
            }
            ConstKind::Infer(_) => bug!("unexpected `ConstKind::Infer`"),
        }
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
            BinOp::Gt(Sort::Int) => c1.gt(c2),
            BinOp::Ge(Sort::Int) => c1.ge(c2),
            BinOp::Lt(Sort::Int) => c2.gt(c1),
            BinOp::Le(Sort::Int) => c2.ge(c1),
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
                                    None => Expr::binary_op(op.clone(), e1, e2, span),
                                }
                            }
                            _ => Expr::binary_op(op.clone(), e1, e2, span),
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

    /// Wether this is an aggregate expression with no fields.
    pub fn is_unit(&self) -> bool {
        matches!(self.kind(), ExprKind::Aggregate(_, flds) if flds.is_empty())
    }

    pub fn eta_expand_abs(&self, inputs: &[Sort], output: Sort) -> Lambda {
        let args = (0..inputs.len())
            .map(|idx| Expr::bvar(INNERMOST, BoundVar::from_usize(idx), BoundReftKind::Annon))
            .collect_vec();
        let body = Expr::app(self, args, None);
        Lambda::with_sorts(body, inputs, output)
    }

    pub fn fold_sort(sort: &Sort, mut f: impl FnMut(&Sort) -> Expr) -> Expr {
        fn go(sort: &Sort, f: &mut impl FnMut(&Sort) -> Expr) -> Expr {
            match sort {
                Sort::Tuple(sorts) => Expr::tuple(sorts.iter().map(|sort| go(sort, f)).collect()),
                Sort::App(SortCtor::Adt(adt_sort_def), args) => {
                    let flds = adt_sort_def.sorts(args);
                    Expr::adt(adt_sort_def.did(), flds.iter().map(|sort| go(sort, f)).collect())
                }
                _ => f(sort),
            }
        }
        go(sort, &mut f)
    }

    /// Applies a projection to an expression and optimistically try to beta reduce it if possible.
    pub fn proj_and_reduce(&self, proj: FieldProj) -> Expr {
        match self.kind() {
            ExprKind::Aggregate(_, flds) => flds[proj.field_idx() as usize].clone(),
            _ => Expr::field_proj(self.clone(), proj, None),
        }
    }

    pub fn flatten_conjs(&self) -> Vec<&Expr> {
        fn go<'a>(e: &'a Expr, vec: &mut Vec<&'a Expr>) {
            if let ExprKind::BinaryOp(BinOp::And, e1, e2) = e.kind() {
                go(e1, vec);
                go(e2, vec);
            } else {
                vec.push(e);
            }
        }
        let mut vec = vec![];
        go(self, &mut vec);
        vec
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

impl From<Var> for Expr {
    fn from(var: Var) -> Self {
        Expr::var(var, None)
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
    enum Precedence {
        Iff,
        Imp,
        Or,
        And,
        Cmp,
        AddSub,
        MulDiv,
    }

    impl BinOp {
        fn precedence(&self) -> Precedence {
            match self {
                BinOp::Iff => Precedence::Iff,
                BinOp::Imp => Precedence::Imp,
                BinOp::Or => Precedence::Or,
                BinOp::And => Precedence::And,
                BinOp::Eq
                | BinOp::Ne
                | BinOp::Gt(_)
                | BinOp::Lt(_)
                | BinOp::Ge(_)
                | BinOp::Le(_) => Precedence::Cmp,
                BinOp::Add | BinOp::Sub => Precedence::AddSub,
                BinOp::Mul | BinOp::Div | BinOp::Mod => Precedence::MulDiv,
            }
        }
    }

    impl Precedence {
        pub fn is_associative(&self) -> bool {
            !matches!(self, Precedence::Imp | Precedence::Cmp)
        }
    }

    impl Pretty for Expr {
        fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            fn should_parenthesize(op: &BinOp, child: &Expr) -> bool {
                if let ExprKind::BinaryOp(child_op, ..) = child.kind() {
                    child_op.precedence() < op.precedence()
                        || (child_op.precedence() == op.precedence()
                            && !op.precedence().is_associative())
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
                        w!("{:?}.{:?}", e, ^proj.field_idx())
                    } else {
                        w!("({:?}).{:?}", e, ^proj.field_idx())
                    }
                }
                ExprKind::Aggregate(AggregateKind::Tuple(_), flds) => {
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
                    w!("({:?})({})",
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
                ExprKind::Alias(alias, args) => {
                    w!("{:?}({:?})", alias, join!(", ", args))
                }
                ExprKind::Abs(lam) => {
                    w!("{:?}", lam)
                }
                ExprKind::GlobalFunc(func, _) => w!("{}", ^func),
                ExprKind::ForAll(expr) => {
                    let vars = expr.vars();
                    cx.with_bound_vars(vars, || {
                        if !vars.is_empty() {
                            cx.fmt_bound_vars("∀", vars, ". ", f)?;
                        }
                        w!("{:?}", expr.as_ref().skip_binder())
                    })
                }
            }
        }
    }

    impl Pretty for AliasReft {
        fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!("<({:?}) as {:?}", &self.args[0], self.trait_id)?;
            let args = &self.args[1..];
            if !args.is_empty() {
                w!("<{:?}>", join!(", ", args))?;
            }
            w!(">::{}", ^self.name)
        }
    }

    impl Pretty for Lambda {
        fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            let vars = self.body.vars();
            cx.with_bound_vars(vars, || {
                cx.fmt_bound_vars("λ", vars, ". ", f)?;
                w!("{:?}", self.body.as_ref().skip_binder())
            })
        }
    }

    impl Pretty for Var {
        fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                Var::Bound(debruijn, var) => cx.fmt_bound_reft(*debruijn, *var, f),
                Var::EarlyParam(var) => w!("{}", ^var.name),
                Var::Free(name) => w!("{:?}", ^name),
                Var::EVar(evar) => w!("{:?}", evar),
                Var::ConstGeneric(param) => w!("{}", ^param.name),
            }
        }
    }

    impl Pretty for KVar {
        fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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
        fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!("{:?}", &self.loc)?;
            for field in &self.projection {
                w!(".{}", ^u32::from(*field))?;
            }
            Ok(())
        }
    }

    impl Pretty for Loc {
        fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                Loc::Local(local) => w!("{:?}", ^local),
                Loc::Var(var) => w!("{:?}", var),
            }
        }
    }

    impl Pretty for BinOp {
        fn fmt(&self, _cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                BinOp::Iff => w!("⇔"),
                BinOp::Imp => w!("⇒"),
                BinOp::Or => w!("∨"),
                BinOp::And => w!("∧"),
                BinOp::Eq => w!("="),
                BinOp::Ne => w!("≠"),
                BinOp::Gt(_) => w!(">"),
                BinOp::Ge(_) => w!("≥"),
                BinOp::Lt(_) => w!("<"),
                BinOp::Le(_) => w!("≤"),
                BinOp::Add => w!("+"),
                BinOp::Sub => w!("-"),
                BinOp::Mul => w!("*"),
                BinOp::Div => w!("/"),
                BinOp::Mod => w!("mod"),
            }
        }
    }

    impl Pretty for UnOp {
        fn fmt(&self, _cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                UnOp::Not => w!("¬"),
                UnOp::Neg => w!("-"),
            }
        }
    }

    impl_debug_with_default_cx!(Expr, Loc, Path, Var, KVar, Lambda, AliasReft);
}
