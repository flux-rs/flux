pub mod fold;
pub mod lowering;
pub mod subst;

use std::{borrow::Cow, fmt, iter, sync::OnceLock};

use flux_common::index::IndexGen;
use itertools::Itertools;

pub use flux_fixpoint::{BinOp, Constant, UnOp};
use rustc_hir::def_id::DefId;
use rustc_index::newtype_index;
use rustc_middle::mir::{Field, Local};
pub use rustc_middle::ty::{AdtFlags, FloatTy, IntTy, ParamTy, UintTy};
pub use rustc_target::abi::VariantIdx;

pub use crate::core::RefKind;
use crate::{
    intern::{impl_internable, Interned, List},
    rustc::mir::{Place, PlaceElem},
};

use self::{fold::TypeFoldable, subst::BVarFolder};

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct AdtDef(Interned<AdtDefData>);

#[derive(Debug, Eq, PartialEq, Hash)]
pub struct AdtDefData {
    def_id: DefId,
    sorts: List<Sort>,
    flags: AdtFlags,
}

#[derive(Clone, Eq, PartialEq, Hash)]
pub(crate) struct VariantDef {
    pub(crate) fields: List<Ty>,
    pub(crate) ret: Ty,
}

#[derive(Clone, Eq, PartialEq, Hash)]
pub struct Binders<T> {
    params: List<Sort>,
    value: T,
}

pub type PolySig = Binders<FnSig>;
#[derive(Clone)]
pub struct FnSig {
    requires: List<Constraint>,
    args: List<Ty>,
    ret: Ty,
    ensures: List<Constraint>,
}

pub type Constraints = List<Constraint>;

#[derive(Clone, Eq, PartialEq, Hash)]
pub enum Constraint {
    Type(Path, Ty),
    Pred(Expr),
}

#[derive(Debug)]
pub struct Qualifier {
    pub name: String,
    pub args: Vec<(Name, Sort)>,
    pub expr: Expr,
}

pub type Ty = Interned<TyS>;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct TyS {
    kind: TyKind,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum TyKind {
    Indexed(BaseTy, List<Index>),
    Exists(BaseTy, Binders<Pred>),
    Tuple(List<Ty>),
    Float(FloatTy),
    Uninit,
    Ptr(Path),
    /// A pointer to a location produced by opening a box. This mostly behaves like a [`TyKind::Ptr`],
    /// with two major differences:
    /// 1. An open box can only point to a fresh location and not an arbitrary [`Path`], so we just
    ///    store a [`Name`].
    /// 2. We keep around the allocator to be able to put the box back together (you could say that
    ///    the capability to deallocate the memory stays with the pointer).
    BoxPtr(Name, Ty),
    Ref(RefKind, Ty),
    Constr(Expr, Ty),
    Param(ParamTy),
    Never,
    /// This is a bit of a hack. We use this type internally to represent the result of
    /// [`Rvalue::Discriminant`] in a way that we can recover the necessary control information
    /// when checking [`TerminatorKind::SwitchInt`].
    ///
    /// [`Rvalue::Discriminant`]: crate::rustc::mir::Rvalue::Discriminant
    /// [`TerminatorKind::SwitchInt`]: crate::rustc::mir::TerminatorKind::SwitchInt
    Discr(Place),
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Index {
    pub expr: Expr,
    /// Whether the index was annotated as a binder in the surface. This is used as a hint for inferring
    /// parameters at call sites. This is very hacky and we should have a different way to preserve this
    /// information. The problem is that the extra field is preserved through substitutions and other
    /// manipulations of types which makes it problematic to test for index equality.
    pub is_binder: bool,
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Path {
    pub loc: Loc,
    projection: List<Field>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Loc {
    Local(Local),
    Free(Name),
    Bound(BoundVar),
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum BaseTy {
    Int(IntTy),
    Uint(UintTy),
    Bool,
    Adt(AdtDef, Substs),
}

pub type Substs = List<Ty>;

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Pred {
    Hole,
    Kvars(List<KVar>),
    Expr(Expr),
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct KVar {
    pub kvid: KVid,
    pub args: List<Expr>,
    pub scope: List<Expr>,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Sort {
    Int,
    Bool,
    Loc,
    Tuple(List<Sort>),
}

pub type Expr = Interned<ExprS>;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct ExprS {
    kind: ExprKind,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum ExprKind {
    ConstDefId(DefId),
    FreeVar(Name),
    BoundVar(BoundVar),
    Local(Local),
    Constant(Constant),
    BinaryOp(BinOp, Expr, Expr),
    UnaryOp(UnOp, Expr),
    TupleProj(Expr, u32),
    Tuple(List<Expr>),
    PathProj(Expr, Field),
}

/// A bound *var*riable is represented as a debruijn index
/// into a list of [`Binders`] and index into that list.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BoundVar {
    pub debruijn: DebruijnIndex,
    pub index: usize,
}

newtype_index! {
    pub struct KVid {
        DEBUG_FORMAT = "$k{}"
    }
}

newtype_index! {
    pub struct Name {
        DEBUG_FORMAT = "a{}",
    }
}

newtype_index! {
    pub struct DebruijnIndex {
        DEBUG_FORMAT = "DebruijnIndex({})",
        const INNERMOST = 0,
    }
}

impl<T> Binders<T> {
    pub fn new(value: T, params: impl Into<List<Sort>>) -> Binders<T> {
        Binders { params: params.into(), value }
    }

    pub fn params(&self) -> &[Sort] {
        &self.params
    }

    pub fn skip_binders(&self) -> &T {
        &self.value
    }
}

impl<T> Binders<T>
where
    T: TypeFoldable,
{
    pub fn replace_bvars_with_fresh_fvars(&self, mut fresh: impl FnMut(&Sort) -> Name) -> T {
        let exprs = self
            .params
            .iter()
            .map(|sort| Expr::fvar(fresh(sort)))
            .collect_vec();
        self.replace_bound_vars(&exprs)
    }

    pub fn replace_bound_vars(&self, exprs: &[Expr]) -> T {
        self.value.fold_with(&mut BVarFolder::new(exprs))
    }
}

impl Binders<Pred> {
    pub fn split_with_fresh_fvars(&self, name_gen: &IndexGen<Name>) -> Vec<(Name, Sort, Pred)> {
        let names = iter::repeat_with(|| name_gen.fresh())
            .take(self.params.len())
            .collect_vec();
        let exprs = names.iter().copied().map(Expr::fvar).collect_vec();
        match self.replace_bound_vars(&exprs) {
            Pred::Hole => {
                iter::zip(names, &self.params)
                    .map(|(name, sort)| (name, sort.clone(), Pred::Hole))
                    .collect()
            }
            Pred::Kvars(kvars) => {
                debug_assert_eq!(kvars.len(), self.params.len());
                itertools::izip!(names, &self.params, &kvars)
                    .map(|(name, sort, kvar)| (name, sort.clone(), Pred::kvars(vec![kvar.clone()])))
                    .collect()
            }
            Pred::Expr(e) => {
                itertools::izip!(names, &self.params)
                    .enumerate()
                    .map(|(idx, (name, sort))| {
                        if idx < self.params.len() - 1 {
                            (name, sort.clone(), Pred::tt())
                        } else {
                            (name, sort.clone(), Pred::Expr(e.clone()))
                        }
                    })
                    .collect()
            }
        }
    }
}

impl FnSig {
    pub fn new<A, B, C>(requires: A, args: B, ret: Ty, ensures: C) -> Self
    where
        List<Constraint>: From<A>,
        List<Ty>: From<B>,
        List<Constraint>: From<C>,
    {
        FnSig {
            requires: Interned::from(requires),
            args: Interned::from(args),
            ret,
            ensures: Interned::from(ensures),
        }
    }
    pub fn requires(&self) -> &Constraints {
        &self.requires
    }

    pub fn args(&self) -> &[Ty] {
        &self.args
    }

    pub fn ret(&self) -> &Ty {
        &self.ret
    }

    pub fn ensures(&self) -> &Constraints {
        &self.ensures
    }
}

impl AdtDef {
    pub fn new(rustc_def: rustc_middle::ty::AdtDef, sorts: impl Into<List<Sort>>) -> Self {
        AdtDef(Interned::new(AdtDefData {
            def_id: rustc_def.did(),
            sorts: sorts.into(),
            flags: rustc_def.flags(),
        }))
    }

    pub fn def_id(&self) -> DefId {
        self.0.def_id
    }

    pub fn sorts(&self) -> &List<Sort> {
        &self.0.sorts
    }

    pub fn flags(&self) -> &AdtFlags {
        &self.0.flags
    }

    pub fn is_box(&self) -> bool {
        self.flags().contains(AdtFlags::IS_BOX)
    }

    pub fn is_enum(&self) -> bool {
        self.flags().contains(AdtFlags::IS_ENUM)
    }

    pub fn is_struct(&self) -> bool {
        self.flags().contains(AdtFlags::IS_STRUCT)
    }
}

impl VariantDef {
    pub fn new(fields: Vec<Ty>, ret: Ty) -> Self {
        VariantDef { fields: List::from_vec(fields), ret }
    }
}

impl Ty {
    pub fn ptr(path: impl Into<Path>) -> Ty {
        TyKind::Ptr(path.into()).intern()
    }

    pub fn box_ptr(loc: Name, alloc: Ty) -> Ty {
        TyKind::BoxPtr(loc, alloc).intern()
    }

    pub fn mk_ref(mode: RefKind, ty: Ty) -> Ty {
        TyKind::Ref(mode, ty).intern()
    }

    pub fn tuple(tys: impl Into<List<Ty>>) -> Ty {
        TyKind::Tuple(tys.into()).intern()
    }

    pub fn constr(p: Expr, ty: Ty) -> Ty {
        TyKind::Constr(p, ty).intern()
    }

    pub fn unconstr(&self) -> &Ty {
        match self.kind() {
            TyKind::Constr(_, ty) => Self::unconstr(ty),
            _ => self,
        }
    }

    pub fn bty(&self) -> Option<&BaseTy> {
        match self.unconstr().kind() {
            TyKind::Indexed(bty, _) | TyKind::Exists(bty, _) => Some(bty),
            _ => None,
        }
    }

    pub fn uninit() -> Ty {
        TyKind::Uninit.intern()
    }

    pub fn indexed<T>(bty: BaseTy, indices: T) -> Ty
    where
        List<Index>: From<T>,
    {
        TyKind::Indexed(bty, Interned::from(indices)).intern()
    }

    pub fn exists(bty: BaseTy, pred: Binders<Pred>) -> Ty {
        TyKind::Exists(bty, pred).intern()
    }

    pub fn float(float_ty: FloatTy) -> Ty {
        TyKind::Float(float_ty).intern()
    }

    pub fn param(param: ParamTy) -> Ty {
        TyKind::Param(param).intern()
    }

    pub fn unit() -> Ty {
        Ty::tuple(vec![])
    }

    pub fn never() -> Ty {
        TyKind::Never.intern()
    }

    pub fn discr(place: Place) -> Ty {
        TyKind::Discr(place).intern()
    }

    pub fn is_box(&self) -> bool {
        match self.kind() {
            TyKind::Indexed(bty, _) | TyKind::Exists(bty, _) => bty.is_box(),
            _ => false,
        }
    }
}

impl TyKind {
    fn intern(self) -> Ty {
        Interned::new(TyS { kind: self })
    }
}

impl TyS {
    pub fn kind(&self) -> &TyKind {
        &self.kind
    }

    pub fn expect_discr(&self) -> &Place {
        if let TyKind::Discr(place) = self.kind() {
            place
        } else {
            panic!("expected discr")
        }
    }

    /// Whether the type is an `int` or a `uint`
    pub fn is_integral(&self) -> bool {
        matches!(self.kind(), TyKind::Indexed(bty, _) | TyKind::Exists(bty, _) if bty.is_integral())
    }

    /// Whether the type is a `bool`
    pub fn is_bool(&self) -> bool {
        matches!(self.kind(), TyKind::Indexed(bty, _) | TyKind::Exists(bty, _) if bty.is_bool())
    }

    pub fn is_uninit(&self) -> bool {
        matches!(self.kind(), TyKind::Uninit)
    }
}

impl List<Index> {
    pub fn to_exprs(&self) -> Vec<Expr> {
        self.iter().map(|idx| idx.to_expr()).collect_vec()
    }
}

impl Index {
    pub fn exprs_eq(idxs1: &[Index], idxs2: &[Index]) -> bool {
        if idxs1.len() != idxs2.len() {
            return false;
        }

        for (idx1, idx2) in iter::zip(idxs1, idxs2) {
            if idx1.expr != idx2.expr {
                return false;
            }
        }
        true
    }

    pub fn to_expr(&self) -> Expr {
        self.expr.clone()
    }
}

impl From<Expr> for Index {
    fn from(expr: Expr) -> Index {
        Index { expr, is_binder: false }
    }
}

impl From<Index> for Expr {
    fn from(index: Index) -> Expr {
        index.expr
    }
}

impl BaseTy {
    pub fn adt(adt_def: AdtDef, substs: impl IntoIterator<Item = Ty>) -> BaseTy {
        BaseTy::Adt(adt_def, Substs::from_vec(substs.into_iter().collect_vec()))
    }

    fn is_integral(&self) -> bool {
        matches!(self, BaseTy::Int(_) | BaseTy::Uint(_))
    }

    fn is_bool(&self) -> bool {
        matches!(self, BaseTy::Bool)
    }

    pub fn is_box(&self) -> bool {
        match self {
            BaseTy::Adt(adt_def, _) => adt_def.is_box(),
            _ => false,
        }
    }

    pub fn sorts(&self) -> &[Sort] {
        match self {
            BaseTy::Int(_) | BaseTy::Uint(_) => &[Sort::Int],
            BaseTy::Bool => &[Sort::Bool],
            BaseTy::Adt(adt_def, _) => adt_def.sorts(),
        }
    }
}

impl Sort {
    pub fn tuple(sorts: impl Into<List<Sort>>) -> Self {
        Sort::Tuple(sorts.into())
    }

    pub fn unit() -> Self {
        Self::tuple(vec![])
    }

    /// Returns `true` if the sort is [`Loc`].
    ///
    /// [`Loc`]: Sort::Loc
    #[must_use]
    pub fn is_loc(&self) -> bool {
        matches!(self, Self::Loc)
    }
}

impl rustc_errors::IntoDiagnosticArg for Sort {
    fn into_diagnostic_arg(self) -> rustc_errors::DiagnosticArgValue<'static> {
        rustc_errors::DiagnosticArgValue::Str(Cow::Owned(format!("{self:?}")))
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

    pub fn and(exprs: impl IntoIterator<Item = Expr>) -> Expr {
        exprs
            .into_iter()
            .reduce(|acc, e| Expr::binary_op(BinOp::And, acc, e))
            .unwrap_or_else(Expr::tt)
    }

    pub fn zero() -> Expr {
        static ZERO: OnceLock<Expr> = OnceLock::new();
        ZERO.get_or_init(|| ExprKind::Constant(Constant::ZERO).intern())
            .clone()
    }

    pub fn unit() -> Expr {
        Expr::tuple(vec![])
    }

    pub fn fvar(name: Name) -> Expr {
        ExprKind::FreeVar(name).intern()
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
            BaseTy::Uint(_) => {
                let bits = bits as u128;
                ExprKind::Constant(Constant::from(bits)).intern()
            }
            BaseTy::Bool => ExprKind::Constant(Constant::Bool(bits != 0)).intern(),
            BaseTy::Adt(_, _) => panic!(),
        }
    }

    pub fn binary_op(op: BinOp, e1: impl Into<Expr>, e2: impl Into<Expr>) -> Expr {
        ExprKind::BinaryOp(op, e1.into(), e2.into()).intern()
    }

    pub fn unary_op(op: UnOp, e: impl Into<Expr>) -> Expr {
        ExprKind::UnaryOp(op, e.into()).intern()
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
}

impl ExprS {
    pub fn kind(&self) -> &ExprKind {
        &self.kind
    }

    /// Whether the expression is literally the constant true.
    pub fn is_true(&self) -> bool {
        matches!(self.kind, ExprKind::Constant(Constant::Bool(true)))
    }

    pub fn is_atom(&self) -> bool {
        matches!(
            self.kind,
            ExprKind::FreeVar(_)
                | ExprKind::Local(_)
                | ExprKind::BoundVar(_)
                | ExprKind::Constant(_)
                | ExprKind::UnaryOp(..)
                | ExprKind::Tuple(..)
                | ExprKind::PathProj(..)
        )
    }

    /// Simplify expression applying some rules like removing double negation. This is only used
    /// for pretty printing.
    pub fn simplify(&self) -> Expr {
        match self.kind() {
            ExprKind::FreeVar(name) => Expr::fvar(*name),
            ExprKind::ConstDefId(did) => Expr::const_def_id(*did),
            ExprKind::BoundVar(idx) => Expr::bvar(*idx),
            ExprKind::Local(local) => Expr::local(*local),
            ExprKind::Constant(c) => Expr::constant(*c),
            ExprKind::BinaryOp(op, e1, e2) => {
                let e1 = e1.simplify();
                let e2 = e2.simplify();
                match (op, e1.kind(), e2.kind()) {
                    (BinOp::And, ExprKind::Constant(Constant::Bool(false)), _)
                    | (BinOp::And, _, ExprKind::Constant(Constant::Bool(false))) => {
                        Expr::constant(Constant::Bool(false))
                    }
                    (BinOp::And, ExprKind::Constant(Constant::Bool(true)), _) => e2,
                    (BinOp::And, _, ExprKind::Constant(Constant::Bool(true))) => e1,
                    _ => Expr::binary_op(*op, e1, e2),
                }
            }
            ExprKind::UnaryOp(UnOp::Not, e) => {
                let e = e.simplify();
                match e.kind() {
                    ExprKind::Constant(Constant::Bool(b)) => Expr::constant(Constant::Bool(!b)),
                    ExprKind::UnaryOp(UnOp::Not, e) => e.clone(),
                    ExprKind::BinaryOp(BinOp::Eq, e1, e2) => {
                        Expr::binary_op(BinOp::Ne, e1.clone(), e2.clone())
                    }
                    _ => Expr::unary_op(UnOp::Not, e),
                }
            }
            ExprKind::UnaryOp(op, e) => Expr::unary_op(*op, e.simplify()),
            ExprKind::TupleProj(e, field) => Expr::proj(e.simplify(), *field),
            ExprKind::Tuple(exprs) => Expr::tuple(exprs.iter().map(|e| e.simplify()).collect_vec()),
            ExprKind::PathProj(e, field) => Expr::path_proj(e.clone(), *field),
        }
    }

    pub fn to_loc(&self) -> Option<Loc> {
        match self.kind() {
            ExprKind::FreeVar(name) => Some(Loc::Free(*name)),
            ExprKind::Local(local) => Some(Loc::Local(*local)),
            ExprKind::BoundVar(bvar) => Some(Loc::Bound(*bvar)),
            _ => None,
        }
    }

    pub fn to_name(&self) -> Option<Name> {
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
                ExprKind::FreeVar(name) => break Loc::Free(*name),
                ExprKind::BoundVar(bvar) => break Loc::Bound(*bvar),
                ExprKind::Local(local) => break Loc::Local(*local),
                _ => return None,
            }
        };
        proj.reverse();
        Some(Path::new(loc, proj))
    }
}

impl Pred {
    pub fn kvars<T>(kvars: T) -> Pred
    where
        List<KVar>: From<T>,
    {
        Pred::Kvars(Interned::from(kvars))
    }

    pub fn tt() -> Pred {
        Pred::Expr(Expr::tt())
    }

    pub fn is_true(&self) -> bool {
        matches!(self, Pred::Expr(e) if e.is_true())
            || matches!(self, Pred::Kvars(kvars) if kvars.is_empty())
    }

    pub fn is_atom(&self) -> bool {
        matches!(self, Pred::Kvars(..)) || matches!(self, Pred::Expr(e) if e.is_atom())
    }
}

impl Binders<Pred> {
    pub fn is_true(&self) -> bool {
        self.value.is_true()
    }
}

impl KVar {
    pub fn new(kvid: KVid, args: Vec<Expr>, scope: Vec<Expr>) -> Self {
        KVar { kvid, args: List::from_vec(args), scope: List::from_vec(scope) }
    }

    fn all_args(&self) -> impl Iterator<Item = &Expr> {
        self.args.iter().chain(&self.scope)
    }
}

impl Path {
    pub fn new<T>(loc: Loc, projection: T) -> Path
    where
        List<Field>: From<T>,
    {
        Path { loc, projection: Interned::from(projection) }
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
}

impl Loc {
    pub fn to_expr(&self) -> Expr {
        match self {
            Loc::Local(local) => Expr::local(*local),
            Loc::Free(name) => Expr::fvar(*name),
            Loc::Bound(bvar) => Expr::bvar(*bvar),
        }
    }
}

impl BoundVar {
    pub const NU: BoundVar = BoundVar { index: 0, debruijn: INNERMOST };

    pub fn new(index: usize, debruijn: DebruijnIndex) -> Self {
        BoundVar { index, debruijn }
    }

    pub fn innermost(index: usize) -> BoundVar {
        BoundVar::new(index, INNERMOST)
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

impl From<Expr> for Pred {
    fn from(expr: Expr) -> Self {
        Pred::Expr(expr)
    }
}

impl From<Loc> for Path {
    fn from(loc: Loc) -> Self {
        Path::new(loc, vec![])
    }
}

impl From<Name> for Loc {
    fn from(name: Name) -> Self {
        Loc::Free(name)
    }
}

impl From<Local> for Loc {
    fn from(local: Local) -> Self {
        Loc::Local(local)
    }
}

impl_internable!(
    AdtDefData,
    TyS,
    ExprS,
    [Ty],
    [Pred],
    [Expr],
    [Field],
    [KVar],
    [Constraint],
    [Index],
    [Sort]
);

mod pretty {
    use rustc_middle::ty::TyCtxt;

    use super::*;
    use crate::pretty::*;

    impl<T> Pretty for Binders<T>
    where
        T: Pretty,
    {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            if !self.params.is_empty() {
                w!("for<{}> ",
                    ^self.params.iter().format_with(", ", |sort, f| {
                        f(&format_args_cx!("{:?}", ^sort))
                    })
                )?;
            }
            w!("{:?}", &self.value)
        }
    }

    impl<T> std::fmt::Debug for Binders<T>
    where
        T: std::fmt::Debug,
    {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            if !self.params.is_empty() {
                write!(
                    f,
                    "for<{}> ",
                    self.params
                        .iter()
                        .format_with(", ", |sort, f| { f(&format_args_cx!("{:?}", ^sort)) })
                )?;
            }
            write!(f, "{:?}", self.value)
        }
    }

    impl Pretty for FnSig {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!("fn(")?;
            if !self.requires.is_empty() {
                w!("[{:?}] ", join!(", ", &self.requires))?;
            }
            w!("{:?}) -> {:?}", join!(", ", &self.args), &self.ret)?;
            if !self.ensures.is_empty() {
                w!("; [{:?}]", join!(", ", &self.ensures))?;
            }

            Ok(())
        }
    }

    impl Pretty for Constraint {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                Constraint::Type(loc, ty) => w!("{:?}: {:?}", ^loc, ty),
                Constraint::Pred(e) => w!("{:?}", e),
            }
        }
    }

    impl Pretty for TyS {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self.kind() {
                TyKind::Indexed(bty, indices) => fmt_bty(bty, indices, cx, f),
                TyKind::Exists(bty, pred) => {
                    if pred.is_true() {
                        w!("{:?}{{}}", bty)
                    } else {
                        w!("{:?}{{{:?}}}", bty, &pred.value)
                    }
                }
                TyKind::Float(float_ty) => w!("{}", ^float_ty.name_str()),
                TyKind::Uninit => w!("uninit"),
                TyKind::Ptr(loc) => w!("ptr({:?})", loc),
                TyKind::BoxPtr(loc, alloc) => w!("box({:?}, {:?})", ^loc, alloc),
                TyKind::Ref(RefKind::Mut, ty) => w!("&mut {:?}", ty),
                TyKind::Ref(RefKind::Shr, ty) => w!("&{:?}", ty),
                TyKind::Param(param) => w!("{}", ^param),
                TyKind::Tuple(tys) => w!("({:?})", join!(", ", tys)),
                TyKind::Never => w!("!"),
                TyKind::Discr(place) => w!("discr({:?})", ^place),
                TyKind::Constr(pred, ty) => w!("{{ {ty:?} : {pred:?} }}"),
            }
        }

        fn default_cx(tcx: TyCtxt) -> PPrintCx {
            PPrintCx::default(tcx).kvar_args(Visibility::Hide)
        }
    }

    impl Pretty for BaseTy {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            fmt_bty(self, &[], cx, f)
        }
    }

    fn fmt_bty(
        bty: &BaseTy,
        indices: &[Index],
        cx: &PPrintCx,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        define_scoped!(cx, f);
        match bty {
            BaseTy::Int(int_ty) => write!(f, "{}", int_ty.name_str())?,
            BaseTy::Uint(uint_ty) => write!(f, "{}", uint_ty.name_str())?,
            BaseTy::Bool => w!("bool")?,
            BaseTy::Adt(adt_def, _) => w!("{:?}", adt_def.def_id())?,
        }
        match bty {
            BaseTy::Int(_) | BaseTy::Uint(_) | BaseTy::Bool => {
                if !indices.is_empty() {
                    w!("<{:?}>", join!(", ", indices))?;
                }
            }
            BaseTy::Adt(_, args) => {
                if !args.is_empty() || !indices.is_empty() {
                    w!("<")?;
                }
                w!("{:?}", join!(", ", args))?;
                if !args.is_empty() && !indices.is_empty() {
                    w!(", ")?;
                }
                w!("{:?}", join!(", ", indices))?;
                if !args.is_empty() || !indices.is_empty() {
                    w!(">")?;
                }
            }
        }
        Ok(())
    }

    impl Pretty for Index {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            if self.is_binder && self.expr.is_atom() {
                w!("@{:?}", &self.expr)
            } else if self.is_binder {
                w!("@({:?})", &self.expr)
            } else {
                w!("{:?}", &self.expr)
            }
        }
    }

    impl Pretty for Pred {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                Pred::Kvars(kvars) => {
                    match &kvars[..] {
                        [] => w!("true"),
                        [kvar] => w!("{:?}", kvar),
                        kvars => w!("{:?}", join!(" ∧ ", kvars)),
                    }
                }
                Pred::Expr(expr) => w!("{:?}", expr),
                Pred::Hole => w!("*"),
            }
        }

        fn default_cx(tcx: TyCtxt) -> PPrintCx {
            PPrintCx::default(tcx).fully_qualified_paths(true)
        }
    }

    impl Pretty for KVar {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!("{:?}", ^self.kvid)?;
            match cx.kvar_args {
                Visibility::Show => w!("({:?})", join!(", ", self.all_args()))?,
                Visibility::Truncate(n) => w!("({:?})", join!(", ", self.all_args().take(n)))?,
                Visibility::Hide => {}
            }
            Ok(())
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
            let e = if cx.simplify_exprs { self.simplify() } else { Interned::new(self.clone()) };
            match e.kind() {
                ExprKind::FreeVar(name) => w!("{:?}", ^name),
                ExprKind::ConstDefId(did) => w!("{:?}", ^did),
                ExprKind::BoundVar(bvar) => w!("{:?}", bvar),
                ExprKind::Local(local) => w!("{:?}", ^local),
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
                ExprKind::TupleProj(e, field) => {
                    if e.is_atom() {
                        w!("{:?}.{:?}", e, ^field)
                    } else {
                        w!("({:?}).{:?}", e, ^field)
                    }
                }
                ExprKind::Tuple(exprs) => {
                    w!("({:?})", join!(", ", exprs))
                }
                ExprKind::PathProj(e, field) => {
                    if e.is_atom() {
                        w!("{:?}.{:?}", e, field)
                    } else {
                        w!("({:?}).{:?}", e, field)
                    }
                }
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
                Loc::Free(name) => w!("{:?}", ^name),
                Loc::Bound(bvar) => w!("{:?}", bvar),
            }
        }
    }

    impl Pretty for Sort {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                Sort::Int => w!("int"),
                Sort::Bool => w!("bool"),
                Sort::Loc => w!("loc"),
                Sort::Tuple(sorts) => w!("({:?})", join!(", ", sorts)),
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

    impl fmt::Display for Sort {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            fmt::Debug::fmt(self, f)
        }
    }

    impl_debug_with_default_cx!(
        Constraint,
        TyS => "ty",
        BaseTy,
        Pred,
        Sort,
        ExprS,
        Loc,
        Path,
        KVar,
        BoundVar,
        FnSig,
        Index,
    );
}
