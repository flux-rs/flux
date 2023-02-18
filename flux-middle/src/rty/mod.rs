//! Defines how flux represents refinement types internally. Definitions in this module are used
//! during refinement type checking. A couple of important differences between definitions in this
//! module and in [`crate::fhir`] are:
//!
//! * Types in this module use debruijn indices to represent local binders.
//! * Data structures are interned so they can be cheaply cloned.
pub mod conv;
pub mod evars;
mod expr;
pub mod fold;
pub(crate) mod normalize;
pub mod subst;

use std::{fmt, hash::Hash, iter, slice, sync::LazyLock};

pub use evars::{EVar, EVarGen};
pub use expr::{DebruijnIndex, Expr, ExprKind, KVar, KVid, Loc, Name, Path, Var, INNERMOST};
use flux_common::{bug, index::IndexGen};
pub use flux_fixpoint::{BinOp, Constant, UnOp};
use itertools::Itertools;
use rustc_hir::def_id::DefId;
use rustc_macros::{TyDecodable, TyEncodable};
use rustc_middle::mir::{Field, Mutability};
pub use rustc_middle::ty::{AdtFlags, FloatTy, IntTy, ParamTy, ScalarInt, UintTy};
use rustc_span::Symbol;
pub use rustc_target::abi::VariantIdx;

use self::{fold::TypeFoldable, subst::BVarSubstFolder};
pub use crate::{
    fhir::{InferMode, RefKind},
    rustc::ty::Const,
};
use crate::{
    intern::{impl_internable, Internable, Interned, List},
    rustc::mir::Place,
};

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub enum Sort {
    Int,
    Bool,
    Real,
    Loc,
    Param(ParamTy),
    Tuple(List<Sort>),
    Func(FuncSort),
    User(Symbol),
}

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub struct FuncSort {
    input_and_output: List<Sort>,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, TyEncodable, TyDecodable)]
pub struct AdtDef(Interned<AdtDefData>);

#[derive(Debug, Eq, PartialEq, Hash, TyEncodable, TyDecodable)]
pub struct AdtDefData {
    def_id: DefId,
    invariants: Vec<Invariant>,
    sort: Sort,
    flags: AdtFlags,
    nvariants: usize,
    opaque: bool,
}

/// Option-like enum to explicitly mark that we don't have information about an ADT because it was
/// annotated with `#[flux::opaque]`. Note that only structs can be marked as opaque.
#[derive(TyEncodable, TyDecodable)]
pub enum Opaqueness<T> {
    Opaque,
    Transparent(T),
}

#[derive(Debug, Eq, PartialEq, Hash, TyEncodable, TyDecodable)]
pub struct Invariant {
    pub pred: Binder<Expr>,
}

pub type PolyVariant = Binder<VariantDef>;

#[derive(Clone, Eq, PartialEq, Hash, TyEncodable, TyDecodable)]
pub struct VariantDef {
    pub fields: List<Ty>,
    pub ret: Ty,
}

#[derive(Clone, Eq, PartialEq, Hash, TyEncodable, TyDecodable)]
pub struct Binder<T> {
    sort: Sort,
    value: T,
}

#[derive(Clone, Eq, PartialEq, Hash, TyEncodable, TyDecodable, Debug)]
pub enum TupleTree<T>
where
    [TupleTree<T>]: Internable,
{
    Tuple(List<TupleTree<T>>),
    Leaf(T),
}

#[derive(Clone, TyEncodable, TyDecodable)]
pub struct PolySig {
    pub fn_sig: Binder<FnSig>,
    pub modes: List<InferMode>,
}

#[derive(Clone, TyEncodable, TyDecodable)]
pub struct FnSig {
    requires: List<Constraint>,
    args: List<Ty>,
    output: Binder<FnOutput>,
}

#[derive(Clone, TyEncodable, TyDecodable)]
pub struct FnOutput {
    pub ret: Ty,
    pub ensures: List<Constraint>,
}

pub type Constraints = List<Constraint>;

#[derive(Clone, Eq, PartialEq, Hash, TyEncodable, TyDecodable)]
pub enum Constraint {
    Type(Path, Ty),
    Pred(Expr),
}

#[derive(Debug)]
pub struct Qualifier {
    pub name: String,
    pub body: Binder<Expr>,
    pub global: bool,
}

pub struct Defn {
    pub name: Symbol,
    pub expr: Binder<Expr>,
}

pub struct UifDef {
    pub name: Symbol,
    pub sort: FuncSort,
}

pub type Ty = Interned<TyS>;

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub struct TyS {
    kind: TyKind,
}

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub enum TyKind {
    Indexed(BaseTy, Index),
    Exists(Binder<Ty>),
    Constr(Expr, Ty),
    Uninit,
    Ptr(PtrKind, Path),
    /// This is a bit of a hack. We use this type internally to represent the result of
    /// [`Rvalue::Discriminant`] in a way that we can recover the necessary control information
    /// when checking [`TerminatorKind::SwitchInt`].
    ///
    /// [`Rvalue::Discriminant`]: crate::rustc::mir::Rvalue::Discriminant
    /// [`TerminatorKind::SwitchInt`]: crate::rustc::mir::TerminatorKind::SwitchInt
    Discr(AdtDef, Place),
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub enum PtrKind {
    Shr,
    Mut,
    Box,
}

#[derive(Clone, Eq, Hash, PartialEq, TyEncodable, TyDecodable)]
pub struct Index {
    pub expr: Expr,
    pub is_binder: TupleTree<bool>,
}

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub enum BaseTy {
    Int(IntTy),
    Uint(UintTy),
    Bool,
    Str,
    Char,
    Slice(Ty),
    Adt(AdtDef, Substs),
    Float(FloatTy),
    RawPtr(Ty, Mutability),
    Ref(RefKind, Ty),
    Tuple(List<Ty>),
    Array(Ty, Const),
    Never,
    Param(ParamTy),
}

pub type Substs = List<GenericArg>;

#[derive(PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub enum GenericArg {
    Ty(Ty),
    BaseTy(Binder<Ty>),
    /// We treat lifetime opaquely
    Lifetime,
}

#[derive(Copy, Clone)]
pub enum TyVarKind {
    Type,
    BaseTy,
}

impl Sort {
    pub fn tuple(sorts: impl Into<List<Sort>>) -> Self {
        Sort::Tuple(sorts.into())
    }

    pub(crate) fn unit() -> Self {
        Self::tuple(vec![])
    }

    #[track_caller]
    fn expect_tuple(&self) -> &[Sort] {
        if let Sort::Tuple(sorts) = self {
            sorts
        } else {
            bug!("expected `Sort::Tuple`")
        }
    }

    #[track_caller]
    pub fn expect_func(&self) -> &FuncSort {
        if let Sort::Func(sort) = self {
            sort
        } else {
            bug!("expected `Sort::Func`")
        }
    }

    pub fn default_infer_mode(&self) -> InferMode {
        if self.is_pred() {
            InferMode::KVar
        } else {
            InferMode::EVar
        }
    }

    pub fn as_tuple(&self) -> &[Sort] {
        if let Sort::Tuple(sorts) = self {
            sorts
        } else {
            slice::from_ref(self)
        }
    }

    pub(crate) fn is_unit(&self) -> bool {
        matches!(self, Sort::Tuple(sorts) if sorts.is_empty())
    }

    /// Whether the sort is a function with return sort bool
    fn is_pred(&self) -> bool {
        matches!(self, Sort::Func(fsort) if fsort.output().is_bool())
    }

    /// Returns `true` if the sort is [`Bool`].
    ///
    /// [`Bool`]: Sort::Bool
    #[must_use]
    fn is_bool(&self) -> bool {
        matches!(self, Self::Bool)
    }

    pub fn flatten(&self) -> Vec<Sort> {
        let mut sorts = vec![];
        self.walk(|sort, _| sorts.push(sort.clone()));
        sorts
    }

    pub fn walk(&self, mut f: impl FnMut(&Sort, &[u32])) {
        fn go(sort: &Sort, f: &mut impl FnMut(&Sort, &[u32]), proj: &mut Vec<u32>) {
            if let Sort::Tuple(sorts) = sort {
                sorts.iter().enumerate().for_each(|(i, sort)| {
                    proj.push(i as u32);
                    go(sort, f, proj);
                    proj.pop();
                });
            } else {
                f(sort, proj);
            }
        }
        go(self, &mut f, &mut vec![]);
    }
}

impl FuncSort {
    pub(crate) fn new(input: Sort, output: Sort) -> Self {
        FuncSort { input_and_output: List::from_vec(vec![input, output]) }
    }

    pub fn input(&self) -> &Sort {
        &self.input_and_output[0]
    }

    pub fn output(&self) -> &Sort {
        &self.input_and_output[1]
    }
}

impl Qualifier {
    pub fn with_fresh_fvars(&self) -> (Vec<(Name, Sort)>, Expr) {
        let name_gen = IndexGen::new();
        let mut params = vec![];
        let arg = Expr::fold_sort(self.body.sort(), |sort| {
            let fresh = name_gen.fresh();
            params.push((fresh, sort.clone()));
            Expr::fvar(fresh)
        });
        let body = self.body.replace_bvar(&arg);
        (params, body)
    }
}

impl<T> Binder<T> {
    pub fn new(value: T, sort: Sort) -> Binder<T> {
        Binder { sort, value }
    }

    pub fn sort(&self) -> &Sort {
        &self.sort
    }

    pub fn as_ref(&self) -> Binder<&T> {
        Binder { sort: self.sort.clone(), value: &self.value }
    }

    pub fn skip_binders(self) -> T {
        self.value
    }

    pub fn map<S>(self, f: impl FnOnce(T) -> S) -> Binder<S> {
        Binder { sort: self.sort, value: f(self.value) }
    }
}

impl VariantDef {
    pub fn new(fields: Vec<Ty>, ret: Ty) -> Self {
        VariantDef { fields: List::from_vec(fields), ret }
    }

    pub fn fields(&self) -> &[Ty] {
        &self.fields
    }
}

impl<T> Binder<T>
where
    T: TypeFoldable,
{
    pub fn replace_bvar(&self, expr: &Expr) -> T {
        self.value
            .fold_with(&mut BVarSubstFolder::new(expr))
            .normalize(&Default::default())
    }

    pub fn replace_bvar_with(&self, mut f: impl FnMut(&Sort) -> Expr) -> T {
        let expr = f(&self.sort);
        self.replace_bvar(&expr)
    }
}

impl<T> TupleTree<T>
where
    [TupleTree<T>]: Internable,
{
    fn unit() -> Self {
        TupleTree::Tuple(List::from_vec(vec![]))
    }

    pub fn split(&self) -> impl Iterator<Item = &TupleTree<T>> {
        match self {
            TupleTree::Tuple(values) => values.iter().cycle(),
            TupleTree::Leaf(_) => slice::from_ref(self).iter().cycle(),
        }
    }

    #[track_caller]
    pub fn expect_leaf(&self) -> &T {
        match self {
            TupleTree::Leaf(value) => value,
            _ => bug!("expected leaf"),
        }
    }
}

impl Index {
    pub(crate) fn unit() -> Self {
        Index { expr: Expr::unit(), is_binder: TupleTree::unit() }
    }
}

impl From<Expr> for Index {
    fn from(expr: Expr) -> Self {
        let is_binder = TupleTree::Leaf(false);
        Self { expr, is_binder }
    }
}

impl From<(Expr, TupleTree<bool>)> for Index {
    fn from((expr, is_binder): (Expr, TupleTree<bool>)) -> Self {
        Self { expr, is_binder }
    }
}

impl PolySig {
    pub fn new(params: impl IntoIterator<Item = (Sort, InferMode)>, fn_sig: FnSig) -> PolySig {
        let (sorts, modes) = params.into_iter().unzip();
        let fn_sig = Binder::new(fn_sig, Sort::Tuple(List::from_vec(sorts)));
        PolySig { fn_sig, modes: List::from_vec(modes) }
    }

    pub fn replace_bvars_with(&self, mut f: impl FnMut(&Sort, InferMode) -> Expr) -> FnSig {
        let exprs = iter::zip(self.fn_sig.sort.expect_tuple(), &self.modes)
            .map(|(sort, kind)| f(sort, *kind))
            .collect_vec();
        self.fn_sig.replace_bvar(&Expr::tuple(exprs))
    }
}

impl FnSig {
    pub fn new(
        requires: impl Into<List<Constraint>>,
        args: impl Into<List<Ty>>,
        output: Binder<FnOutput>,
    ) -> Self {
        FnSig { requires: requires.into(), args: args.into(), output }
    }

    pub fn requires(&self) -> &Constraints {
        &self.requires
    }

    pub fn args(&self) -> &[Ty] {
        &self.args
    }

    pub fn output(&self) -> &Binder<FnOutput> {
        &self.output
    }
}

impl FnOutput {
    pub fn new(ret: Ty, ensures: impl Into<List<Constraint>>) -> Self {
        Self { ret, ensures: ensures.into() }
    }
}

impl AdtDef {
    pub(crate) fn new(
        rustc_def: rustc_middle::ty::AdtDef,
        sort: Sort,
        invariants: Vec<Invariant>,
        opaque: bool,
    ) -> Self {
        AdtDef(Interned::new(AdtDefData {
            def_id: rustc_def.did(),
            invariants,
            sort,
            flags: rustc_def.flags(),
            nvariants: rustc_def.variants().len(),
            opaque,
        }))
    }

    pub fn def_id(&self) -> DefId {
        self.0.def_id
    }

    pub fn sort(&self) -> &Sort {
        &self.0.sort
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

    pub fn variants(&self) -> impl Iterator<Item = VariantIdx> {
        (0..self.0.nvariants).map(VariantIdx::from)
    }

    pub fn nvariants(&self) -> usize {
        self.0.nvariants
    }

    pub fn invariants(&self) -> &[Invariant] {
        &self.0.invariants
    }

    pub fn is_opaque(&self) -> bool {
        self.0.opaque
    }
}

impl<T> Opaqueness<T> {
    pub fn map<S>(self, f: impl FnOnce(T) -> S) -> Opaqueness<S> {
        match self {
            Opaqueness::Opaque => Opaqueness::Opaque,
            Opaqueness::Transparent(value) => Opaqueness::Transparent(f(value)),
        }
    }

    pub fn as_ref(&self) -> Opaqueness<&T> {
        match self {
            Opaqueness::Opaque => Opaqueness::Opaque,
            Opaqueness::Transparent(value) => Opaqueness::Transparent(value),
        }
    }

    pub fn as_deref(&self) -> Opaqueness<&T::Target>
    where
        T: std::ops::Deref,
    {
        match self {
            Opaqueness::Opaque => Opaqueness::Opaque,
            Opaqueness::Transparent(value) => Opaqueness::Transparent(value.deref()),
        }
    }

    pub fn ok_or<E>(self, err: E) -> Result<T, E> {
        match self {
            Opaqueness::Opaque => Err(err),
            Opaqueness::Transparent(value) => Ok(value),
        }
    }
}

impl PolyVariant {
    pub fn to_fn_sig(&self) -> PolySig {
        let fn_sig = self
            .as_ref()
            .map(|variant| {
                let ret = variant.ret.shift_in_bvars(1);
                let output = Binder::new(FnOutput::new(ret, vec![]), Sort::unit());
                FnSig::new(vec![], variant.fields.clone(), output)
            })
            .skip_binders();
        let params = self
            .sort
            .expect_tuple()
            .iter()
            .map(|sort| (sort.clone(), Sort::default_infer_mode(sort)))
            .collect_vec();
        PolySig::new(params, fn_sig)
    }
}

impl Ty {
    pub fn ptr(pk: impl Into<PtrKind>, path: impl Into<Path>) -> Ty {
        TyKind::Ptr(pk.into(), path.into()).intern()
    }

    pub fn constr(p: impl Into<Expr>, ty: Ty) -> Ty {
        TyKind::Constr(p.into(), ty).intern()
    }

    pub fn uninit() -> Ty {
        TyKind::Uninit.intern()
    }

    pub fn indexed(bty: BaseTy, idx: impl Into<Index>) -> Ty {
        TyKind::Indexed(bty, idx.into()).intern()
    }

    pub fn exists(ty: Binder<Ty>) -> Ty {
        TyKind::Exists(ty).intern()
    }

    pub fn exists_with_constr(bty: BaseTy, pred: Expr) -> Ty {
        let sort = bty.sort();
        let ty = Ty::indexed(bty, Expr::nu());
        Ty::exists(Binder::new(Ty::constr(pred, ty), sort))
    }

    pub fn discr(adt_def: AdtDef, place: Place) -> Ty {
        TyKind::Discr(adt_def, place).intern()
    }

    pub fn unit() -> Ty {
        Ty::tuple(vec![])
    }

    pub fn bool() -> Ty {
        BaseTy::Bool.into_ty()
    }

    pub fn int(int_ty: IntTy) -> Ty {
        BaseTy::Int(int_ty).into_ty()
    }

    pub fn uint(uint_ty: UintTy) -> Ty {
        BaseTy::Uint(uint_ty).into_ty()
    }

    pub fn param(param_ty: ParamTy) -> Ty {
        Ty::exists(Binder::new(
            Ty::indexed(BaseTy::Param(param_ty), Expr::nu()),
            Sort::Param(param_ty),
        ))
    }

    pub fn usize() -> Ty {
        Ty::uint(UintTy::Usize)
    }

    pub fn str() -> Ty {
        BaseTy::Str.into_ty()
    }

    pub fn char() -> Ty {
        BaseTy::Char.into_ty()
    }

    pub fn float(float_ty: FloatTy) -> Ty {
        BaseTy::Float(float_ty).into_ty()
    }

    pub fn mk_ref(mode: RefKind, ty: Ty) -> Ty {
        BaseTy::Ref(mode, ty).into_ty()
    }

    pub fn tuple(tys: impl Into<List<Ty>>) -> Ty {
        BaseTy::Tuple(tys.into()).into_ty()
    }

    pub fn array(ty: Ty, c: Const) -> Ty {
        BaseTy::Array(ty, c).into_ty()
    }

    pub fn never() -> Ty {
        BaseTy::Never.into_ty()
    }

    pub fn unconstr(&self) -> (Ty, Expr) {
        fn go(this: &Ty, preds: &mut Vec<Expr>) -> Ty {
            if let TyKind::Constr(pred, ty) = this.kind() {
                preds.push(pred.clone());
                go(ty, preds)
            } else {
                this.clone()
            }
        }
        let mut preds = vec![];
        (go(self, &mut preds), Expr::and(preds))
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

    #[track_caller]
    pub fn expect_discr(&self) -> (&AdtDef, &Place) {
        if let TyKind::Discr(adt_def, place) = self.kind() {
            (adt_def, place)
        } else {
            bug!("expected discr")
        }
    }

    #[track_caller]
    pub fn expect_adt(&self) -> (&AdtDef, &[GenericArg], &Index) {
        if let TyKind::Indexed(BaseTy::Adt(adt_def, substs), idx) = self.kind() {
            (adt_def, substs, idx)
        } else {
            bug!("expected adt")
        }
    }

    #[track_caller]
    pub fn expect_indexed(&self) -> (&BaseTy, &Index) {
        if let TyKind::Indexed(bty, idx) = self.kind() {
            (bty, idx)
        } else {
            bug!("expected indexed")
        }
    }

    /// Whether the type is an `int` or a `uint`
    pub fn is_integral(&self) -> bool {
        self.as_bty_skipping_binders()
            .map(BaseTy::is_integral)
            .unwrap_or_default()
    }

    /// Whether the type is a `bool`
    pub fn is_bool(&self) -> bool {
        self.as_bty_skipping_binders()
            .map(BaseTy::is_bool)
            .unwrap_or_default()
    }

    pub fn is_uninit(&self) -> bool {
        matches!(self.kind(), TyKind::Uninit)
    }

    fn as_bty_skipping_binders(&self) -> Option<&BaseTy> {
        match self.kind() {
            TyKind::Indexed(bty, _) => Some(bty),
            TyKind::Exists(ty) => Some(ty.as_ref().skip_binders().as_bty_skipping_binders()?),
            TyKind::Constr(_, ty) => ty.as_bty_skipping_binders(),
            _ => None,
        }
    }
}

impl From<RefKind> for PtrKind {
    fn from(rk: RefKind) -> Self {
        match rk {
            RefKind::Shr => PtrKind::Shr,
            RefKind::Mut => PtrKind::Mut,
        }
    }
}

impl BaseTy {
    pub fn adt(adt_def: AdtDef, substs: impl Into<List<GenericArg>>) -> BaseTy {
        BaseTy::Adt(adt_def, substs.into())
    }

    pub fn slice(ty: Ty) -> BaseTy {
        BaseTy::Slice(ty)
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

    pub fn invariants(&self) -> &[Invariant] {
        static GE0: LazyLock<Invariant> = LazyLock::new(|| {
            Invariant {
                pred: Binder::new(Expr::binary_op(BinOp::Ge, Expr::nu(), Expr::zero()), Sort::Int),
            }
        });

        match self {
            BaseTy::Adt(adt_def, _) => adt_def.invariants(),
            BaseTy::Uint(_) => std::slice::from_ref(&GE0),
            BaseTy::Int(_)
            | BaseTy::Bool
            | BaseTy::Str
            | BaseTy::Float(_)
            | BaseTy::Slice(_)
            | BaseTy::RawPtr(_, _)
            | BaseTy::Char
            | BaseTy::Ref(_, _)
            | BaseTy::Tuple(_)
            | BaseTy::Array(_, _)
            | BaseTy::Never
            | BaseTy::Param(_) => &[],
        }
    }

    fn into_ty(self) -> Ty {
        let sort = self.sort();
        if sort.is_unit() {
            Ty::indexed(self, Index::unit())
        } else {
            Ty::exists(Binder::new(Ty::indexed(self, Expr::nu()), sort))
        }
    }

    pub fn sort(&self) -> Sort {
        match self {
            BaseTy::Int(_) | BaseTy::Uint(_) | BaseTy::Slice(_) => Sort::Int,
            BaseTy::Bool => Sort::Bool,
            BaseTy::Adt(adt_def, _) => adt_def.sort().clone(),
            BaseTy::Param(param_ty) => Sort::Param(*param_ty),
            BaseTy::Float(_)
            | BaseTy::Str
            | BaseTy::Char
            | BaseTy::RawPtr(..)
            | BaseTy::Ref(..)
            | BaseTy::Tuple(_)
            | BaseTy::Array(_, _)
            | BaseTy::Never => Sort::unit(),
        }
    }
}

impl Binder<Expr> {
    /// See [`Expr::is_trivially_true`]
    pub fn is_trivially_true(&self) -> bool {
        self.value.is_trivially_true()
    }
}

#[track_caller]
pub fn box_args(substs: &Substs) -> (&Ty, &Ty) {
    if let [GenericArg::Ty(boxed), GenericArg::Ty(alloc)] = &substs[..] {
        (boxed, alloc)
    } else {
        bug!("invalid generic arguments for box");
    }
}

impl_internable!(
    AdtDefData,
    TyS,
    [Ty],
    [GenericArg],
    [Field],
    [Constraint],
    [InferMode],
    [TupleTree<bool>],
    [Sort]
);

#[macro_export]
macro_rules! _Int {
    ($int_ty:pat, $idxs:pat) => {
        TyKind::Indexed(BaseTy::Int($int_ty), $idxs)
    };
}
pub use crate::_Int as Int;

#[macro_export]
macro_rules! _Uint {
    ($uint_ty:pat, $idxs:pat) => {
        TyKind::Indexed(BaseTy::Uint($uint_ty), $idxs)
    };
}
pub use crate::_Uint as Uint;

#[macro_export]
macro_rules! _Bool {
    ($idxs:pat) => {
        TyKind::Indexed(BaseTy::Bool, $idxs)
    };
}
pub use crate::_Bool as Bool;

#[macro_export]
macro_rules! _Float {
    ($float_ty:pat) => {
        TyKind::Indexed(BaseTy::Float($float_ty), _)
    };
}
pub use crate::_Float as Float;

#[macro_export]
macro_rules! _Ref {
    ($rk:pat, $ty:pat) => {
        TyKind::Indexed(BaseTy::Ref($rk, $ty), _)
    };
}
pub use crate::_Ref as Ref;

mod pretty {
    use rustc_middle::ty::TyCtxt;

    use super::*;
    use crate::pretty::*;

    impl<T> Pretty for Binder<T>
    where
        T: Pretty,
    {
        default fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!("for<{:?}> {:?}", &self.sort, &self.value)
        }
    }

    impl Pretty for Sort {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                Sort::Bool => w!("bool"),
                Sort::Int => w!("int"),
                Sort::Real => w!("real"),
                Sort::Loc => w!("loc"),
                Sort::Func(sort) => w!("{:?}", sort),
                Sort::Tuple(sorts) => {
                    if let [sort] = &sorts[..] {
                        w!("({:?},)", sort)
                    } else {
                        w!("({:?})", join!(", ", sorts))
                    }
                }
                Sort::Param(param_ty) => w!("sortof({})", ^param_ty),
                Sort::User(name) => w!("{}", ^name),
            }
        }
    }

    impl Pretty for FuncSort {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!("{:?} -> {:?}", self.input(), self.output())
        }
    }

    impl Pretty for Binder<Expr> {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!("|{:?}| {:?}", &self.sort, &self.value)
        }
    }

    impl<T> std::fmt::Debug for Binder<T>
    where
        T: std::fmt::Debug,
    {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "for<{:?}> {:?}", self.sort, self.value)
        }
    }

    impl Pretty for PolySig {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            let sorts = self.fn_sig.sort.expect_tuple();
            if !sorts.is_empty() {
                write!(
                    f,
                    "forall<{}> ",
                    sorts.iter().enumerate().format_with(", ", |(i, sort), f| {
                        match self.modes[i] {
                            InferMode::KVar => f(&format_args_cx!("${:?}", ^sort)),
                            InferMode::EVar => f(&format_args_cx!("?{:?}", ^sort)),
                        }
                    })
                )?;
            }
            w!("{:?}", &self.fn_sig.value)
        }
    }

    impl Pretty for FnSig {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!("fn(")?;
            if !self.requires.is_empty() {
                w!("[{:?}] ", join!(", ", &self.requires))?;
            }
            w!("{:?}) -> {:?}", join!(", ", &self.args), &self.output)?;

            Ok(())
        }

        fn default_cx(tcx: TyCtxt) -> PPrintCx {
            PPrintCx::default(tcx).show_is_binder(true)
        }
    }

    impl Pretty for Binder<FnOutput> {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            let sorts = self.sort.expect_tuple();
            w!("exists<{:?}> {:?}", join!(", ", sorts), &self.value.ret)?;
            if !self.value.ensures.is_empty() {
                w!("; [{:?}]", join!(", ", &self.value.ensures))?;
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
                TyKind::Indexed(bty, idx) => {
                    w!("{:?}", bty)?;
                    if !cx.hide_refinements && !bty.sort().is_unit() {
                        w!("[{:?}]", idx)?;
                    }
                    Ok(())
                }
                TyKind::Exists(Binder { sort, value: ty }) => {
                    if cx.hide_refinements {
                        w!("{:?}", ty)
                    } else {
                        w!("∃{:?}. {:?}", sort, ty)
                    }
                }
                TyKind::Uninit => w!("uninit"),
                TyKind::Ptr(pk, loc) => w!("ptr({:?}, {:?})", pk, loc),
                TyKind::Discr(adt_def, place) => w!("discr({:?}, {:?})", adt_def.def_id(), ^place),
                TyKind::Constr(pred, ty) => {
                    if cx.hide_refinements {
                        w!("{:?}", ty)
                    } else {
                        w!("{{ {:?} | {:?} }}", ty, pred)
                    }
                }
            }
        }

        fn default_cx(tcx: TyCtxt) -> PPrintCx {
            PPrintCx::default(tcx).kvar_args(KVarArgs::Hide)
        }
    }

    impl Pretty for PtrKind {
        fn fmt(&self, _cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                PtrKind::Shr => w!("shr"),
                PtrKind::Mut => w!("mut"),
                PtrKind::Box => w!("box"),
            }
        }
    }

    impl Pretty for Index {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            fn go(
                cx: &PPrintCx,
                f: &mut fmt::Formatter<'_>,
                is_binder: &TupleTree<bool>,
                expr: &Expr,
            ) -> fmt::Result {
                define_scoped!(cx, f);
                match (is_binder, expr.kind()) {
                    (TupleTree::Tuple(is_binder), ExprKind::Tuple(es)) => {
                        debug_assert_eq!(is_binder.len(), es.len());
                        w!("(")?;
                        for (is_binder, e) in iter::zip(is_binder, es) {
                            go(cx, f, is_binder, e)?;
                            w!(", ")?;
                        }
                        w!(")")?;
                    }
                    (TupleTree::Leaf(is_binder), _) => {
                        if *is_binder {
                            w!("@{:?}", expr)?;
                        } else {
                            w!("{:?}", expr)?;
                        }
                    }
                    _ => bug!("{is_binder:?} {expr:?}"),
                }
                Ok(())
            }
            go(cx, f, &self.is_binder, &self.expr)
        }
    }

    impl Pretty for BaseTy {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                BaseTy::Int(int_ty) => w!("{}", ^int_ty.name_str()),
                BaseTy::Uint(uint_ty) => w!("{}", ^uint_ty.name_str()),
                BaseTy::Bool => w!("bool"),
                BaseTy::Str => w!("str"),
                BaseTy::Char => w!("char"),
                BaseTy::Adt(adt_def, substs) => {
                    w!("{:?}", adt_def.def_id())?;
                    if !substs.is_empty() {
                        w!("<{:?}>", join!(", ", substs))?;
                    }
                    Ok(())
                }
                BaseTy::Param(param) => w!("{}", ^param),
                BaseTy::Float(float_ty) => w!("{}", ^float_ty.name_str()),
                BaseTy::Slice(ty) => w!("[{:?}]", ty),
                BaseTy::RawPtr(ty, Mutability::Mut) => w!("*mut {:?}", ty),
                BaseTy::RawPtr(ty, Mutability::Not) => w!("*const {:?}", ty),
                BaseTy::Ref(RefKind::Mut, ty) => w!("&mut {:?}", ty),
                BaseTy::Ref(RefKind::Shr, ty) => w!("&{:?}", ty),
                BaseTy::Tuple(tys) => {
                    if let [ty] = &tys[..] {
                        w!("({:?},)", ty)
                    } else {
                        w!("({:?})", join!(", ", tys))
                    }
                }
                BaseTy::Array(ty, c) => w!("[{:?}; {:?}]", ty, ^c),
                BaseTy::Never => w!("!"),
            }
        }
    }

    impl Pretty for GenericArg {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                GenericArg::Ty(arg) => w!("{:?}", arg),
                GenericArg::BaseTy(arg) => {
                    w!("λ{:?}. {:?}", arg.sort(), arg.as_ref().skip_binders())
                }
                GenericArg::Lifetime => w!("'_"),
            }
        }
    }

    impl Pretty for Var {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);

            match self {
                Var::Bound(bvar) => w!("{:?}", ^bvar),
                Var::Free(name) => w!("{:?}", ^name),
                Var::EVar(evar) => w!("{:?}", evar),
            }
        }
    }

    impl Pretty for VariantDef {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!(f, "({:?}) -> {:?}", join!(", ", self.fields()), &self.ret)
        }
    }

    impl_debug_with_default_cx!(
        Constraint,
        Sort,
        TyS => "ty",
        PolySig,
        BaseTy,
        FnSig,
        GenericArg,
        Index,
        VariantDef,
        PtrKind,
        Binder<FnOutput>,
    );
}
