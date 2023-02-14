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

use std::{fmt, hash::Hash, iter, sync::LazyLock};

pub use evars::{EVar, EVarGen};
pub use expr::{DebruijnIndex, Expr, ExprKind, KVar, KVid, Loc, Name, Path, Var, INNERMOST};
use flux_common::bug;
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
    fhir::{FuncSort, InferMode, RefKind, Sort},
    rustc::ty::Const,
};
use crate::{
    intern::{impl_internable, Internable, Interned, List},
    rustc::mir::Place,
};

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
    Param(ParamTy),
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

// #[derive(Eq, Hash, PartialEq, TyEncodable, TyDecodable)]
// struct RefineArgsData {
//     args: Vec<Expr>,
//     /// Set containing all the indices of arguments that were used as binders in the surface syntax.
//     /// This is used as a hint for inferring parameters at call sites.
//     is_binder: BitSet<usize>,
// }

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
}

pub type Substs = List<GenericArg>;

#[derive(PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub enum GenericArg {
    Ty(Ty),
    /// We treat lifetime opaquely
    Lifetime,
}

impl Qualifier {
    pub fn with_fresh_fvars(&self) -> (Vec<(Name, Sort)>, Expr) {
        // let name_gen = IndexGen::new();
        // let mut args = vec![];
        todo!()
        // let body = self.body.replace_bvars_with_fresh_fvars(|sort| {
        //     let fresh = name_gen.fresh();
        //     args.push((fresh, sort.clone()));
        //     fresh
        // });
        // (args, body)
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
    pub fn replace_bvars(&self, expr: &Expr) -> T {
        self.value
            .fold_with(&mut BVarSubstFolder::new(expr))
            .normalize(&Default::default())
    }

    pub fn replace_bvars_with(&self, mut f: impl FnMut(&Sort) -> Expr) -> T {
        let expr = f(&self.sort);
        self.replace_bvars(&expr)
    }

    // pub fn replace_bvars_with_fresh_fvars(&self, mut fresh: impl FnMut(&Sort) -> Name) -> T {
    //     self.replace_bvars_with(|sort| Expr::fvar(fresh(sort)))
    // }
}

impl<T> TupleTree<T>
where
    [TupleTree<T>]: Internable,
{
    fn unit() -> Self {
        TupleTree::Tuple(List::from_vec(vec![]))
    }
}

impl<T> TupleTree<T>
where
    [TupleTree<T>]: Internable,
    T: Clone,
{
    pub fn from_expr(e: &Expr, value: T) -> Self {
        Self::from_expr_inner(e, value)
    }

    fn from_expr_inner(e: &Expr, value: T) -> Self {
        if let ExprKind::Tuple(es) = e.kind() {
            TupleTree::Tuple(List::from_vec(
                es.iter()
                    .map(|e| Self::from_expr_inner(e, value.clone()))
                    .collect(),
            ))
        } else {
            TupleTree::Leaf(value)
        }
    }
}

impl Index {
    /// Return a list of bound variables. The returned value will have escaping vars which
    /// need to be put inside a [`Binders`]
    pub fn bound(sort: &Sort) -> Index {
        fn go(sort: &Sort) -> Expr {
            if let Sort::Tuple(sorts) = sort {
                Expr::tuple(
                    sorts
                        .iter()
                        .enumerate()
                        .map(|(i, sort)| Expr::tuple_proj(go(sort), i as u32))
                        .collect_vec(),
                )
            } else {
                Expr::nu()
            }
        }
        Index::from(go(sort))
    }

    pub fn unit() -> Self {
        Index { expr: Expr::unit(), is_binder: TupleTree::unit() }
    }

    pub fn tuple(exprs: Vec<Expr>) -> Self {
        let is_binder = TupleTree::Tuple(List::from_vec(
            exprs
                .iter()
                .map(|e| TupleTree::from_expr(e, false))
                .collect(),
        ));
        let expr = Expr::tuple(exprs);
        Index { expr, is_binder }
    }
}

impl From<Expr> for Index {
    fn from(expr: Expr) -> Self {
        let is_binder = TupleTree::from_expr(&expr, false);
        Self { expr, is_binder }
    }
}

impl From<(Expr, TupleTree<bool>)> for Index {
    fn from((expr, is_binder): (Expr, TupleTree<bool>)) -> Self {
        Self { expr, is_binder }
    }
}

impl PolySig {
    pub fn new(params: &[Sort], fn_sig: FnSig, modes: impl Into<List<InferMode>>) -> PolySig {
        let modes = modes.into();
        debug_assert_eq!(params.len(), modes.len());
        let fn_sig = Binder::new(fn_sig, Sort::tuple(params));
        PolySig { fn_sig, modes }
    }

    pub fn replace_bvars_with(&self, mut f: impl FnMut(&Sort, InferMode) -> Expr) -> FnSig {
        let exprs = iter::zip(self.fn_sig.sort.as_tuple(), &self.modes)
            .map(|(sort, kind)| f(sort, *kind))
            .collect_vec();
        self.fn_sig.replace_bvars(&Expr::tuple(exprs))
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
        let modes = self
            .sort
            .as_tuple()
            .iter()
            .map(Sort::default_infer_mode)
            .collect_vec();
        PolySig::new(self.sort.as_tuple(), fn_sig, modes)
    }
}

impl Ty {
    pub fn ptr(pk: impl Into<PtrKind>, path: impl Into<Path>) -> Ty {
        TyKind::Ptr(pk.into(), path.into()).intern()
    }

    pub fn constr(p: impl Into<Expr>, ty: Ty) -> Ty {
        TyKind::Constr(p.into(), ty).intern()
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

    pub fn uninit() -> Ty {
        TyKind::Uninit.intern()
    }

    pub fn indexed(bty: BaseTy, idx: impl Into<Index>) -> Ty {
        TyKind::Indexed(bty, idx.into()).intern()
    }

    pub fn exists(ty: Binder<Ty>) -> Ty {
        TyKind::Exists(ty).intern()
    }

    /// Makes a *fully applied* existential, i.e., an existential that has binders for all the
    /// indices of the [`BaseTy`]. For example, if we have
    ///
    /// ```ignore
    /// #[flux::refined_by(a: int, b: int)]
    /// struct Pair {
    ///     #[flux::field(i32[@a])]
    ///     fst: i32,
    ///     #[flux::field(i32[@b])]
    ///     snd: i32,
    /// }
    /// ```
    /// Then, a fully applied existential for `Pair` binds both indices: `{int,int. Pair[^0.0, ^0.1] | p}`.
    ///
    /// Note that the arguments `bty` and `pred` may have escaping vars, which will be closed by
    /// wrapping them inside a [`Binders`].
    pub fn full_exists(bty: BaseTy, pred: Expr) -> Ty {
        let sort = bty.sort();
        let ty = Ty::indexed(bty, Index::bound(&sort));
        Ty::exists(Binder::new(Ty::constr(pred, ty), sort))
    }

    pub fn param(param: ParamTy) -> Ty {
        TyKind::Param(param).intern()
    }

    pub fn unit() -> Ty {
        Ty::tuple(vec![])
    }

    pub fn discr(adt_def: AdtDef, place: Place) -> Ty {
        TyKind::Discr(adt_def, place).intern()
    }

    pub fn bool() -> Ty {
        Ty::full_exists(BaseTy::Bool, Expr::tt())
    }

    pub fn int(int_ty: IntTy) -> Ty {
        Ty::full_exists(BaseTy::Int(int_ty), Expr::tt())
    }

    pub fn uint(uint_ty: UintTy) -> Ty {
        Ty::full_exists(BaseTy::Uint(uint_ty), Expr::tt())
    }

    pub fn usize() -> Ty {
        Ty::uint(UintTy::Usize)
    }

    pub fn str() -> Ty {
        Ty::indexed_by_unit(BaseTy::Str)
    }

    pub fn char() -> Ty {
        Ty::indexed_by_unit(BaseTy::Char)
    }

    pub fn float(float_ty: FloatTy) -> Ty {
        Ty::indexed_by_unit(BaseTy::Float(float_ty))
    }

    pub fn mk_ref(mode: RefKind, ty: Ty) -> Ty {
        Ty::indexed_by_unit(BaseTy::Ref(mode, ty))
    }

    pub fn tuple(tys: impl Into<List<Ty>>) -> Ty {
        Ty::indexed_by_unit(BaseTy::Tuple(tys.into()))
    }

    pub fn array(ty: Ty, c: Const) -> Ty {
        Ty::indexed_by_unit(BaseTy::Array(ty, c))
    }

    pub fn never() -> Ty {
        Ty::indexed_by_unit(BaseTy::Never)
    }

    fn indexed_by_unit(bty: BaseTy) -> Ty {
        debug_assert!(bty.sort().is_unit());
        Ty::indexed(bty, Index::unit())
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
            panic!("expected discr")
        }
    }

    #[track_caller]
    pub fn expect_adt(&self) -> (&AdtDef, &[GenericArg], &Index) {
        if let TyKind::Indexed(BaseTy::Adt(adt_def, substs), idxs) = self.kind() {
            (adt_def, substs, idxs)
        } else {
            panic!("expected adt")
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

    pub fn as_bty_skipping_binders(&self) -> Option<&BaseTy> {
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
            | BaseTy::Never => &[],
        }
    }

    pub fn sort(&self) -> Sort {
        match self {
            BaseTy::Int(_) | BaseTy::Uint(_) | BaseTy::Slice(_) => Sort::Int,
            BaseTy::Bool => Sort::Bool,
            BaseTy::Adt(adt_def, _) => adt_def.sort().clone(),
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
        panic!("invalid generic arguments for box");
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
        fn fmt(&self, _cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            std::fmt::Display::fmt(self, f)
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
            if !self.fn_sig.sort.as_tuple().is_empty() {
                write!(
                    f,
                    "forall<{}> ",
                    self.fn_sig.sort.as_tuple().iter().enumerate().format_with(
                        ", ",
                        |(i, sort), f| {
                            match self.modes[i] {
                                InferMode::KVar => f(&format_args_cx!("${:?}", ^sort)),
                                InferMode::EVar => f(&format_args_cx!("?{:?}", ^sort)),
                            }
                        }
                    )
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
            if !self.sort().as_tuple().is_empty() {
                w!("exists<{:?}>", join!(", ", self.sort().as_tuple()))?;
            }
            w!("{:?}", &self.value.ret)?;
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
                        w!("{{ ∃{:?}. {:?} }}", sort, ty)
                    }
                }
                TyKind::Uninit => w!("uninit"),
                TyKind::Ptr(pk, loc) => w!("ptr({:?}, {:?})", pk, loc),
                TyKind::Param(param) => w!("{}", ^param),
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
                    (TupleTree::Tuple(ts), ExprKind::Tuple(es)) => {
                        debug_assert_eq!(ts.len(), es.len());
                        w!("(")?;
                        for (t, e) in ts.iter().zip(es.iter()) {
                            go(cx, f, is_binder, e)?;
                            w!(", ")?;
                        }
                        w!(")")?;
                    }
                    (TupleTree::Leaf(is_binder), _) => {
                        if *is_binder {
                            w!("@{:?}", expr)?
                        } else {
                            w!("{:?}", expr)?
                        }
                    }
                    _ => bug!(),
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
                BaseTy::Float(float_ty) => w!("{}", ^float_ty.name_str()),
                BaseTy::Slice(ty) => w!("[{:?}]", ty),
                BaseTy::RawPtr(ty, Mutability::Mut) => w!("*mut {:?}", ty),
                BaseTy::RawPtr(ty, Mutability::Not) => w!("*const {:?}", ty),
                BaseTy::Ref(RefKind::Mut, ty) => w!("&mut {:?}", ty),
                BaseTy::Ref(RefKind::Shr, ty) => w!("&{:?}", ty),
                BaseTy::Tuple(tys) => w!("({:?})", join!(", ", tys)),
                BaseTy::Array(ty, c) => w!("[{:?}; {:?}]", ty, ^c),
                BaseTy::Never => w!("!"),
            }
        }
    }

    impl Pretty for GenericArg {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                GenericArg::Ty(ty) => w!("{:?}", ty),
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
        TyS => "ty",
        PolySig,
        BaseTy,
        FnSig,
        GenericArg,
        Index,
        VariantDef,
        PtrKind,
        Binder<FnOutput>
    );
}
