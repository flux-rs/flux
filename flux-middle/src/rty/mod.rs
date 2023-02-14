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
pub mod subst;

use std::{collections::HashSet, fmt, hash::Hash, iter, sync::LazyLock};

pub use evars::{EVar, EVarGen};
pub use expr::{
    BoundVar, DebruijnIndex, Expr, ExprKind, Func, KVar, KVid, Loc, Name, Path, Var, INNERMOST,
};
use flux_common::index::IndexGen;
pub use flux_fixpoint::{BinOp, Constant, UnOp};
use itertools::Itertools;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_index::bit_set::BitSet;
use rustc_macros::{TyDecodable, TyEncodable};
use rustc_middle::mir::{Field, Mutability};
pub use rustc_middle::ty::{AdtFlags, FloatTy, IntTy, ParamTy, ScalarInt, UintTy};
use rustc_span::Symbol;
pub use rustc_target::abi::VariantIdx;
use toposort_scc::IndexGraph;

use self::{
    fold::{TypeFoldable, TypeFolder},
    subst::BVarSubstFolder,
};
pub use crate::{
    fhir::{FuncSort, InferMode, RefKind, Sort},
    rustc::ty::Const,
};
use crate::{
    intern::{impl_internable, Interned, List},
    rustc::mir::Place,
};

#[derive(Debug, Clone, Eq, PartialEq, Hash, TyEncodable, TyDecodable)]
pub struct AdtDef(Interned<AdtDefData>);

#[derive(Debug, Eq, PartialEq, Hash, TyEncodable, TyDecodable)]
pub struct AdtDefData {
    def_id: DefId,
    invariants: Vec<Invariant>,
    sorts: Vec<Sort>,
    flags: AdtFlags,
    nvariants: usize,
    opaque: bool,
}

#[derive(Debug, Eq, PartialEq, Hash, TyEncodable, TyDecodable)]
pub struct Invariant {
    pub pred: Binders<Expr>,
}

pub type PolyVariant = Binders<VariantDef>;

#[derive(Clone, Eq, PartialEq, Hash, TyEncodable, TyDecodable)]
pub struct VariantDef {
    pub fields: List<Ty>,
    pub ret: Ty,
}

#[derive(Clone, Eq, PartialEq, Hash, TyEncodable, TyDecodable)]
pub struct Binders<T> {
    params: List<Sort>,
    value: T,
}

#[derive(Clone, TyEncodable, TyDecodable)]
pub struct PolySig {
    pub fn_sig: Binders<FnSig>,
    pub modes: List<InferMode>,
}

#[derive(Clone, TyEncodable, TyDecodable)]
pub struct FnSig {
    requires: List<Constraint>,
    args: List<Ty>,
    output: Binders<FnOutput>,
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
    pub body: Binders<Expr>,
    pub global: bool,
}

pub struct Defn {
    pub name: Symbol,
    pub expr: Binders<Expr>,
}

pub struct UifDef {
    pub name: Symbol,
    pub sort: FuncSort,
}

pub struct Defns {
    defns: FxHashMap<Symbol, Defn>,
}

pub type Ty = Interned<TyS>;

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub struct TyS {
    kind: TyKind,
}

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub enum TyKind {
    Indexed(BaseTy, RefineArgs),
    Exists(Binders<Ty>),
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
pub struct RefineArgs(Interned<RefineArgsData>);

#[derive(Eq, Hash, PartialEq, TyEncodable, TyDecodable)]
struct RefineArgsData {
    args: Vec<Expr>,
    /// Set containing all the indices of arguments that were used as binders in the surface syntax.
    /// This is used as a hint for inferring parameters at call sites.
    is_binder: BitSet<usize>,
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
        let name_gen = IndexGen::new();
        let mut args = vec![];
        let body = self.body.replace_bvars_with_fresh_fvars(|sort| {
            let fresh = name_gen.fresh();
            args.push((fresh, sort.clone()));
            fresh
        });
        (args, body)
    }
}

impl<T> Binders<T> {
    pub fn new(value: T, params: impl Into<List<Sort>>) -> Binders<T> {
        Binders { params: params.into(), value }
    }

    pub fn params(&self) -> &[Sort] {
        &self.params
    }

    pub fn as_ref(&self) -> Binders<&T> {
        Binders { params: self.params.clone(), value: &self.value }
    }

    pub fn skip_binders(self) -> T {
        self.value
    }

    pub fn map<S>(self, f: impl FnOnce(T) -> S) -> Binders<S> {
        Binders { params: self.params, value: f(self.value) }
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

impl<T> Binders<T>
where
    T: TypeFoldable,
{
    pub fn replace_bvars(&self, args: &[Expr]) -> T {
        self.value.fold_with(&mut BVarSubstFolder::new(args))
    }

    pub fn replace_bvars_with(&self, f: impl FnMut(&Sort) -> Expr) -> T {
        let args = self.params.iter().map(f).collect_vec();
        self.replace_bvars(&args)
    }

    pub fn replace_bvars_with_fresh_fvars(&self, mut fresh: impl FnMut(&Sort) -> Name) -> T {
        self.replace_bvars_with(|sort| Expr::fvar(fresh(sort)))
    }
}

impl RefineArgs {
    pub fn new<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = (Expr, bool)>,
        T::IntoIter: ExactSizeIterator,
    {
        let iter = iter.into_iter();
        let mut bitset = BitSet::new_empty(iter.len());
        let args = iter
            .enumerate()
            .map(|(idx, (arg, is_binder))| {
                if is_binder {
                    bitset.insert(idx);
                }
                arg
            })
            .collect();
        RefineArgsData { args, is_binder: bitset }.intern()
    }

    pub fn multi(args: Vec<Expr>) -> Self {
        let is_binder = BitSet::new_empty(args.len());
        RefineArgsData { args, is_binder }.intern()
    }

    pub fn one(arg: impl Into<Expr>) -> Self {
        RefineArgsData { args: vec![arg.into()], is_binder: BitSet::new_empty(1) }.intern()
    }

    /// Return a list of bound variables. The returned value will have escaping vars which
    /// need to be put inside a [`Binders`]
    pub fn bound(n: usize) -> RefineArgs {
        RefineArgs::multi((0..n).map(|i| Expr::bvar(BoundVar::innermost(i))).collect())
    }

    pub fn is_binder(&self, i: usize) -> bool {
        self.0.is_binder.contains(i)
    }

    pub fn nth(&self, idx: usize) -> &Expr {
        &self.args()[idx]
    }

    pub fn args(&self) -> &[Expr] {
        &self.0.args
    }

    pub fn empty() -> Self {
        RefineArgsData { args: vec![], is_binder: BitSet::new_empty(0) }.intern()
    }
}

impl RefineArgsData {
    pub fn intern(self) -> RefineArgs {
        RefineArgs(Interned::new(self))
    }
}

impl PolySig {
    pub fn new(fn_sig: Binders<FnSig>, modes: impl Into<List<InferMode>>) -> PolySig {
        let modes = modes.into();
        debug_assert_eq!(fn_sig.params.len(), modes.len());
        PolySig { fn_sig, modes }
    }

    pub fn replace_bvars_with(&self, mut f: impl FnMut(&Sort, InferMode) -> Expr) -> FnSig {
        let args = iter::zip(&self.fn_sig.params, &self.modes)
            .map(|(sort, kind)| f(sort, *kind))
            .collect_vec();
        self.fn_sig.replace_bvars(&args)
    }
}

impl FnSig {
    pub fn new(
        requires: impl Into<List<Constraint>>,
        args: impl Into<List<Ty>>,
        output: Binders<FnOutput>,
    ) -> Self {
        FnSig { requires: requires.into(), args: args.into(), output }
    }

    pub fn requires(&self) -> &Constraints {
        &self.requires
    }

    pub fn args(&self) -> &[Ty] {
        &self.args
    }

    pub fn output(&self) -> &Binders<FnOutput> {
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
        sorts: Vec<Sort>,
        invariants: Vec<Invariant>,
        opaque: bool,
    ) -> Self {
        AdtDef(Interned::new(AdtDefData {
            def_id: rustc_def.did(),
            invariants,
            sorts,
            flags: rustc_def.flags(),
            nvariants: rustc_def.variants().len(),
            opaque,
        }))
    }

    pub fn def_id(&self) -> DefId {
        self.0.def_id
    }

    pub fn sorts(&self) -> &[Sort] {
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
        let fn_sig = self.as_ref().map(|variant| {
            let ret = variant.ret.shift_in_bvars(1);
            let output = Binders::new(FnOutput::new(ret, vec![]), vec![]);
            FnSig::new(vec![], variant.fields.clone(), output)
        });
        let modes = fn_sig
            .params
            .iter()
            .map(Sort::default_infer_mode)
            .collect_vec();
        PolySig::new(fn_sig, modes)
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

    pub fn indexed(bty: BaseTy, args: RefineArgs) -> Ty {
        TyKind::Indexed(bty, args).intern()
    }

    pub fn exists(ty: Binders<Ty>) -> Ty {
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
        let sorts = List::from(bty.sorts());
        let ty = Ty::indexed(bty, RefineArgs::bound(sorts.len()));
        Ty::exists(Binders::new(Ty::constr(pred, ty), sorts))
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
        debug_assert_eq!(bty.sorts().len(), 0);
        Ty::indexed(bty, RefineArgs::empty())
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
    pub fn expect_adt(&self) -> (&AdtDef, &[GenericArg], &RefineArgs) {
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
                pred: Binders::new(
                    Expr::binary_op(BinOp::Ge, BoundVar::NU, Expr::zero()),
                    vec![Sort::Int],
                ),
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

    pub fn sorts(&self) -> &[Sort] {
        match self {
            BaseTy::Int(_) | BaseTy::Uint(_) | BaseTy::Slice(_) => &[Sort::Int],
            BaseTy::Bool => &[Sort::Bool],
            BaseTy::Adt(adt_def, _) => adt_def.sorts(),
            BaseTy::Float(_)
            | BaseTy::Str
            | BaseTy::Char
            | BaseTy::RawPtr(..)
            | BaseTy::Ref(..)
            | BaseTy::Tuple(_)
            | BaseTy::Array(_, _)
            | BaseTy::Never => &[],
        }
    }
}

impl Binders<Expr> {
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
    RefineArgsData,
    AdtDefData,
    TyS,
    [Ty],
    [GenericArg],
    [Field],
    [Constraint],
    [InferMode],
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

    impl<T> Pretty for Binders<T>
    where
        T: Pretty,
    {
        default fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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

    impl Pretty for Sort {
        fn fmt(&self, _cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            std::fmt::Display::fmt(self, f)
        }
    }

    impl Pretty for Binders<Expr> {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!("|{:?}| {:?}", join!(", ", &self.params), &self.value)
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

    impl Pretty for PolySig {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            if !self.fn_sig.params.is_empty() {
                write!(
                    f,
                    "forall<{}> ",
                    self.fn_sig
                        .params
                        .iter()
                        .enumerate()
                        .format_with(", ", |(i, sort), f| {
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

    impl Pretty for Binders<FnOutput> {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            if !self.params().is_empty() {
                w!("exists<{:?}>", join!(", ", self.params()))?;
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
                TyKind::Indexed(bty, idxs) => {
                    w!("{:?}", bty)?;
                    if !cx.hide_refinements && !idxs.args().is_empty() {
                        w!("[{:?}]", idxs)?;
                    }
                    Ok(())
                }
                TyKind::Exists(Binders { params, value: ty }) => {
                    if cx.hide_refinements {
                        w!("{:?}", ty)
                    } else {
                        w!("{{ ∃[{:?}]. {:?} }}", join!(", ", params), ty)
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

    impl Pretty for RefineArgs {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!(
                "{}",
                ^self.args()
                    .iter()
                    .enumerate()
                    .format_with(", ", |(i, arg), f| {
                        if cx.show_is_binder && self.is_binder(i) {
                            f(&format_args_cx!("@{:?}", arg))
                        } else {
                            f(&format_args_cx!("{:?}", arg))
                        }
                    })
            )
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
                Var::Bound(bvar) => w!("{:?}", bvar),
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
        RefineArgs,
        VariantDef,
        PtrKind,
        Binders<FnOutput>
    );
}

impl Defns {
    pub fn new(defns: FxHashMap<Symbol, Defn>) -> Result<Self, Vec<Symbol>> {
        let raw = Defns { defns };
        raw.normalize()
    }

    fn defn_deps(&self, expr: &Binders<Expr>) -> HashSet<Symbol> {
        struct Deps<'a>(&'a mut HashSet<Symbol>);
        impl<'a> TypeFolder for Deps<'a> {
            fn fold_expr(&mut self, expr: &Expr) -> Expr {
                if let ExprKind::App(func, _) = expr.kind()
                   && let Func::Uif(sym) = func
                {
                    self.0.insert(*sym);
                }
                expr.super_fold_with(self)
            }
        }
        let mut e_deps = HashSet::new();
        expr.fold_with(&mut Deps(&mut e_deps));
        e_deps
    }

    /// Returns
    /// * either Ok(d1...dn) which are topologically sorted such that
    ///   forall i < j, di does not depend on i.e. "call" dj
    /// * or Err(d1...dn) where d1 'calls' d2 'calls' ... 'calls' dn 'calls' d1
    fn sorted_defns(&self) -> Result<Vec<Symbol>, Vec<Symbol>> {
        // 1. Make the Symbol-Index
        let mut i2s: Vec<Symbol> = Vec::new();
        let mut s2i: FxHashMap<Symbol, usize> = FxHashMap::default();
        for (i, s) in self.defns.keys().enumerate() {
            i2s.push(*s);
            s2i.insert(*s, i);
        }

        // 2. Make the dependency graph
        let mut adj_list: Vec<Vec<usize>> = vec![];
        for name in i2s.iter() {
            let defn = self.defns.get(name).unwrap();
            let deps = self.defn_deps(&defn.expr);
            let ddeps: Vec<usize> = deps
                .iter()
                .filter_map(|s| s2i.get(s).copied())
                .collect_vec();
            adj_list.push(ddeps);
        }
        let mut g = IndexGraph::from_adjacency_list(&adj_list);
        g.transpose();

        // 3. Topologically sort the graph
        match g.toposort_or_scc() {
            Ok(is) => Ok(is.iter().map(|i| i2s[*i]).collect()),
            Err(mut scc) => {
                let cycle = scc.pop().unwrap();
                Err(cycle.iter().map(|i| i2s[*i]).collect())
            }
        }
    }

    // private function normalize (expand_defns) which does the SCC-expansion
    fn normalize(mut self) -> Result<Self, Vec<Symbol>> {
        // 1. Topologically sort the Defns
        let ds = self.sorted_defns()?;

        // 2. Expand each defn in the sorted order
        let mut exp_defns = Defns { defns: FxHashMap::default() };
        for d in ds {
            if let Some(defn) = self.defns.remove(&d) {
                let expr = defn.expr.normalize(&exp_defns);
                let exp_defn = Defn { expr, ..defn };
                exp_defns.defns.insert(d, exp_defn);
            }
        }
        Ok(exp_defns)
    }

    fn func_defn(&self, f: &Symbol) -> Option<&Defn> {
        if let Some(defn) = self.defns.get(f) {
            return Some(defn);
        }
        None
    }

    fn expand_defn(defn: &Defn, args: &[Expr]) -> Expr {
        defn.expr.replace_bvars(args)
    }

    // expand a particular app if there is a known defn for it
    pub fn app(&self, func: &Symbol, args: &[Expr]) -> Expr {
        if let Some(defn) = self.func_defn(func) {
            Self::expand_defn(defn, args)
        } else {
            Expr::app(Func::Uif(*func), args)
        }
    }
}
