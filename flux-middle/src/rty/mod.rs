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

use std::{borrow::Cow, collections::HashSet, fmt, hash::Hash, iter, sync::LazyLock};

pub use evars::{EVar, EVarGen};
pub use expr::{BoundVar, DebruijnIndex, Expr, ExprKind, Loc, Name, Path, Var, INNERMOST};
pub use flux_fixpoint::{BinOp, Constant, UnOp};
use itertools::Itertools;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_index::{bit_set::BitSet, newtype_index};
use rustc_middle::mir::Field;
pub use rustc_middle::ty::{AdtFlags, FloatTy, IntTy, ParamTy, ScalarInt, UintTy};
use rustc_span::Symbol;
pub use rustc_target::abi::VariantIdx;
use toposort_scc::IndexGraph;

use self::{
    fold::{TypeFoldable, TypeFolder},
    subst::BVarFolder,
};
pub use crate::{
    fhir::{FuncSort, InferMode, RefKind, Sort},
    rustc::ty::Const,
};
use crate::{
    intern::{impl_internable, Interned, List},
    rustc::mir::Place,
};

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct AdtDef(Interned<AdtDefData>);

#[derive(Debug, Eq, PartialEq, Hash)]
pub struct AdtDefData {
    def_id: DefId,
    invariants: Vec<Invariant>,
    sorts: Vec<Sort>,
    flags: AdtFlags,
    nvariants: usize,
    opaque: bool,
}

#[derive(Debug, Eq, PartialEq, Hash)]
pub struct Invariant {
    pub pred: Binders<Expr>,
}

pub type PolyVariant = Binders<VariantDef>;

#[derive(Clone, Eq, PartialEq, Hash)]
pub struct VariantDef {
    pub fields: List<Ty>,
    pub ret: VariantRet,
}

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct VariantRet {
    pub bty: BaseTy,
    pub args: List<RefineArg>,
}

#[derive(Clone, Eq, PartialEq, Hash)]
pub struct Binders<T> {
    params: List<Sort>,
    value: T,
}

#[derive(Clone)]
pub struct PolySig {
    pub fn_sig: Binders<FnSig>,
    pub modes: List<InferMode>,
}

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
    Pred(Pred),
}

#[derive(Debug)]
pub struct Qualifier {
    pub name: String,
    pub args: Vec<(Name, Sort)>,
    pub expr: Expr,
}

pub struct Defn {
    pub name: Symbol,
    pub expr: Binders<Expr>,
}

pub struct Defns {
    defns: FxHashMap<Symbol, Defn>,
}

pub type Ty = Interned<TyS>;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct TyS {
    kind: TyKind,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum TyKind {
    Indexed(BaseTy, RefineArgs),
    Exists(BaseTy, Binders<Pred>),
    Tuple(List<Ty>),
    Uninit,
    Ptr(RefKind, Path),
    /// A pointer to a location produced by opening a box. This mostly behaves like a [`TyKind::Ptr`],
    /// with two major differences:
    /// 1. An open box can only point to a fresh location and not an arbitrary [`Path`], so we just
    ///    store a [`Name`].
    /// 2. We keep around the allocator to be able to put the box back together (you could say that
    ///    the capability to deallocate the memory stays with the pointer).
    BoxPtr(Name, Ty),
    Ref(RefKind, Ty),
    Constr(Pred, Ty),
    Param(ParamTy),
    Never,
    /// This is a bit of a hack. We use this type internally to represent the result of
    /// [`Rvalue::Discriminant`] in a way that we can recover the necessary control information
    /// when checking [`TerminatorKind::SwitchInt`].
    ///
    /// [`Rvalue::Discriminant`]: crate::rustc::mir::Rvalue::Discriminant
    /// [`TerminatorKind::SwitchInt`]: crate::rustc::mir::TerminatorKind::SwitchInt
    Discr(AdtDef, Place),
}

#[derive(Clone, Eq, Hash, PartialEq)]
pub struct RefineArgs(Interned<RefineArgsData>);

#[derive(Eq, Hash, PartialEq)]
struct RefineArgsData {
    args: Vec<RefineArg>,
    /// Set containing all the indices of arguments that were used as binders in the surface syntax.
    /// This is used as a hint for inferring parameters at call sites.
    is_binder: BitSet<usize>,
}

#[derive(Clone, Eq, Hash, PartialEq)]
pub enum RefineArg {
    Expr(Expr),
    Abs(Binders<Pred>),
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum BaseTy {
    Int(IntTy),
    Uint(UintTy),
    Bool,
    Str,
    Char,
    Array(Ty, Const),
    Slice(Ty),
    Adt(AdtDef, Substs),
    Float(FloatTy),
}

pub type Substs = List<GenericArg>;

#[derive(PartialEq, Eq, Hash)]
pub enum GenericArg {
    Ty(Ty),
    /// We treat lifetime opaquely
    Lifetime,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Pred {
    Hole,
    Kvar(KVar),
    Expr(Expr),
    And(List<Pred>),
    App(Var, List<Expr>),
}

/// In theory a kvar is just an unknown predicate that can use some variables in scope. In practice,
/// fixpoint makes a diference between the first and the rest of the variables, the first one being
/// the kvar's *self argument*. Fixpoint will only instantiate qualifiers that use the self argument.
/// Flux generalizes the self argument to be a list.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct KVar {
    pub kvid: KVid,
    pub args: List<Expr>,
    pub scope: List<Expr>,
}

newtype_index! {
    pub struct KVid {
        DEBUG_FORMAT = "$k{}"
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
}

impl<T> Binders<T>
where
    T: TypeFoldable,
{
    pub fn replace_bvars(&self, args: &[RefineArg]) -> T {
        self.value.fold_with(&mut BVarFolder::new(args))
    }

    pub fn replace_bvars_with(&self, f: impl FnMut(&Sort) -> RefineArg) -> T {
        let args = self.params.iter().map(f).collect_vec();
        self.replace_bvars(&args)
    }

    pub fn replace_bvars_with_fresh_fvars(&self, mut fresh: impl FnMut(&Sort) -> Name) -> T {
        self.replace_bvars_with(|sort| RefineArg::Expr(Expr::fvar(fresh(sort))))
    }
}

impl RefineArgs {
    pub fn new<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = (RefineArg, bool)>,
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

    pub fn multi(args: Vec<RefineArg>) -> Self {
        let is_binder = BitSet::new_empty(args.len());
        RefineArgsData { args, is_binder }.intern()
    }

    pub fn one(arg: impl Into<RefineArg>) -> Self {
        RefineArgsData { args: vec![arg.into()], is_binder: BitSet::new_empty(1) }.intern()
    }

    pub fn is_binder(&self, i: usize) -> bool {
        self.0.is_binder.contains(i)
    }

    pub fn nth(&self, idx: usize) -> &RefineArg {
        &self.args()[idx]
    }

    pub fn args(&self) -> &[RefineArg] {
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

impl RefineArg {
    #[track_caller]
    pub fn as_expr(&self) -> &Expr {
        if let RefineArg::Expr(e) = self {
            e
        } else {
            panic!("expected an `RefineArg::Expr`")
        }
    }
}

impl PolySig {
    pub fn new(fn_sig: Binders<FnSig>, modes: impl Into<List<InferMode>>) -> PolySig {
        let modes = modes.into();
        debug_assert_eq!(fn_sig.params.len(), modes.len());
        PolySig { fn_sig, modes }
    }

    pub fn replace_bvars_with(&self, mut f: impl FnMut(&Sort, InferMode) -> RefineArg) -> FnSig {
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
        ret: Ty,
        ensures: impl Into<List<Constraint>>,
    ) -> Self {
        FnSig { requires: requires.into(), args: args.into(), ret, ensures: ensures.into() }
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

impl VariantRet {
    pub fn to_ty(&self) -> Ty {
        Ty::indexed(self.bty.clone(), RefineArgs::multi(self.args.to_vec()))
    }
}

impl Ty {
    pub fn ptr(rk: RefKind, path: impl Into<Path>) -> Ty {
        TyKind::Ptr(rk, path.into()).intern()
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

    pub fn constr(p: impl Into<Pred>, ty: Ty) -> Ty {
        TyKind::Constr(p.into(), ty).intern()
    }

    pub fn unconstr(&self) -> (Ty, Pred) {
        fn go(this: &Ty, preds: &mut Vec<Pred>) -> Ty {
            if let TyKind::Constr(prd, ty) = this.kind() {
                preds.push(prd.clone());
                go(ty, preds)
            } else {
                this.clone()
            }
        }
        let mut preds = vec![];
        (go(self, &mut preds), Pred::And(List::from(preds)))
    }

    pub fn uninit() -> Ty {
        TyKind::Uninit.intern()
    }

    pub fn indexed(bty: BaseTy, args: RefineArgs) -> Ty {
        TyKind::Indexed(bty, args).intern()
    }

    pub fn exists(bty: BaseTy, pred: Binders<Pred>) -> Ty {
        TyKind::Exists(bty, pred).intern()
    }

    pub fn param(param: ParamTy) -> Ty {
        TyKind::Param(param).intern()
    }

    pub fn unit() -> Ty {
        Ty::tuple(vec![])
    }

    pub fn str() -> Ty {
        Ty::indexed(BaseTy::Str, RefineArgs::empty())
    }

    pub fn char() -> Ty {
        Ty::indexed(BaseTy::Char, RefineArgs::empty())
    }

    pub fn never() -> Ty {
        TyKind::Never.intern()
    }

    pub fn discr(adt_def: AdtDef, place: Place) -> Ty {
        TyKind::Discr(adt_def, place).intern()
    }

    pub fn is_box(&self) -> bool {
        match self.kind() {
            TyKind::Indexed(bty, _) | TyKind::Exists(bty, _) => bty.is_box(),
            _ => false,
        }
    }

    pub fn bool() -> Ty {
        Ty::exists(BaseTy::Bool, Binders::new(Pred::tt(), vec![Sort::Bool]))
    }

    pub fn int(int_ty: IntTy) -> Ty {
        Ty::exists(BaseTy::Int(int_ty), Binders::new(Pred::tt(), vec![Sort::Int]))
    }

    pub fn uint(uint_ty: UintTy) -> Ty {
        Ty::exists(BaseTy::Uint(uint_ty), Binders::new(Pred::tt(), vec![Sort::Int]))
    }

    pub fn usize() -> Ty {
        Ty::uint(UintTy::Usize)
    }

    pub fn float(float_ty: FloatTy) -> Ty {
        Ty::indexed(BaseTy::Float(float_ty), RefineArgs::empty())
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

    pub fn expect_discr(&self) -> (&AdtDef, &Place) {
        if let TyKind::Discr(adt_def, place) = self.kind() {
            (adt_def, place)
        } else {
            panic!("expected discr")
        }
    }

    pub fn expect_adt(&self) -> (&AdtDef, &[GenericArg], &RefineArgs) {
        if let TyKind::Indexed(BaseTy::Adt(adt_def, substs), idxs) = self.kind() {
            (adt_def, substs, idxs)
        } else {
            panic!("expected adt")
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

impl From<Expr> for Pred {
    fn from(e: Expr) -> Self {
        Pred::Expr(e)
    }
}

impl From<&Pred> for Pred {
    fn from(pred: &Pred) -> Self {
        pred.clone()
    }
}

impl From<&RefineArg> for RefineArg {
    fn from(arg: &RefineArg) -> Self {
        arg.clone()
    }
}

impl From<Expr> for RefineArg {
    fn from(expr: Expr) -> Self {
        RefineArg::Expr(expr)
    }
}

impl From<&Expr> for RefineArg {
    fn from(expr: &Expr) -> Self {
        RefineArg::Expr(expr.clone())
    }
}

impl BaseTy {
    pub fn adt(adt_def: AdtDef, substs: impl Into<List<GenericArg>>) -> BaseTy {
        BaseTy::Adt(adt_def, substs.into())
    }

    pub fn array(ty: Ty, c: Const) -> BaseTy {
        BaseTy::Array(ty, c)
        // Ty::indexed(BaseTy::Array(ty, c), RefineArgs::empty())
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
                    Expr::binary_op(BinOp::Ge, Expr::bvar(BoundVar::NU), Expr::zero()),
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
            | BaseTy::Array(_, _)
            | BaseTy::Float(_)
            | BaseTy::Slice(_)
            | BaseTy::Char => &[],
        }
    }

    pub fn sorts(&self) -> &[Sort] {
        match self {
            BaseTy::Int(_) | BaseTy::Uint(_) | BaseTy::Array(..) | BaseTy::Slice(_) => &[Sort::Int],
            BaseTy::Bool => &[Sort::Bool],
            BaseTy::Adt(adt_def, _) => adt_def.sorts(),
            BaseTy::Float(_) | BaseTy::Str | BaseTy::Char => &[],
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

impl Pred {
    pub fn tt() -> Pred {
        Pred::Expr(Expr::tt())
    }

    /// Simple syntactic check to see if the predicate is true. This is used mostly for filtering
    /// predicates when pretty printing but also to avoid adding unnecesary predicates to the constraint.
    pub fn is_trivially_true(&self) -> bool {
        matches!(self, Pred::Expr(e) if e.is_true())
            || matches!(self, Pred::Kvar(kvar) if kvar.args.is_empty())
            || matches!(self, Pred::And(preds) if preds.is_empty())
    }

    /// A predicate is an atom if it "self-delimiting", i.e., it has a clear boundary
    /// when printed. This is used to avoid unnecesary parenthesis when pretty printing.
    pub fn is_atom(&self) -> bool {
        match self {
            Pred::Hole | Pred::Kvar(_) | Pred::App(..) => true,
            Pred::Expr(expr) => expr.is_binary_op(),
            Pred::And(preds) => {
                match &preds[..] {
                    [] => true,
                    [pred] => pred.is_atom(),
                    _ => false,
                }
            }
        }
    }

    /// Simplify expression applying some simple rules like removing double negation. This is
    /// only used for pretty printing.
    pub fn simplify(&self) -> Pred {
        match self {
            Pred::And(preds) => {
                let preds = preds
                    .iter()
                    .map(Pred::simplify)
                    .filter(|p| !p.is_trivially_true());
                Pred::And(List::from_iter(preds))
            }
            Pred::Expr(e) => Pred::Expr(e.simplify()),
            _ => self.clone(),
        }
    }
}

impl Binders<Pred> {
    /// See [`Pred::is_trivially_true`]
    pub fn is_trivially_true(&self) -> bool {
        self.value.is_trivially_true()
    }
}

impl KVar {
    pub fn new(kvid: KVid, args: Vec<Expr>, scope: Vec<Expr>) -> Self {
        KVar { kvid, args: List::from_vec(args), scope: List::from_vec(scope) }
    }

    pub fn all_args(&self) -> impl Iterator<Item = &Expr> {
        self.args.iter().chain(&self.scope)
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
    [Pred],
    [Field],
    [KVar],
    [Constraint],
    [RefineArg],
    [InferMode]
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
    ($float_ty:pat, $idxs:pat) => {
        TyKind::Indexed(BaseTy::Float($float_ty), $idxs)
    };
}
pub use crate::_Float as Float;

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

    impl Pretty for Binders<Pred> {
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
                    "for<{}> ",
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
            w!("{:?}) -> {:?}", join!(", ", &self.args), &self.ret)?;
            if !self.ensures.is_empty() {
                w!("; [{:?}]", join!(", ", &self.ensures))?;
            }

            Ok(())
        }

        fn default_cx(tcx: TyCtxt) -> PPrintCx {
            PPrintCx::default(tcx).show_is_binder(true)
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
                    if !idxs.args().is_empty() {
                        w!("[{:?}]", idxs)?;
                    }
                    Ok(())
                }
                TyKind::Exists(bty, pred) => {
                    if pred.is_trivially_true() {
                        w!("{:?}{{}}", bty)
                    } else {
                        w!("{:?}{{{:?}}}", bty, &pred.value)
                    }
                }
                TyKind::Uninit => w!("uninit"),
                TyKind::Ptr(rk, loc) => w!("ptr({:?}, {:?})", ^rk, loc),
                TyKind::BoxPtr(loc, alloc) => w!("box({:?}, {:?})", ^loc, alloc),
                TyKind::Ref(RefKind::Mut, ty) => w!("&mut {:?}", ty),
                TyKind::Ref(RefKind::Shr, ty) => w!("&{:?}", ty),
                TyKind::Param(param) => w!("{}", ^param),
                TyKind::Tuple(tys) => w!("({:?})", join!(", ", tys)),
                TyKind::Never => w!("!"),
                TyKind::Discr(adt_def, place) => w!("discr({:?}, {:?})", adt_def.def_id(), ^place),
                TyKind::Constr(pred, ty) => w!("{{ {:?} : {:?} }}", ty, pred),
            }
        }

        fn default_cx(tcx: TyCtxt) -> PPrintCx {
            PPrintCx::default(tcx).kvar_args(KVarArgs::Hide)
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

    impl Pretty for RefineArg {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                RefineArg::Expr(e) => w!("{:?}", e),
                RefineArg::Abs(abs) => w!("{:?}", abs),
            }
        }
    }

    impl Pretty for BaseTy {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                BaseTy::Int(int_ty) => w!("{}", ^int_ty.name_str())?,
                BaseTy::Uint(uint_ty) => w!("{}", ^uint_ty.name_str())?,
                BaseTy::Bool => w!("bool")?,
                BaseTy::Str => w!("str")?,
                BaseTy::Char => w!("char")?,
                BaseTy::Adt(adt_def, _) => w!("{:?}", adt_def.def_id())?,
                BaseTy::Float(float_ty) => w!("{}", ^float_ty.name_str())?,
                BaseTy::Array(ty, c) => w!("[{:?}; {:?}]", ty, ^c)?,
                BaseTy::Slice(ty) => w!("[{:?}]", ty)?,
            }
            if let BaseTy::Adt(_, args) = self && !args.is_empty() {
                w!("<{:?}>", join!(", ", args))?;
            }
            Ok(())
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

    impl Pretty for Pred {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                Pred::Kvar(kvar) => w!("{:?}", kvar),
                Pred::Expr(expr) => w!("{:?}", expr),
                Pred::Hole => w!("*"),
                Pred::And(preds) => {
                    if preds.is_empty() {
                        w!("true")
                    } else {
                        w!("{:?}", join!(" ∧ ", preds))
                    }
                }
                Pred::App(func, args) => {
                    w!("{:?}({:?})", func, join!(", ", args))
                }
            }
        }

        fn default_cx(tcx: TyCtxt) -> PPrintCx {
            PPrintCx::default(tcx).fully_qualified_paths(true)
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

    impl Pretty for KVar {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!("{:?}", ^self.kvid)?;
            match cx.kvar_args {
                KVarArgs::All => {
                    if self.scope.is_empty() {
                        w!("({:?})", join!(", ", &self.args))?;
                    } else {
                        w!("({:?})[{:?}]", join!(", ", &self.args), join!(", ", &self.scope))?;
                    }
                }
                KVarArgs::SelfOnly => w!("({:?})", join!(", ", &self.args))?,
                KVarArgs::Hide => {}
            }
            Ok(())
        }
    }

    impl Pretty for Sort {
        fn fmt(&self, _cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!(f, "{}", ^self)
        }
    }

    impl Pretty for VariantDef {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!(f, "({:?}) -> {:?}", join!(", ", self.fields()), &self.ret)
        }
    }

    impl Pretty for VariantRet {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!(f, "{:?}", self.to_ty())
        }
    }

    impl_debug_with_default_cx!(
        Constraint,
        TyS => "ty",
        PolySig,
        BaseTy,
        Pred,
        KVar,
        FnSig,
        GenericArg,
        RefineArg,
        RefineArgs,
        VariantDef,
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
                if let ExprKind::App(f, _) = expr.kind() {
                    self.0.insert(*f);
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
            adj_list.push(deps.iter().map(|s| *s2i.get(s).unwrap()).collect());
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
            let defn = self.defns.remove(&d).unwrap();
            let expr = defn.expr.normalize(&exp_defns);
            let exp_defn = Defn { expr, ..defn };
            exp_defns.defns.insert(d, exp_defn);
        }
        Ok(exp_defns)
    }

    fn func_defn(&self, f: &Symbol) -> Option<&Defn> {
        if let Some(defn) = self.defns.get(f) {
            return Some(defn);
        }
        None
    }

    fn expand_defn(defn: &Defn, args: List<Expr>) -> Expr {
        let args = args
            .iter()
            .map(|e| RefineArg::Expr(e.clone()))
            .collect_vec();
        defn.expr.replace_bvars(&args)
    }

    // expand a particular app if there is a known defn for it
    pub fn app(&self, func: &Symbol, args: List<Expr>) -> Expr {
        if let Some(defn) = self.func_defn(func) {
            Self::expand_defn(defn, args)
        } else {
            Expr::app(*func, args)
        }
    }
}
