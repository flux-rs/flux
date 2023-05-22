//! Defines how flux represents refinement types internally. Definitions in this module are used
//! during refinement type checking. A couple of important differences between definitions in this
//! module and in [`crate::fhir`] are:
//!
//! * Types in this module use debruijn indices to represent local binders.
//! * Data structures are interned so they can be cheaply cloned.
pub mod evars;
mod expr;
pub mod fold;
pub(crate) mod normalize;
pub mod refining;
pub mod subst;

use std::{fmt, hash::Hash, iter, slice, sync::LazyLock};

pub use evars::{EVar, EVarGen};
pub use expr::{Expr, ExprKind, KVar, KVid, Loc, Name, Path, Var};
use flux_common::{bug, index::IndexGen};
pub use flux_fixpoint::{BinOp, Constant, UnOp};
use itertools::Itertools;
pub use normalize::Defns;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_macros::{TyDecodable, TyEncodable};
pub use rustc_middle::{
    mir::Mutability,
    ty::{AdtFlags, ClosureKind, FloatTy, IntTy, ParamTy, ScalarInt, UintTy},
};
use rustc_span::Symbol;
pub use rustc_target::abi::VariantIdx;
use rustc_type_ir::INNERMOST;

use self::{
    fold::TypeFoldable,
    subst::{BoundVarReplacer, FnMutDelegate},
};
use crate::{
    fhir::FuncKind,
    global_env::GlobalEnv,
    intern::{impl_internable, Internable, Interned, List},
    queries::QueryResult,
    rustc::mir::Place,
};
pub use crate::{
    fhir::InferMode,
    rustc::ty::{
        BoundRegion, BoundRegionKind, BoundVar, BoundVariableKind, Const, EarlyBoundRegion,
        Region::{self, *},
    },
};

#[derive(Debug, Clone)]
pub struct Generics {
    pub params: List<GenericParamDef>,
    pub parent: Option<DefId>,
    pub parent_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GenericParamDef {
    pub kind: GenericParamDefKind,
    pub def_id: DefId,
    pub index: u32,
    pub name: Symbol,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum GenericParamDefKind {
    Type { has_default: bool },
    BaseTy,
    Lifetime,
}

#[derive(Clone, Debug)]
pub struct GenericPredicates {
    pub parent: Option<DefId>,
    pub predicates: List<Predicate>,
}

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct Predicate {
    kind: Binder<PredicateKind>,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum PredicateKind {
    FnTrait(FnTraitPredicate),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct FnTraitPredicate {
    pub self_ty: Ty,
    pub tupled_args: Ty,
    pub output: Ty,
    pub kind: ClosureKind,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub enum SortCtor {
    Set,
    User { name: Symbol, arity: usize },
}

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub enum Sort {
    Int,
    Bool,
    Real,
    BitVec(usize),
    Loc,
    Param(ParamTy),
    Tuple(List<Sort>),
    Func(FuncSort),
    App(SortCtor, List<Sort>),
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
#[derive(Clone, Debug, TyEncodable, TyDecodable)]
pub enum Opaqueness<T> {
    Opaque,
    Transparent(T),
}

pub static INT_TYS: [IntTy; 6] =
    [IntTy::Isize, IntTy::I8, IntTy::I16, IntTy::I32, IntTy::I64, IntTy::I128];
pub static UINT_TYS: [UintTy; 6] =
    [UintTy::Usize, UintTy::U8, UintTy::U16, UintTy::U32, UintTy::U64, UintTy::U128];

#[derive(Debug, Clone, Eq, PartialEq, Hash, TyEncodable, TyDecodable)]
pub struct Invariant {
    pub pred: Binder<Expr>,
}

pub type PolyVariants = List<Binder<VariantDef>>;
pub type PolyVariant = Binder<VariantDef>;

#[derive(Clone, Eq, PartialEq, Hash, TyEncodable, TyDecodable)]
pub struct VariantDef {
    pub fields: List<Ty>,
    pub ret: Ty,
}

#[derive(Clone, Eq, PartialEq, Hash, TyEncodable, TyDecodable)]
pub struct Binder<T> {
    vars: List<BoundVariableKind>,
    sort: Sort,
    value: T,
}

#[derive(Clone, Debug, TyEncodable, TyDecodable)]
pub struct EarlyBinder<T>(pub T);

#[derive(Clone, Eq, PartialEq, Hash, TyEncodable, TyDecodable, Debug)]
pub enum TupleTree<T>
where
    [TupleTree<T>]: Internable,
{
    Tuple(List<TupleTree<T>>),
    Leaf(T),
}

#[derive(Clone, TyEncodable, TyDecodable)]
pub struct PolyFnSig {
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
    pub name: Symbol,
    pub body: Binder<Expr>,
    pub global: bool,
}

pub struct Defn {
    pub name: Symbol,
    pub expr: Binder<Expr>,
}

#[derive(Debug)]
pub struct FuncDecl {
    pub name: Symbol,
    pub sort: FuncSort,
    pub kind: FuncKind,
}

#[derive(Debug)]
pub struct ClosureOblig {
    pub oblig_def_id: DefId,
    pub oblig_sig: PolyFnSig,
}

pub type PolyTy = Binder<Ty>;
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
    Param(ParamTy),
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub enum PtrKind {
    Shr(Region),
    Mut(Region),
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
    Ref(Region, Ty, Mutability),
    Tuple(List<Ty>),
    Array(Ty, Const),
    Never,
    Closure(DefId, List<Ty>),
    Param(ParamTy),
}

pub type Substs = List<GenericArg>;

#[derive(PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub enum GenericArg {
    Ty(Ty),
    BaseTy(Binder<Ty>),
    Lifetime(Region),
}

// <<<<<<< HEAD
// impl FnTraitPredicate {
//     pub fn to_poly_sig(&self, closure_id: DefId, tys: List<Ty>) -> PolyFnSig {
//         let closure_ty = Ty::closure(closure_id, tys);
//         let env_ty = match self.kind {
//             ClosureKind::Fn => Ty::mk_ref(RefKind::Shr, closure_ty),
//             ClosureKind::FnMut => Ty::mk_ref(RefKind::Mut, closure_ty),
// =======
impl Predicate {
    pub fn kind(&self) -> Binder<PredicateKind> {
        self.kind.clone()
    }
}

impl Binder<FnTraitPredicate> {
    pub fn self_ty(&self) -> Binder<Ty> {
        self.as_ref()
            .map(|fn_trait_pred| fn_trait_pred.self_ty.clone())
    }

    pub fn to_closure_sig(&self, closure_id: DefId, tys: List<Ty>) -> PolyFnSig {
        let bound_vars: List<BoundVariableKind> = self
            .vars
            .iter()
            .copied()
            .chain(std::iter::once(BoundVariableKind::Region(BoundRegionKind::BrEnv)))
            .collect();

        let pred = self.as_ref().skip_binder();

        let closure_ty = Ty::closure(closure_id, tys);
        let env_ty = match pred.kind {
            ClosureKind::Fn => {
                let br = BoundRegion {
                    var: BoundVar::from_usize(bound_vars.len() - 1),
                    kind: BoundRegionKind::BrEnv,
                };
                Ty::mk_ref(ReLateBound(INNERMOST, br), closure_ty, Mutability::Not)
            }
            ClosureKind::FnMut => {
                let br = BoundRegion {
                    var: BoundVar::from_usize(bound_vars.len() - 1),
                    kind: BoundRegionKind::BrEnv,
                };
                Ty::mk_ref(ReLateBound(INNERMOST, br), closure_ty, Mutability::Mut)
            }
            ClosureKind::FnOnce => closure_ty,
        };
        let inputs = std::iter::once(env_ty)
            .chain(pred.tupled_args.expect_tuple().iter().cloned())
            .collect_vec();

        let fn_sig = FnSig::new(
            vec![],
            inputs,
            Binder::with_sort(FnOutput::new(pred.output.clone(), vec![]), Sort::unit()),
        );

        let params = self
            .sort()
            .expect_tuple()
            .iter()
            .map(|sort| (sort.clone(), sort.default_infer_mode()));
        PolyFnSig::new(bound_vars, params, fn_sig)
    }
}

impl Generics {
    pub fn param_at(&self, param_index: usize, genv: &GlobalEnv) -> QueryResult<GenericParamDef> {
        if let Some(index) = param_index.checked_sub(self.parent_count) {
            Ok(self.params[index].clone())
        } else {
            genv.generics_of(self.parent.expect("parent_count > 0 but no parent?"))?
                .param_at(param_index, genv)
        }
    }
}

impl Sort {
    pub fn tuple(sorts: impl Into<List<Sort>>) -> Self {
        Sort::Tuple(sorts.into())
    }

    pub fn app(ctor: SortCtor, sorts: impl Into<List<Sort>>) -> Self {
        Sort::App(ctor, sorts.into())
    }

    pub fn unit() -> Self {
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

    pub fn is_unit(&self) -> bool {
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
    pub fn new(input: Sort, output: Sort) -> Self {
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
        let body = self.body.replace_bound_expr(|sort| {
            Expr::fold_sort(sort, |s| {
                let fresh = name_gen.fresh();
                params.push((fresh, s.clone()));
                Expr::fvar(fresh)
            })
        });
        (params, body)
    }
}

impl<T> Binder<T> {
    pub fn new(value: T, vars: List<BoundVariableKind>, sort: Sort) -> Binder<T> {
        Binder { vars, sort, value }
    }

    pub fn with_sort(value: T, sort: Sort) -> Binder<T> {
        Binder { vars: List::empty(), sort, value }
    }

    pub fn sort(&self) -> &Sort {
        &self.sort
    }

    pub fn as_ref(&self) -> Binder<&T> {
        Binder { vars: self.vars.clone(), sort: self.sort.clone(), value: &self.value }
    }

    pub fn skip_binder(self) -> T {
        self.value
    }

    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Binder<U> {
        Binder { vars: self.vars, sort: self.sort, value: f(self.value) }
    }

    pub fn try_map<U, E>(self, f: impl FnOnce(T) -> Result<U, E>) -> Result<Binder<U>, E> {
        Ok(Binder { vars: self.vars, sort: self.sort, value: f(self.value)? })
    }
}

impl<T> EarlyBinder<T> {
    pub fn as_ref(&self) -> EarlyBinder<&T> {
        EarlyBinder(&self.0)
    }

    pub fn as_deref(&self) -> EarlyBinder<&T::Target>
    where
        T: std::ops::Deref,
    {
        EarlyBinder(self.0.deref())
    }

    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> EarlyBinder<U> {
        EarlyBinder(f(self.0))
    }

    pub fn skip_binder(self) -> T {
        self.0
    }
}

impl<T> Binder<T>
where
    T: TypeFoldable,
{
    pub fn replace_bound_expr(&self, f: impl FnOnce(&Sort) -> Expr) -> T {
        debug_assert!(self.vars.is_empty());
        let expr = f(&self.sort);
        let delegate = FnMutDelegate { expr, regions: |_| bug!("unexpected escaping region") };
        self.value
            .fold_with(&mut BoundVarReplacer::new(delegate))
            .normalize(&Default::default())
    }
}

impl<T: TypeFoldable> EarlyBinder<T> {
    pub fn subst(self, generics: &[GenericArg], refine: &[Expr]) -> T
    where
        T: std::fmt::Debug,
    {
        self.0
            .fold_with(&mut subst::GenericsSubstFolder::new(generics, refine))
    }

    pub fn subst_generics(self, generics: &[GenericArg]) -> T
    where
        T: std::fmt::Debug,
    {
        self.subst(generics, &[])
    }

    pub fn subst_identity(self) -> T {
        self.0
    }
}

impl EarlyBinder<GenericPredicates> {
    pub fn predicates(&self) -> EarlyBinder<List<Predicate>> {
        EarlyBinder(self.0.predicates.clone())
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

    pub fn as_leaf(&self) -> Option<&T> {
        match self {
            TupleTree::Leaf(value) => Some(value),
            _ => None,
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

impl PolyFnSig {
    pub fn new(
        vars: List<BoundVariableKind>,
        params: impl IntoIterator<Item = (Sort, InferMode)>,
        fn_sig: FnSig,
    ) -> PolyFnSig {
        let (sorts, modes) = params.into_iter().unzip();
        let fn_sig = Binder::new(fn_sig, vars, Sort::Tuple(List::from_vec(sorts)));
        PolyFnSig { fn_sig, modes: List::from_vec(modes) }
    }

    pub fn replace_bound_vars(
        &self,
        replace_region: impl FnMut(BoundRegion) -> Region,
        mut replace_expr: impl FnMut(&Sort, InferMode) -> Expr,
    ) -> FnSig {
        let exprs = iter::zip(self.fn_sig.sort.expect_tuple(), &self.modes)
            .map(|(sort, kind)| replace_expr(sort, *kind))
            .collect_vec();

        let delegate = FnMutDelegate { expr: Expr::tuple(exprs), regions: replace_region };

        self.fn_sig
            .value
            .fold_with(&mut BoundVarReplacer::new(delegate))
            .normalize(&Default::default())
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
    pub fn new(
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

    pub fn ok_or_else<E>(self, err: impl FnOnce() -> E) -> Result<T, E> {
        match self {
            Opaqueness::Transparent(v) => Ok(v),
            Opaqueness::Opaque => Err(err()),
        }
    }

    #[track_caller]
    pub fn expect(self, msg: &str) -> T {
        match self {
            Opaqueness::Transparent(val) => val,
            Opaqueness::Opaque => bug!("{}", msg),
        }
    }
}

impl<T, E> Opaqueness<Result<T, E>> {
    pub fn transpose(self) -> Result<Opaqueness<T>, E> {
        match self {
            Opaqueness::Transparent(Ok(x)) => Ok(Opaqueness::Transparent(x)),
            Opaqueness::Transparent(Err(e)) => Err(e),
            Opaqueness::Opaque => Ok(Opaqueness::Opaque),
        }
    }
}

impl EarlyBinder<PolyVariant> {
    pub fn to_poly_sig(&self) -> EarlyBinder<PolyFnSig> {
        let fn_sig = self
            .0
            .as_ref()
            .map(|variant| {
                let ret = variant.ret.shift_in_escaping(1);
                let output = Binder::with_sort(FnOutput::new(ret, vec![]), Sort::unit());
                FnSig::new(vec![], variant.fields.clone(), output)
            })
            .skip_binder();
        let params = self
            .0
            .sort
            .expect_tuple()
            .iter()
            .map(|sort| (sort.clone(), Sort::default_infer_mode(sort)))
            .collect_vec();
        EarlyBinder(PolyFnSig::new(List::empty(), params, fn_sig))
    }
}

impl PtrKind {
    pub fn from_ref(r: Region, m: Mutability) -> Self {
        match m {
            Mutability::Not => PtrKind::Shr(r),
            Mutability::Mut => PtrKind::Mut(r),
        }
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
        Ty::exists(Binder::with_sort(Ty::constr(pred, ty), sort))
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
        TyKind::Param(param_ty).intern()
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

    pub fn mk_ref(region: Region, ty: Ty, mutbl: Mutability) -> Ty {
        BaseTy::Ref(region, ty, mutbl).into_ty()
    }

    pub fn tuple(tys: impl Into<List<Ty>>) -> Ty {
        BaseTy::Tuple(tys.into()).into_ty()
    }

    pub fn array(ty: Ty, c: Const) -> Ty {
        BaseTy::Array(ty, c).into_ty()
    }

    pub fn closure(did: DefId, tys: impl Into<List<Ty>>) -> Ty {
        BaseTy::Closure(did, tys.into()).into_ty()
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

    pub(crate) fn expect_tuple(&self) -> &[Ty] {
        if let TyKind::Indexed(BaseTy::Tuple(tys), _) = self.kind() {
            tys
        } else {
            bug!("expected adt")
        }
    }

    /// Whether the type is an `int` or a `uint`
    pub fn is_integral(&self) -> bool {
        self.as_bty_skipping_existentials()
            .map(BaseTy::is_integral)
            .unwrap_or_default()
    }

    /// Whether the type is a `bool`
    pub fn is_bool(&self) -> bool {
        self.as_bty_skipping_existentials()
            .map(BaseTy::is_bool)
            .unwrap_or_default()
    }

    pub fn is_uninit(&self) -> bool {
        matches!(self.kind(), TyKind::Uninit)
    }

    pub fn as_bty_skipping_existentials(&self) -> Option<&BaseTy> {
        match self.kind() {
            TyKind::Indexed(bty, _) => Some(bty),
            TyKind::Exists(ty) => Some(ty.as_ref().skip_binder().as_bty_skipping_existentials()?),
            TyKind::Constr(_, ty) => ty.as_bty_skipping_existentials(),
            _ => None,
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

    pub fn invariants(&self, overflow_checking: bool) -> &[Invariant] {
        match self {
            BaseTy::Adt(adt_def, _) => adt_def.invariants(),
            BaseTy::Uint(uint_ty) => uint_invariants(*uint_ty, overflow_checking),
            BaseTy::Int(int_ty) => int_invariants(*int_ty, overflow_checking),
            BaseTy::Bool
            | BaseTy::Str
            | BaseTy::Float(_)
            | BaseTy::Slice(_)
            | BaseTy::RawPtr(_, _)
            | BaseTy::Char
            | BaseTy::Ref(..)
            | BaseTy::Tuple(_)
            | BaseTy::Array(_, _)
            | BaseTy::Closure(_, _)
            | BaseTy::Never
            | BaseTy::Param(_) => &[],
        }
    }

    fn into_ty(self) -> Ty {
        let sort = self.sort();
        if sort.is_unit() {
            Ty::indexed(self, Index::unit())
        } else {
            Ty::exists(Binder::with_sort(Ty::indexed(self, Expr::nu()), sort))
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
            | BaseTy::Closure(_, _)
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

fn uint_invariants(uint_ty: UintTy, overflow_checking: bool) -> &'static [Invariant] {
    static DEFAULT: LazyLock<[Invariant; 1]> = LazyLock::new(|| {
        [Invariant {
            pred: Binder::with_sort(
                Expr::binary_op(BinOp::Ge, Expr::nu(), Expr::zero()),
                Sort::Int,
            ),
        }]
    });

    static OVERFLOW: LazyLock<FxHashMap<UintTy, [Invariant; 2]>> = LazyLock::new(|| {
        UINT_TYS
            .into_iter()
            .map(|uint_ty| {
                let invariants = [
                    Invariant {
                        pred: Binder::with_sort(
                            Expr::binary_op(BinOp::Ge, Expr::nu(), Expr::zero()),
                            Sort::Int,
                        ),
                    },
                    Invariant {
                        pred: Binder::with_sort(
                            Expr::binary_op(BinOp::Lt, Expr::nu(), Expr::uint_max(uint_ty)),
                            Sort::Int,
                        ),
                    },
                ];
                (uint_ty, invariants)
            })
            .collect()
    });
    if overflow_checking {
        &OVERFLOW[&uint_ty]
    } else {
        &*DEFAULT
    }
}

fn int_invariants(int_ty: IntTy, overflow_checking: bool) -> &'static [Invariant] {
    static DEFAULT: [Invariant; 0] = [];

    static OVERFLOW: LazyLock<FxHashMap<IntTy, [Invariant; 2]>> = LazyLock::new(|| {
        INT_TYS
            .into_iter()
            .map(|int_ty| {
                let invariants = [
                    Invariant {
                        pred: Binder::with_sort(
                            Expr::binary_op(BinOp::Ge, Expr::nu(), Expr::int_min(int_ty)),
                            Sort::Int,
                        ),
                    },
                    Invariant {
                        pred: Binder::with_sort(
                            Expr::binary_op(BinOp::Lt, Expr::nu(), Expr::int_max(int_ty)),
                            Sort::Int,
                        ),
                    },
                ];
                (int_ty, invariants)
            })
            .collect()
    });
    if overflow_checking {
        &OVERFLOW[&int_ty]
    } else {
        &DEFAULT
    }
}

impl_internable!(
    AdtDefData,
    TyS,
    [Ty],
    [GenericArg],
    [Constraint],
    [InferMode],
    [TupleTree<bool>],
    [Sort],
    [GenericParamDef],
    [Predicate],
    [PolyVariant],
    [Invariant],
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
    ($($pats:pat),+ $(,)?) => {
        TyKind::Indexed(BaseTy::Ref($($pats),+), _)
    };
}
pub use crate::_Ref as Ref;

mod pretty {
    use rustc_middle::ty::TyCtxt;
    use rustc_type_ir::DebruijnIndex;

    use super::*;
    use crate::{pretty::*, rustc::ty::region_to_string};

    impl<T> Pretty for Binder<T>
    where
        T: Pretty,
    {
        default fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!("for<{:?}> {:?}", &self.sort, &self.value)
        }
    }

    impl Pretty for SortCtor {
        fn fmt(&self, _cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(_cx, f);
            match self {
                SortCtor::Set => w!("Set"),
                SortCtor::User { name, .. } => w!("{}", ^name),
            }
        }
    }

    impl Pretty for Sort {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                Sort::Bool => w!("bool"),
                Sort::Int => w!("int"),
                Sort::Real => w!("real"),
                Sort::BitVec(w) => w!("bitvec({})", ^w),
                Sort::Loc => w!("loc"),
                Sort::Func(sort) => w!("{:?}", sort),
                Sort::Tuple(sorts) => {
                    if let [sort] = &sorts[..] {
                        w!("({:?},)", sort)
                    } else {
                        w!("({:?})", join!(", ", sorts))
                    }
                }
                Sort::App(ctor, sorts) => {
                    if let [sort] = &sorts[..] {
                        w!("{:?}<{:?}>", ctor, sort)
                    } else {
                        w!("{:?}<{:?}>", ctor, join!(", ", sorts))
                    }
                }
                Sort::Param(param_ty) => w!("sortof({})", ^param_ty),
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

    impl Pretty for PolyFnSig {
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
                TyKind::Exists(Binder { sort, value: ty, .. }) => {
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
                TyKind::Param(param_ty) => w!("{}#t", ^param_ty),
            }
        }

        fn default_cx(tcx: TyCtxt) -> PPrintCx {
            PPrintCx::default(tcx).kvar_args(KVarArgs::Hide)
        }
    }

    impl Pretty for PtrKind {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                PtrKind::Shr(r) => w!("shr[{:?}]", r),
                PtrKind::Mut(r) => w!("mut[{:?}]", r),
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
                if let ExprKind::Tuple(es) = expr.kind() {
                    w!("(")?;
                    for (is_binder, e) in iter::zip(is_binder.split(), es) {
                        go(cx, f, is_binder, e)?;
                        w!(", ")?;
                    }
                    w!(")")?;
                } else if let Some(true) = is_binder.as_leaf() {
                    w!("@{:?}", expr)?;
                } else {
                    w!("{:?}", expr)?;
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
                BaseTy::Param(param) => w!("{}#b", ^param),
                BaseTy::Float(float_ty) => w!("{}", ^float_ty.name_str()),
                BaseTy::Slice(ty) => w!("[{:?}]", ty),
                BaseTy::RawPtr(ty, Mutability::Mut) => w!("*mut {:?}", ty),
                BaseTy::RawPtr(ty, Mutability::Not) => w!("*const {:?}", ty),
                BaseTy::Ref(region, ty, mutbl) => {
                    w!("&{:?} {}{:?}", region, ^mutbl.prefix_str(), ty)
                }
                BaseTy::Tuple(tys) => {
                    if let [ty] = &tys[..] {
                        w!("({:?},)", ty)
                    } else {
                        w!("({:?})", join!(", ", tys))
                    }
                }
                BaseTy::Array(ty, c) => w!("[{:?}; {:?}]", ty, ^c),
                BaseTy::Never => w!("!"),
                BaseTy::Closure(did, substs) => {
                    w!("{:?}", did)?;
                    if !substs.is_empty() {
                        w!("<{:?}>", join!(", ", substs))?;
                    }
                    Ok(())
                }
            }
        }
    }

    impl Pretty for GenericArg {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                GenericArg::Ty(arg) => w!("{:?}", arg),
                GenericArg::BaseTy(arg) => {
                    w!("λ{:?}. {:?}", arg.sort(), arg.as_ref().skip_binder())
                }
                GenericArg::Lifetime(re) => w!("{:?}", re),
            }
        }
    }

    impl Pretty for VariantDef {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!("({:?}) -> {:?}", join!(", ", self.fields()), &self.ret)
        }
    }

    impl Pretty for Region {
        fn fmt(&self, _cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!("{}", ^region_to_string(*self))
        }
    }

    impl Pretty for DebruijnIndex {
        fn fmt(&self, _cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!("^{}", ^self.as_usize())
        }
    }

    impl_debug_with_default_cx!(
        Constraint,
        Sort,
        TyS => "ty",
        PolyFnSig,
        BaseTy,
        FnSig,
        GenericArg,
        Index,
        VariantDef,
        PtrKind,
        Binder<FnOutput>,
        FuncSort,
    );
}
