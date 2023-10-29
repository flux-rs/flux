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
pub mod projections;
pub mod refining;
pub mod subst;

use std::{fmt, hash::Hash, iter, slice, sync::LazyLock};

pub use evars::{EVar, EVarGen};
pub use expr::{ESpan, Expr, ExprKind, HoleKind, KVar, KVid, Loc, Name, Path, Var};
use flux_common::{bug, index::IndexGen};
pub use flux_fixpoint::{BinOp, Constant, UnOp};
use itertools::Itertools;
pub use normalize::Defns;
use rustc_data_structures::unord::UnordMap;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_index::IndexSlice;
use rustc_macros::{TyDecodable, TyEncodable};
use rustc_middle::ty::ParamConst;
pub use rustc_middle::{
    mir::Mutability,
    ty::{AdtFlags, ClosureKind, FloatTy, IntTy, ParamTy, ScalarInt, UintTy},
};
use rustc_span::Symbol;
pub use rustc_target::abi::{VariantIdx, FIRST_VARIANT};
pub use rustc_type_ir::INNERMOST;

use self::{
    fold::TypeFoldable,
    subst::{BoundVarReplacer, FnMutDelegate},
};
use crate::{
    fhir::FuncKind,
    global_env::GlobalEnv,
    intern::{impl_internable, impl_slice_internable, Internable, Interned, List},
    queries::QueryResult,
    rustc::{
        self,
        mir::Place,
        ty::{GeneratorArgsParts, ValueConst, VariantDef},
    },
};
pub use crate::{
    fhir::InferMode,
    rustc::ty::{
        BoundRegion, BoundRegionKind, BoundVar, Const, EarlyBoundRegion, FreeRegion,
        Region::{self, *},
    },
};

#[derive(Debug, Clone)]
pub struct Generics {
    pub params: List<GenericParamDef>,
    pub refine_params: List<RefineParam>,
    pub parent: Option<DefId>,
    pub parent_count: usize,
    pub parent_refine_count: usize,
}

#[derive(PartialEq, Eq, Debug, Clone, Hash)]
pub struct RefineParam {
    pub sort: Sort,
    pub mode: InferMode,
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
    SplTy,
    BaseTy,
    Lifetime,
    Const { has_default: bool },
}

#[derive(Debug, Clone)]
pub struct GenericPredicates {
    pub parent: Option<DefId>,
    pub predicates: List<Clause>,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Clause {
    kind: Binder<ClauseKind>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ClauseKind {
    FnTrait(FnTraitPredicate),
    Trait(TraitPredicate),
    Projection(ProjectionPredicate),
    GeneratorOblig(GeneratorObligPredicate),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TraitPredicate {
    pub trait_ref: TraitRef,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TraitRef {
    pub def_id: DefId,
    pub args: GenericArgs,
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct ProjectionPredicate {
    pub projection_ty: AliasTy,
    pub term: Ty,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct FnTraitPredicate {
    pub self_ty: Ty,
    pub tupled_args: Ty,
    pub output: Ty,
    pub kind: ClosureKind,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct GeneratorObligPredicate {
    pub def_id: DefId,
    pub args: GenericArgs,
    pub output: Ty,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub enum SortCtor {
    Set,
    Map,
    User { name: Symbol, arity: usize },
}

/// [SortVar] are used for polymorphic sorts (Set, Map etc.) and they should occur
/// "bound" under a PolyFuncSort; i.e. should be < than the number of params in the
/// PolyFuncSort.
#[derive(Clone, PartialEq, Eq, Debug, Hash, TyEncodable, TyDecodable)]
pub struct SortVar {
    pub index: usize,
}

impl From<usize> for SortVar {
    fn from(index: usize) -> Self {
        SortVar { index }
    }
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
    Func(PolyFuncSort),
    App(SortCtor, List<Sort>),
    Var(SortVar),
}

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub struct FuncSort {
    inputs_and_output: List<Sort>,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, TyEncodable, TyDecodable)]
pub struct PolyFuncSort {
    params: usize,
    fsort: FuncSort,
}

impl PolyFuncSort {
    pub fn skip_binders(&self) -> FuncSort {
        self.fsort.clone()
    }

    pub fn params(&self) -> usize {
        self.params
    }

    pub fn new(params: usize, fsort: FuncSort) -> Self {
        PolyFuncSort { params, fsort }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, TyEncodable, TyDecodable)]
pub struct AdtDef(Interned<AdtDefData>);

#[derive(Debug, Eq, PartialEq, Hash, TyEncodable, TyDecodable)]
pub struct AdtDefData {
    invariants: Vec<Invariant>,
    sort: Sort, // TODO: Binder<Sort>
    opaque: bool,
    rustc: rustc::ty::AdtDef,
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

pub type PolyVariants = List<Binder<VariantSig>>;
pub type PolyVariant = Binder<VariantSig>;

#[derive(Clone, Eq, PartialEq, Hash, TyEncodable, TyDecodable)]
pub struct VariantSig {
    pub fields: List<Ty>,
    pub ret: Ty,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, TyEncodable, TyDecodable)]
pub enum BoundVariableKind {
    Region(BoundRegionKind),
    Refine(Sort, InferMode),
}

#[derive(Clone, Eq, PartialEq, Hash, TyEncodable, TyDecodable)]
pub struct Binder<T> {
    vars: List<BoundVariableKind>,
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

pub type PolyFnSig = Binder<FnSig>;

#[derive(Clone, TyEncodable, TyDecodable)]
pub struct FnSig {
    requires: List<Constraint>,
    args: List<Ty>,
    output: Binder<FnOutput>,
}

#[derive(Clone, Debug, TyEncodable, TyDecodable)]
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
    pub sort: PolyFuncSort,
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

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable, Debug)]
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
    Downcast(AdtDef, GenericArgs, Ty, VariantIdx, List<Ty>),
    Blocked(Ty),
    Alias(AliasKind, AliasTy),
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
    Adt(AdtDef, GenericArgs),
    Float(FloatTy),
    RawPtr(Ty, Mutability),
    Ref(Region, Ty, Mutability),
    Tuple(List<Ty>),
    Array(Ty, Const),
    Never,
    Closure(DefId, List<Ty>),
    Generator(DefId, GenericArgs),
    GeneratorWitness(Binder<List<Ty>>),
    Param(ParamTy),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, TyEncodable, TyDecodable)]
pub struct AliasTy {
    pub args: GenericArgs,
    /// Holds the refinement-arguments for opaque-types; empty for projections
    pub refine_args: RefineArgs,
    pub def_id: DefId,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, TyEncodable, TyDecodable)]
pub enum AliasKind {
    Projection,
    Opaque,
}

pub type RefineArgs = List<Expr>;
pub type GenericArgs = List<GenericArg>;

pub type OpaqueArgsMap = FxHashMap<DefId, (GenericArgs, RefineArgs)>;

#[derive(PartialEq, Clone, Eq, Hash, TyEncodable, TyDecodable)]
pub enum GenericArg {
    Ty(Ty),
    BaseTy(Binder<Ty>),
    Lifetime(Region),
    Const(Const),
}

impl GenericArgs {
    pub fn identity_for_item(genv: &GlobalEnv, def_id: impl Into<DefId>) -> QueryResult<Self> {
        let mut args = vec![];
        let generics = genv.generics_of(def_id)?;
        Self::fill_item(genv, &mut args, &generics, &mut |param, _| {
            GenericArg::from_param_def(param)
        })?;
        Ok(List::from_vec(args))
    }

    fn fill_item<F>(
        genv: &GlobalEnv,
        args: &mut Vec<GenericArg>,
        generics: &Generics,
        mk_kind: &mut F,
    ) -> QueryResult<()>
    where
        F: FnMut(&GenericParamDef, &[GenericArg]) -> GenericArg,
    {
        if let Some(def_id) = generics.parent {
            let parent_generics = genv.generics_of(def_id)?;
            Self::fill_item(genv, args, &parent_generics, mk_kind)?;
        }
        for param in &generics.params {
            let kind = mk_kind(param, args);
            assert_eq!(param.index as usize, args.len(), "{args:#?}, {generics:#?}");
            args.push(kind);
        }
        Ok(())
    }
}

impl GenericArg {
    pub fn expect_type(&self) -> &Ty {
        if let GenericArg::Ty(ty) = self {
            ty
        } else {
            bug!("expected `rty::GenericArg::Ty`, found {:?}", self)
        }
    }
    pub fn is_valid_base_arg(&self) -> bool {
        let res = match self {
            GenericArg::Ty(ty) => ty.kind().is_valid_base_ty(),
            GenericArg::BaseTy(bty) => bty.skip_binder_as_ref().kind().is_valid_base_ty(),
            _ => false,
        };
        // println!("TRACE: is_valid_base arg: {:?} => {res:?}", self);
        res
    }

    fn from_param_def(param: &GenericParamDef) -> Self {
        match param.kind {
            GenericParamDefKind::Type { .. } | GenericParamDefKind::SplTy => {
                let param_ty = ParamTy { index: param.index, name: param.name };
                GenericArg::Ty(Ty::param(param_ty))
            }
            GenericParamDefKind::Lifetime => {
                let region =
                    EarlyBoundRegion { index: param.index, name: param.name, def_id: param.def_id };
                GenericArg::Lifetime(Region::ReEarlyBound(region))
            }
            GenericParamDefKind::Const { .. } => {
                let param_const = ParamConst { index: param.index, name: param.name };
                GenericArg::Const(Const::Param(param_const))
            }
            GenericParamDefKind::BaseTy => {
                bug!("")
            }
        }
    }
}

impl Clause {
    pub fn new(vars: impl Into<List<BoundVariableKind>>, kind: ClauseKind) -> Self {
        Clause { kind: Binder::new(kind, vars.into()) }
    }

    pub fn kind(&self) -> ClauseKind {
        // FIXME(nilehmann) we should deal with the binder in all the places this is used instead of blindly skipping it here
        self.kind.clone().skip_binder()
    }
}

pub struct GeneratorArgs {
    pub args: GenericArgs,
}

impl GeneratorArgs {
    pub fn new(parts: GeneratorArgsParts<GenericArg>) -> Self {
        let args = parts
            .parent_args
            .iter()
            .cloned()
            .chain([
                parts.resume_ty.clone(),
                parts.yield_ty.clone(),
                parts.return_ty.clone(),
                parts.witness.clone(),
                parts.tupled_upvars_ty.clone(),
            ])
            .collect();
        GeneratorArgs { args }
    }

    pub fn resume_ty(&self) -> Ty {
        self.split().resume_ty.expect_type().clone()
    }

    pub fn tupled_upvars_ty(&self) -> Ty {
        self.split().tupled_upvars_ty.expect_type().clone()
    }
}

impl GeneratorArgs {
    pub fn split(&self) -> GeneratorArgsParts<GenericArg> {
        match &self.args[..] {
            [ref parent_args @ .., resume_ty, yield_ty, return_ty, witness, tupled_upvars_ty] => {
                GeneratorArgsParts {
                    parent_args,
                    resume_ty,
                    yield_ty,
                    return_ty,
                    witness,
                    tupled_upvars_ty,
                }
            }
            _ => bug!("generator args missing synthetics"),
        }
    }
}

impl GenericArgs {
    pub fn as_generator(&self) -> GeneratorArgs {
        GeneratorArgs { args: self.clone() }
    }
}

impl FnTraitPredicate {
    pub fn to_closure_sig(&self, closure_id: DefId, tys: List<Ty>) -> PolyFnSig {
        let mut vars = vec![];

        let closure_ty = Ty::closure(closure_id, tys);
        let env_ty = match self.kind {
            ClosureKind::Fn => {
                vars.push(BoundVariableKind::Region(BoundRegionKind::BrEnv));
                let br = BoundRegion {
                    var: BoundVar::from_usize(vars.len() - 1),
                    kind: BoundRegionKind::BrEnv,
                };
                Ty::mk_ref(ReLateBound(INNERMOST, br), closure_ty, Mutability::Not)
            }
            ClosureKind::FnMut => {
                vars.push(BoundVariableKind::Region(BoundRegionKind::BrEnv));
                let br = BoundRegion {
                    var: BoundVar::from_usize(vars.len() - 1),
                    kind: BoundRegionKind::BrEnv,
                };
                Ty::mk_ref(ReLateBound(INNERMOST, br), closure_ty, Mutability::Mut)
            }
            ClosureKind::FnOnce => closure_ty,
        };
        let inputs = std::iter::once(env_ty)
            .chain(self.tupled_args.expect_tuple().iter().cloned())
            .collect_vec();

        let fn_sig = FnSig::new(
            vec![],
            inputs,
            Binder::new(FnOutput::new(self.output.clone(), vec![]), List::empty()),
        );

        PolyFnSig::new(fn_sig, List::from(vars))
    }
}

impl GeneratorObligPredicate {
    pub fn to_closure_sig(&self) -> PolyFnSig {
        let vars = vec![];
        let pred_args = self.args.as_generator();

        let tys = pred_args
            .tupled_upvars_ty()
            .expect_tuple()
            .iter()
            .cloned()
            .collect_vec();

        let env_ty = Ty::closure(self.def_id, tys);
        let resume_ty = pred_args.resume_ty();
        let requires = vec![];

        let inputs = vec![env_ty, resume_ty];

        let output = Binder::new(FnOutput::new(self.output.clone(), vec![]), List::empty());

        PolyFnSig::new(FnSig::new(requires, inputs, output), List::from(vars))
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

    pub fn refine_count(&self) -> usize {
        self.parent_refine_count + self.refine_params.len()
    }

    pub fn refine_param_at(
        &self,
        param_index: usize,
        genv: &GlobalEnv,
    ) -> QueryResult<RefineParam> {
        if let Some(index) = param_index.checked_sub(self.parent_refine_count) {
            Ok(self.refine_params[index].clone())
        } else {
            genv.generics_of(self.parent.expect("parent_count > 0 but no parent?"))?
                .refine_param_at(param_index, genv)
        }
    }

    /// Iterate and collect all refinement parameters in this item including parents
    pub fn collect_all_refine_params<T, S>(
        &self,
        genv: &GlobalEnv,
        mut f: impl FnMut(RefineParam) -> T,
    ) -> QueryResult<S>
    where
        S: FromIterator<T>,
    {
        (0..self.refine_count())
            .map(|i| Ok(f(self.refine_param_at(i, genv)?)))
            .try_collect()
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
    pub fn expect_func(&self) -> &PolyFuncSort {
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

    pub fn is_unit(&self) -> bool {
        matches!(self, Sort::Tuple(sorts) if sorts.is_empty())
    }

    /// Whether the sort is a function with return sort bool
    fn is_pred(&self) -> bool {
        matches!(self, Sort::Func(fsort) if fsort.skip_binders().output().is_bool())
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
    pub fn new(mut inputs: Vec<Sort>, output: Sort) -> Self {
        inputs.push(output);
        FuncSort { inputs_and_output: List::from_vec(inputs) }
    }

    pub fn inputs(&self) -> &[Sort] {
        &self.inputs_and_output[0..self.inputs_and_output.len() - 1]
    }

    pub fn output(&self) -> &Sort {
        &self.inputs_and_output[self.inputs_and_output.len() - 1]
    }
}

impl Qualifier {
    pub fn with_fresh_fvars(&self) -> (Vec<(Name, Sort)>, Expr) {
        let name_gen = IndexGen::new();
        let mut params = vec![];
        let body = self.body.replace_bound_exprs_with(|sort, _| {
            Expr::fold_sort(sort, |s| {
                let fresh = name_gen.fresh();
                params.push((fresh, s.clone()));
                Expr::fvar(fresh)
            })
        });
        (params, body)
    }
}

impl BoundVariableKind {
    fn expect_refine(&self) -> (&Sort, InferMode) {
        if let BoundVariableKind::Refine(sort, mode) = self {
            (sort, *mode)
        } else {
            bug!("expected `BoundVariableKind::Refine`")
        }
    }
}

impl<T> Binder<T> {
    pub fn new(value: T, vars: List<BoundVariableKind>) -> Binder<T> {
        Binder { vars, value }
    }

    pub fn with_sorts(value: T, sorts: impl IntoIterator<Item = Sort>) -> Binder<T> {
        let vars = sorts
            .into_iter()
            .map(|s| {
                let infer_mode = s.default_infer_mode();
                BoundVariableKind::Refine(s, infer_mode)
            })
            .collect();
        Binder { vars, value }
    }

    pub fn with_sort(value: T, sort: Sort) -> Binder<T> {
        Binder::with_sorts(value, [sort])
    }

    pub fn vars(&self) -> &List<BoundVariableKind> {
        &self.vars
    }

    pub fn as_ref(&self) -> Binder<&T> {
        Binder { vars: self.vars.clone(), value: &self.value }
    }

    pub fn skip_binder(self) -> T {
        self.value
    }

    pub fn skip_binder_as_ref(&self) -> &T {
        &self.value
    }

    pub fn rebind<U>(self, value: U) -> Binder<U> {
        Binder { vars: self.vars, value }
    }

    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Binder<U> {
        Binder { vars: self.vars, value: f(self.value) }
    }

    pub fn try_map<U, E>(self, f: impl FnOnce(T) -> Result<U, E>) -> Result<Binder<U>, E> {
        Ok(Binder { vars: self.vars, value: f(self.value)? })
    }
}

impl List<BoundVariableKind> {
    pub fn to_sort_list(&self) -> List<Sort> {
        self.iter()
            .map(|kind| {
                match kind {
                    BoundVariableKind::Region(_) => {
                        bug!("`to_sort_list` called on bound variable list with non-refinements")
                    }
                    BoundVariableKind::Refine(sort, _) => sort.clone(),
                }
            })
            .collect()
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
    pub fn replace_bound_vars(
        &self,
        replace_region: impl FnMut(BoundRegion) -> Region,
        mut replace_expr: impl FnMut(&Sort, InferMode) -> Expr,
    ) -> T {
        let mut exprs = UnordMap::default();
        let delegate = FnMutDelegate {
            exprs: |idx| {
                exprs
                    .entry(idx)
                    .or_insert_with(|| {
                        let (sort, mode) = self.vars[idx as usize].expect_refine();
                        replace_expr(sort, mode)
                    })
                    .clone()
            },
            regions: replace_region,
        };

        self.value
            .fold_with(&mut BoundVarReplacer::new(delegate))
            .normalize(&Default::default())
    }

    pub fn replace_bound_exprs(&self, exprs: &[Expr]) -> T {
        let delegate = FnMutDelegate {
            exprs: |idx| exprs[idx as usize].clone(),
            regions: |_| bug!("unexpected escaping region"),
        };
        self.value
            .fold_with(&mut BoundVarReplacer::new(delegate))
            .normalize(&Default::default())
    }

    pub fn replace_bound_expr(&self, expr: &Expr) -> T {
        debug_assert!(matches!(&self.vars[..], [BoundVariableKind::Refine(..)]));
        self.replace_bound_exprs(slice::from_ref(expr))
    }

    pub fn replace_bound_exprs_with(&self, mut f: impl FnMut(&Sort, InferMode) -> Expr) -> T {
        let exprs = self
            .vars
            .iter()
            .map(|param| {
                let (sort, mode) = param.expect_refine();
                f(sort, mode)
            })
            .collect_vec();
        self.replace_bound_exprs(&exprs)
    }
}

impl Binder<Ty> {
    pub fn into_ty(self) -> Ty {
        if self.vars.is_empty() {
            self.value
        } else {
            Ty::exists(self)
        }
    }
}

impl<T: TypeFoldable> EarlyBinder<T> {
    pub fn instantiate(self, args: &[GenericArg], refine_args: &[Expr]) -> T {
        self.0
            .fold_with(&mut subst::GenericsSubstFolder::new(Some(args), refine_args))
    }

    pub fn instantiate_identity(self, refine_args: &[Expr]) -> T {
        self.0
            .fold_with(&mut subst::GenericsSubstFolder::new(None, refine_args))
    }
}

impl EarlyBinder<GenericPredicates> {
    pub fn predicates(&self) -> EarlyBinder<List<Clause>> {
        EarlyBinder(self.0.predicates.clone())
    }

    pub fn instantiate_identity(
        self,
        genv: &GlobalEnv,
        refine_args: &[Expr],
    ) -> QueryResult<Vec<Clause>> {
        let mut predicates = vec![];
        self.instantiate_identity_into(genv, refine_args, &mut predicates)?;
        Ok(predicates)
    }

    fn instantiate_identity_into(
        self,
        genv: &GlobalEnv,
        refine_args: &[Expr],
        predicates: &mut Vec<Clause>,
    ) -> QueryResult<()> {
        if let Some(def_id) = self.0.parent {
            genv.predicates_of(def_id)?
                .instantiate_identity_into(genv, refine_args, predicates)?;
        }
        predicates.extend(
            self.0
                .predicates
                .iter()
                .cloned()
                .map(|p| EarlyBinder(p).instantiate_identity(refine_args)),
        );
        Ok(())
    }
}

impl VariantSig {
    pub fn new(fields: Vec<Ty>, ret: Ty) -> Self {
        VariantSig { fields: List::from_vec(fields), ret }
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
        TupleTree::Tuple(List::empty())
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

impl From<ValueConst> for Index {
    fn from(value: ValueConst) -> Self {
        let c = Constant::from(value.val);
        let expr = Expr::constant(c);
        Index { expr, is_binder: TupleTree::Leaf(false) }
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
        rustc: rustc::ty::AdtDef,
        sort: Sort,
        invariants: Vec<Invariant>,
        opaque: bool,
    ) -> Self {
        AdtDef(Interned::new(AdtDefData { invariants, sort, opaque, rustc }))
    }

    pub fn did(&self) -> DefId {
        self.0.rustc.did()
    }

    pub fn sort(&self) -> &Sort {
        &self.0.sort
    }

    pub fn is_box(&self) -> bool {
        self.0.rustc.is_box()
    }

    pub fn is_enum(&self) -> bool {
        self.0.rustc.is_enum()
    }

    pub fn is_struct(&self) -> bool {
        self.0.rustc.is_struct()
    }

    pub fn variants(&self) -> &IndexSlice<VariantIdx, VariantDef> {
        self.0.rustc.variants()
    }

    pub fn variant(&self, idx: VariantIdx) -> &VariantDef {
        self.0.rustc.variant(idx)
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
    pub fn to_poly_fn_sig(&self) -> EarlyBinder<PolyFnSig> {
        self.as_ref().map(|poly_fn_sig| {
            poly_fn_sig.as_ref().map(|variant| {
                let ret = variant.ret.shift_in_escaping(1);
                let output = Binder::new(FnOutput::new(ret, vec![]), List::empty());
                FnSig::new(vec![], variant.fields.clone(), output)
            })
        })
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
    pub fn alias(kind: AliasKind, alias_ty: AliasTy) -> Ty {
        TyKind::Alias(kind, alias_ty).intern()
    }

    pub fn opaque(def_id: impl Into<DefId>, args: GenericArgs, refine_args: RefineArgs) -> Ty {
        TyKind::Alias(AliasKind::Opaque, AliasTy { def_id: def_id.into(), args, refine_args })
            .intern()
    }

    pub fn projection(alias_ty: AliasTy) -> Ty {
        Self::alias(AliasKind::Projection, alias_ty)
    }

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

    pub fn downcast(
        adt: AdtDef,
        args: GenericArgs,
        ty: Ty,
        variant: VariantIdx,
        fields: List<Ty>,
    ) -> Ty {
        TyKind::Downcast(adt, args, ty, variant, fields).intern()
    }

    pub fn blocked(ty: Ty) -> Ty {
        TyKind::Blocked(ty).intern()
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

    pub fn mk_slice(ty: Ty) -> Ty {
        BaseTy::Slice(ty).into_ty()
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

    pub fn generator(did: DefId, args: impl Into<List<GenericArg>>) -> Ty {
        BaseTy::Generator(did, args.into()).into_ty()
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

    pub fn unblocked(&self) -> Ty {
        match self.kind() {
            TyKind::Blocked(ty) => ty.clone(),
            _ => self.clone(),
        }
    }
}

impl TyKind {
    fn intern(self) -> Ty {
        Interned::new(TyS { kind: self })
    }

    fn is_valid_base_ty(&self) -> bool {
        match self {
            TyKind::Param(_) | TyKind::Indexed(_, _) | TyKind::Exists(_) => true,
            TyKind::Constr(_, ty) => ty.kind().is_valid_base_ty(),
            TyKind::Uninit
            | TyKind::Ptr(_, _)
            | TyKind::Discr(_, _)
            | TyKind::Downcast(_, _, _, _, _)
            | TyKind::Blocked(_)
            | TyKind::Alias(_, _) => false,
        }
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
        if let TyKind::Indexed(BaseTy::Adt(adt_def, args), idx) = self.kind() {
            (adt_def, args, idx)
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

    pub fn is_box(&self) -> bool {
        self.as_bty_skipping_existentials()
            .map(BaseTy::is_box)
            .unwrap_or_default()
    }

    pub fn is_struct(&self) -> bool {
        self.as_bty_skipping_existentials()
            .map(BaseTy::is_struct)
            .unwrap_or_default()
    }

    pub fn is_closure(&self) -> bool {
        self.as_bty_skipping_existentials()
            .map(BaseTy::is_closure)
            .unwrap_or_default()
    }

    pub fn is_tuple(&self) -> bool {
        self.as_bty_skipping_existentials()
            .map(BaseTy::is_tuple)
            .unwrap_or_default()
    }

    pub fn is_array(&self) -> bool {
        self.as_bty_skipping_existentials()
            .map(BaseTy::is_array)
            .unwrap_or_default()
    }

    pub fn is_slice(&self) -> bool {
        self.as_bty_skipping_existentials()
            .map(BaseTy::is_slice)
            .unwrap_or_default()
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

impl AliasTy {
    pub fn new(
        def_id: DefId,
        args: impl Into<GenericArgs>,
        refine_args: impl Into<RefineArgs>,
    ) -> Self {
        AliasTy { def_id, args: args.into(), refine_args: refine_args.into() }
    }

    /// This method work only with associated type projections (i.e., no opaque tpes)
    pub fn self_ty(&self) -> &Ty {
        self.args[0].expect_type()
    }
}

impl BaseTy {
    pub fn adt(adt_def: AdtDef, args: impl Into<GenericArgs>) -> BaseTy {
        BaseTy::Adt(adt_def, args.into())
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

    fn is_struct(&self) -> bool {
        matches!(self, BaseTy::Adt(adt_def, _) if adt_def.is_struct())
    }

    fn is_closure(&self) -> bool {
        matches!(self, BaseTy::Closure(..))
    }

    fn is_tuple(&self) -> bool {
        matches!(self, BaseTy::Tuple(..))
    }

    fn is_array(&self) -> bool {
        matches!(self, BaseTy::Array(..))
    }

    fn is_slice(&self) -> bool {
        matches!(self, BaseTy::Slice(..))
    }

    pub fn is_box(&self) -> bool {
        matches!(self, BaseTy::Adt(adt_def, _) if adt_def.is_box())
    }

    pub fn invariants(&self, overflow_checking: bool) -> &[Invariant] {
        match self {
            BaseTy::Adt(adt_def, _) => adt_def.invariants(),
            BaseTy::Uint(uint_ty) => uint_invariants(*uint_ty, overflow_checking),
            BaseTy::Int(int_ty) => int_invariants(*int_ty, overflow_checking),
            _ => &[],
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
        // CODESYNC(sort-of, 3) sorts should be given consistently
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
            | BaseTy::Generator(_, _)
            | BaseTy::GeneratorWitness(_)
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
pub fn box_args(args: &GenericArgs) -> (&Ty, &Ty) {
    if let [GenericArg::Ty(boxed), GenericArg::Ty(alloc)] = &args[..] {
        (boxed, alloc)
    } else {
        bug!("invalid generic arguments for box");
    }
}

fn uint_invariants(uint_ty: UintTy, overflow_checking: bool) -> &'static [Invariant] {
    static DEFAULT: LazyLock<[Invariant; 1]> = LazyLock::new(|| {
        [Invariant {
            pred: Binder::with_sort(
                Expr::binary_op(BinOp::Ge, Expr::nu(), Expr::zero(), None),
                Sort::Int,
            ),
        }]
    });

    static OVERFLOW: LazyLock<UnordMap<UintTy, [Invariant; 2]>> = LazyLock::new(|| {
        UINT_TYS
            .into_iter()
            .map(|uint_ty| {
                let invariants = [
                    Invariant {
                        pred: Binder::with_sort(
                            Expr::binary_op(BinOp::Ge, Expr::nu(), Expr::zero(), None),
                            Sort::Int,
                        ),
                    },
                    Invariant {
                        pred: Binder::with_sort(
                            Expr::binary_op(BinOp::Lt, Expr::nu(), Expr::uint_max(uint_ty), None),
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

    static OVERFLOW: LazyLock<UnordMap<IntTy, [Invariant; 2]>> = LazyLock::new(|| {
        INT_TYS
            .into_iter()
            .map(|int_ty| {
                let invariants = [
                    Invariant {
                        pred: Binder::with_sort(
                            Expr::binary_op(BinOp::Ge, Expr::nu(), Expr::int_min(int_ty), None),
                            Sort::Int,
                        ),
                    },
                    Invariant {
                        pred: Binder::with_sort(
                            Expr::binary_op(BinOp::Lt, Expr::nu(), Expr::int_max(int_ty), None),
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

impl_internable!(AdtDefData, TyS);
impl_slice_internable!(
    Ty,
    GenericArg,
    Constraint,
    InferMode,
    TupleTree<bool>,
    Sort,
    GenericParamDef,
    Clause,
    PolyVariant,
    Invariant,
    BoundVariableKind,
    RefineParam,
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

    impl Pretty for BoundVariableKind {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                BoundVariableKind::Region(re) => w!("{:?}", re),
                BoundVariableKind::Refine(sort, mode) => {
                    if let InferMode::KVar = mode {
                        w!("${:?}", sort)
                    } else {
                        w!("{:?}", sort)
                    }
                }
            }
        }
    }

    impl Pretty for ClauseKind {
        fn fmt(&self, _cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(_cx, f);
            match self {
                ClauseKind::FnTrait(pred) => w!("FnTrait ({pred:?})"),
                ClauseKind::Trait(pred) => w!("Trait ({pred:?})"),
                ClauseKind::Projection(pred) => w!("Projection ({pred:?})"),
                ClauseKind::GeneratorOblig(pred) => w!("Projection ({pred:?})"),
            }
        }
    }

    impl Pretty for BoundRegionKind {
        fn fmt(&self, _cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                BoundRegionKind::BrAnon => w!("'<annon>"),
                BoundRegionKind::BrNamed(_, sym) => w!("{sym}"),
                BoundRegionKind::BrEnv => w!("'<env>"),
            }
        }
    }

    impl<T> Pretty for Binder<T>
    where
        T: Pretty,
    {
        default fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!(
                "for<{}> {:?}",
                ^self.vars
                    .iter()
                    .format_with(", ", |s, f| f(&format_args_cx!("{:?}", s))),
                &self.value
            )
        }
    }

    impl Pretty for Binder<Expr> {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!(
                "|{}| {:?}",
                ^self.vars
                    .iter()
                    .format_with(", ", |s, f| f(&format_args_cx!("{:?}", s))),
                &self.value
            )
        }
    }

    impl<T: Pretty> std::fmt::Debug for Binder<T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            pprint_with_default_cx(f, self, None)
        }
    }

    impl Pretty for PolyFnSig {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            let vars = &self.vars;
            if !vars.is_empty() {
                w!(
                    "for<{}> ",
                    ^vars.iter().format_with(", ", |kind, f| {
                        f(&format_args_cx!("{:?}", kind))
                    })
                )?;
            }
            w!("{:?}", &self.value)
        }
    }

    impl Pretty for SortCtor {
        fn fmt(&self, _cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(_cx, f);
            match self {
                SortCtor::Set => w!("Set"),
                SortCtor::Map => w!("Map"),
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
                Sort::Var(n) => w!("@{}", ^n.index),
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
                Sort::Param(param_ty) => w!("{}::sort", ^param_ty),
            }
        }
    }

    impl Pretty for FuncSort {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!("({}) -> {:?}",
                ^self.inputs()
                    .iter()
                    .format_with(", ", |s, f| f(&format_args_cx!("{:?}", s))),
                self.output()
            )
        }
    }

    impl Pretty for PolyFuncSort {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            if self.params == 0 {
                w!("{:?}", &self.fsort)
            } else {
                w!("for<{}> {:?}", ^self.params, &self.fsort)
            }
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
            let vars = &self.vars;
            w!("exists<{:?}> {:?}", join!(", ", vars), &self.value.ret)?;
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
                TyKind::Exists(Binder { vars, value: ty }) => {
                    if cx.hide_refinements {
                        w!("{:?}", ty)
                    } else {
                        w!("∃{}. {:?}",
                            ^vars
                                .iter()
                                .format_with(", ", |s, f| f(&format_args_cx!("{:?}", s))),
                            ty
                        )
                    }
                }
                TyKind::Uninit => w!("uninit"),
                TyKind::Ptr(pk, loc) => w!("ptr({:?}, {:?})", pk, loc),
                TyKind::Discr(adt_def, place) => w!("discr({:?}, {:?})", adt_def.did(), ^place),
                TyKind::Constr(pred, ty) => {
                    if cx.hide_refinements {
                        w!("{:?}", ty)
                    } else {
                        w!("{{ {:?} | {:?} }}", ty, pred)
                    }
                }
                TyKind::Param(param_ty) => w!("{}", ^param_ty),
                TyKind::Downcast(adt, .., variant_idx, fields) => {
                    w!("{:?}::{}", adt.did(), ^adt.variant(*variant_idx).name)?;
                    if !fields.is_empty() {
                        w!("({:?})", join!(", ", fields))?;
                    }
                    Ok(())
                }
                TyKind::Blocked(ty) => w!("†{:?}", ty),
                TyKind::Alias(AliasKind::Projection, alias_ty) => {
                    let assoc_name = cx.tcx.item_name(alias_ty.def_id);
                    let trait_ref = cx.tcx.parent(alias_ty.def_id);
                    w!("<{:?} as {:?}>::{}", &alias_ty.args[0], trait_ref, ^assoc_name)?;
                    if alias_ty.args.len() > 1 {
                        w!("<{:?}>", join!(", ", &alias_ty.args[1..]))?;
                    }
                    Ok(())
                }
                TyKind::Alias(AliasKind::Opaque, alias_ty) => {
                    w!(
                        "Alias(Opaque, {:?}, [{:?}], [{:?}])",
                        alias_ty.def_id,
                        join!(", ", &alias_ty.args),
                        join!(", ", &alias_ty.refine_args)
                    )
                }
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
                PtrKind::Shr(re) => {
                    w!("shr")?;
                    if !cx.hide_regions {
                        w!("[{:?}]", re)?;
                    }
                    Ok(())
                }
                PtrKind::Mut(re) => {
                    w!("mut")?;
                    if !cx.hide_regions {
                        w!("[{:?}]", re)?;
                    }
                    Ok(())
                }
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
                    for (i, (is_binder, e)) in iter::zip(is_binder.split(), es).enumerate() {
                        if i > 0 {
                            w!(" ")?;
                        }
                        go(cx, f, is_binder, e)?;
                        w!(",")?;
                    }
                } else if let Some(true) = is_binder.as_leaf() && !cx.hide_binder {
                    w!("@{:?}", expr)?;
                } else {
                    w!("{:?}", expr)?;
                }
                Ok(())
            }
            go(cx, f, &self.is_binder, &self.expr)
        }
    }

    impl Pretty for AliasKind {
        fn fmt(&self, _cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(_cx, f);
            match self {
                AliasKind::Projection => w!("Projection"),
                AliasKind::Opaque => w!("Opaque"),
            }
        }
    }

    impl Pretty for List<Ty> {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            if let [ty] = &self[..] {
                w!("({:?},)", ty)
            } else {
                w!("({:?})", join!(", ", self))
            }
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
                BaseTy::Adt(adt_def, args) => {
                    w!("{:?}", adt_def.did())?;
                    let args = args
                        .iter()
                        .filter(|arg| !cx.hide_regions || !matches!(arg, GenericArg::Lifetime(_)))
                        .collect_vec();
                    if !args.is_empty() {
                        w!("<{:?}>", join!(", ", args))?;
                    }
                    Ok(())
                }
                BaseTy::Param(param) => w!("{}", ^param),
                BaseTy::Float(float_ty) => w!("{}", ^float_ty.name_str()),
                BaseTy::Slice(ty) => w!("[{:?}]", ty),
                BaseTy::RawPtr(ty, Mutability::Mut) => w!("*mut {:?}", ty),
                BaseTy::RawPtr(ty, Mutability::Not) => w!("*const {:?}", ty),
                BaseTy::Ref(re, ty, mutbl) => {
                    w!("&")?;
                    if !cx.hide_regions {
                        w!("{:?} ", re)?;
                    }
                    w!("{}{:?}",  ^mutbl.prefix_str(), ty)
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
                BaseTy::Closure(did, args) => {
                    w!("Closure {:?}<{:?}>", did, args)
                }
                BaseTy::Generator(did, args) => {
                    w!("Generator {:?}", did)?;
                    let args = args
                        .iter()
                        .filter(|arg| !cx.hide_regions || !matches!(arg, GenericArg::Lifetime(_)))
                        .collect_vec();
                    if !args.is_empty() {
                        w!("<{:?}>", join!(", ", args))?;
                    }
                    Ok(())
                }
                BaseTy::GeneratorWitness(args) => {
                    w!("GeneratorWitness<{:?}>", args)
                }
            }
        }
    }

    impl Pretty for Const {
        fn fmt(&self, _cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                Const::Param(p) => w!("{}", ^p.name.as_str()),
                Const::Value(v) => w!("^{}", ^v.val),
            }
        }
    }

    impl Pretty for GenericArg {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                GenericArg::Ty(arg) => w!("{:?}", arg),
                GenericArg::BaseTy(arg) => {
                    w!("λ{}. {:?}",
                        ^arg.vars
                            .iter()
                            .format_with(", ", |s, f| f(&format_args_cx!("{:?}", ^s))),
                        arg.as_ref().skip_binder()
                    )
                }
                GenericArg::Lifetime(re) => w!("{:?}", re),
                GenericArg::Const(c) => w!("{:?}", c),
            }
        }
    }

    impl Pretty for VariantSig {
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
        BaseTy,
        FnSig,
        GenericArg,
        Index,
        VariantSig,
        PtrKind,
        FuncSort,
    );
}
