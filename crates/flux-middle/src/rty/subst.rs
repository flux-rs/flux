use std::{cmp::Ordering, collections::hash_map};

use flux_common::{bug, tracked_span_bug};
use rustc_hash::FxHashMap;
use rustc_middle::ty::RegionVid;
use rustc_type_ir::DebruijnIndex;

use self::fold::FallibleTypeFolder;
use super::{
    evars::EVarSol,
    fold::{TypeFolder, TypeSuperFoldable},
};
use crate::rty::*;

/// See `flux_refineck::type_env::TypeEnv::assign`
pub fn match_regions(a: &Ty, b: &rustc::ty::Ty) -> Ty {
    let a = replace_regions_with_unique_vars(a);
    let mut subst = RegionSubst::default();
    subst.infer_from_ty(&a, b);
    subst.apply(&a)
}

/// Replace all regions with a [`ReVar`] assigning each a unique [`RegionVid`]. This is used
/// to have a unique identifier for each position such that we can infer a region substitution.
fn replace_regions_with_unique_vars(ty: &Ty) -> Ty {
    struct Replacer {
        next_rvid: u32,
    }
    impl TypeFolder for Replacer {
        fn fold_region(&mut self, _: &Region) -> Region {
            let rvid = self.next_rvid;
            self.next_rvid += 1;
            Region::ReVar(RegionVid::from_u32(rvid))
        }
    }

    ty.fold_with(&mut Replacer { next_rvid: 0 })
}

#[derive(Default, Debug)]
struct RegionSubst {
    map: UnordMap<RegionVid, Region>,
}

impl RegionSubst {
    fn apply<T: TypeFoldable>(&self, t: &T) -> T {
        struct Folder<'a>(&'a RegionSubst);
        impl TypeFolder for Folder<'_> {
            fn fold_region(&mut self, re: &Region) -> Region {
                if let ReVar(rvid) = re
                    && let Some(region) = self.0.map.get(rvid)
                {
                    *region
                } else {
                    *re
                }
            }
        }
        t.fold_with(&mut Folder(self))
    }

    fn infer_from_ty(&mut self, a: &Ty, b: &rustc::ty::Ty) {
        use rustc::ty;
        match (a.kind(), b.kind()) {
            (TyKind::Exists(ty_a), _) => {
                self.infer_from_ty(ty_a.as_ref().skip_binder(), b);
            }
            (TyKind::Constr(_, ty_a), _) => {
                self.infer_from_ty(ty_a, b);
            }
            (TyKind::Indexed(bty_a, _), _) => {
                self.infer_from_bty(bty_a, b);
            }
            (TyKind::Ptr(PtrKind::Mut(re_a), _), ty::TyKind::Ref(re_b, _, mutbl)) => {
                debug_assert!(mutbl.is_mut());
                self.infer_from_region(*re_a, *re_b);
            }
            (TyKind::StrgRef(re_a, ..), ty::TyKind::Ref(re_b, _, mutbl)) => {
                debug_assert!(mutbl.is_mut());
                self.infer_from_region(*re_a, *re_b);
            }
            _ => {}
        }
    }

    fn infer_from_bty(&mut self, a: &BaseTy, ty: &rustc::ty::Ty) {
        use rustc::ty;
        match (a, ty.kind()) {
            (BaseTy::Ref(re_a, ty_a, _), ty::TyKind::Ref(re_b, ty_b, _)) => {
                self.infer_from_region(*re_a, *re_b);
                self.infer_from_ty(ty_a, ty_b);
            }
            (BaseTy::Adt(_, args_a), ty::TyKind::Adt(_, args_b)) => {
                self.infer_from_generic_args(args_a, args_b);
            }
            (BaseTy::Dynamic(preds_a, re_a), ty::TyKind::Dynamic(preds_b, re_b)) => {
                debug_assert_eq!(preds_a.len(), preds_b.len());
                self.infer_from_region(*re_a, *re_b);
                for (pred_a, pred_b) in iter::zip(preds_a, preds_b) {
                    match (pred_a.as_ref().skip_binder(), pred_b.as_ref().skip_binder()) {
                        (
                            ExistentialPredicate::Trait(trait_ref_a),
                            ty::ExistentialPredicate::Trait(trait_ref_b),
                        ) => {
                            debug_assert_eq!(trait_ref_a.def_id, trait_ref_b.def_id);
                            self.infer_from_generic_args(&trait_ref_a.args, &trait_ref_b.args);
                        }
                        (
                            ExistentialPredicate::Projection(proj_a),
                            ty::ExistentialPredicate::Projection(proj_b),
                        ) => {
                            debug_assert_eq!(proj_a.def_id, proj_b.def_id);
                            self.infer_from_generic_args(&proj_a.args, &proj_b.args);
                            self.infer_from_ty(&proj_a.term, &proj_b.term);
                        }
                        _ => {}
                    }
                }
            }
            (BaseTy::Tuple(fields_a), ty::TyKind::Tuple(fields_b)) => {
                debug_assert_eq!(fields_a.len(), fields_b.len());
                for (ty_a, ty_b) in iter::zip(fields_a, fields_b) {
                    self.infer_from_ty(ty_a, ty_b);
                }
            }
            _ => {}
        }
    }

    fn infer_from_generic_args(&mut self, a: &GenericArgs, b: &rustc::ty::GenericArgs) {
        debug_assert_eq!(a.len(), b.len());
        for (arg_a, arg_b) in iter::zip(a, b) {
            self.infer_from_generic_arg(arg_a, arg_b);
        }
    }

    fn infer_from_generic_arg(&mut self, a: &GenericArg, b: &rustc::ty::GenericArg) {
        use rustc::ty;
        match (a, b) {
            (GenericArg::Base(ctor_a), ty::GenericArg::Ty(ty_b)) => {
                self.infer_from_bty(ctor_a.as_bty_skipping_binder(), ty_b);
            }
            (GenericArg::Ty(ty_a), ty::GenericArg::Ty(ty_b)) => {
                self.infer_from_ty(ty_a, ty_b);
            }
            (GenericArg::Lifetime(re_a), ty::GenericArg::Lifetime(re_b)) => {
                self.infer_from_region(*re_a, *re_b);
            }
            _ => {}
        }
    }

    fn infer_from_region(&mut self, a: Region, b: Region) {
        let ReVar(var) = a else { return };
        match self.map.entry(var) {
            hash_map::Entry::Occupied(entry) => {
                if entry.get() != &b {
                    bug!("ambiguous region substitution: {:?} -> [{:?}, {:?}]", a, entry.get(), b);
                }
            }
            hash_map::Entry::Vacant(entry) => {
                entry.insert(b);
            }
        }
    }
}

/// Substitution for late bound variables
pub(super) struct BoundVarReplacer<D> {
    current_index: DebruijnIndex,
    delegate: D,
}

pub trait BoundVarReplacerDelegate {
    fn replace_expr(&mut self, var: BoundReft) -> Expr;
    fn replace_region(&mut self, br: BoundRegion) -> Region;
}

pub(crate) struct FnMutDelegate<F1, F2> {
    pub exprs: F1,
    pub regions: F2,
}

impl<F1, F2> FnMutDelegate<F1, F2>
where
    F1: FnMut(BoundReft) -> Expr,
    F2: FnMut(BoundRegion) -> Region,
{
    pub(crate) fn new(exprs: F1, regions: F2) -> Self {
        Self { exprs, regions }
    }
}

impl<F1, F2> BoundVarReplacerDelegate for FnMutDelegate<F1, F2>
where
    F1: FnMut(BoundReft) -> Expr,
    F2: FnMut(BoundRegion) -> Region,
{
    fn replace_expr(&mut self, var: BoundReft) -> Expr {
        (self.exprs)(var)
    }

    fn replace_region(&mut self, br: BoundRegion) -> Region {
        (self.regions)(br)
    }
}

impl<D> BoundVarReplacer<D> {
    pub(super) fn new(delegate: D) -> BoundVarReplacer<D> {
        BoundVarReplacer { delegate, current_index: INNERMOST }
    }
}

impl<D> TypeFolder for BoundVarReplacer<D>
where
    D: BoundVarReplacerDelegate,
{
    fn fold_binder<T>(&mut self, t: &Binder<T>) -> Binder<T>
    where
        T: TypeFoldable,
    {
        self.current_index.shift_in(1);
        let r = t.super_fold_with(self);
        self.current_index.shift_out(1);
        r
    }

    fn fold_expr(&mut self, e: &Expr) -> Expr {
        if let ExprKind::Var(Var::Bound(debruijn, breft)) = e.kind() {
            match debruijn.cmp(&self.current_index) {
                Ordering::Less => Expr::bvar(*debruijn, breft.var, breft.kind),
                Ordering::Equal => {
                    self.delegate
                        .replace_expr(*breft)
                        .shift_in_escaping(self.current_index.as_u32())
                }
                Ordering::Greater => Expr::bvar(debruijn.shifted_out(1), breft.var, breft.kind),
            }
        } else {
            e.super_fold_with(self)
        }
    }

    fn fold_region(&mut self, re: &Region) -> Region {
        if let ReBound(debruijn, br) = *re {
            match debruijn.cmp(&self.current_index) {
                Ordering::Less => *re,
                Ordering::Equal => {
                    let region = self.delegate.replace_region(br);
                    if let ReBound(debruijn1, br) = region {
                        // If the callback returns a late-bound region,
                        // that region should always use the INNERMOST
                        // debruijn index. Then we adjust it to the
                        // correct depth.
                        assert_eq!(debruijn1, INNERMOST);
                        Region::ReBound(debruijn, br)
                    } else {
                        region
                    }
                }
                Ordering::Greater => ReBound(debruijn.shifted_out(1), br),
            }
        } else {
            *re
        }
    }
}

/// Substitution for [existential variables]
///
/// [existential variables]: crate::rty::Var::EVar
pub(super) struct EVarSubstFolder<'a> {
    evars: &'a EVarSol,
}

impl<'a> EVarSubstFolder<'a> {
    pub(super) fn new(evars: &'a EVarSol) -> Self {
        Self { evars }
    }
}

impl TypeFolder for EVarSubstFolder<'_> {
    fn fold_expr(&mut self, e: &Expr) -> Expr {
        if let ExprKind::Var(Var::EVar(evar)) = e.kind()
            && let Some(sol) = self.evars.get(*evar)
        {
            sol.clone()
        } else {
            e.super_fold_with(self)
        }
    }
}

/// Substitution for generics, i.e., early bound types, lifetimes, const generics, and refinements.
/// Note that a substitution for refinement parameters (a list of expressions) must always be
/// specified, while the behavior of other generics parameters (types, lifetimes and consts) can be
/// configured with [`GenericsSubstDelegate`].
pub(crate) struct GenericsSubstFolder<'a, D> {
    current_index: DebruijnIndex,
    delegate: D,
    refinement_args: &'a [Expr],
}

pub trait GenericsSubstDelegate {
    type Error = !;

    fn sort_for_param(&mut self, param_ty: ParamTy) -> Result<Sort, Self::Error>;
    fn ty_for_param(&mut self, param_ty: ParamTy) -> Ty;
    fn ctor_for_param(&mut self, param_ty: ParamTy) -> SubsetTyCtor;
    fn region_for_param(&mut self, ebr: EarlyParamRegion) -> Region;
    fn expr_for_param_const(&self, param_const: ParamConst) -> Expr;
    fn const_for_param(&mut self, param: &Const) -> Const;
}

/// The identity substitution used when checking the body of a (polymorphic) function. For example,
/// consider the function `fn foo<T>(){ .. }`
///
/// Outside of `foo`, `T` is bound (represented by the presence of `EarlyBinder`). Inside of the body
/// of `foo`, we treat `T` as a placeholder.
pub(crate) struct IdentitySubstDelegate;

impl GenericsSubstDelegate for IdentitySubstDelegate {
    fn sort_for_param(&mut self, param_ty: ParamTy) -> Result<Sort, !> {
        Ok(Sort::Param(param_ty))
    }

    fn ty_for_param(&mut self, param_ty: ParamTy) -> Ty {
        Ty::param(param_ty)
    }

    fn ctor_for_param(&mut self, param_ty: ParamTy) -> SubsetTyCtor {
        Binder::with_sort(
            SubsetTy::trivial(BaseTy::Param(param_ty), Expr::nu()),
            Sort::Param(param_ty),
        )
    }

    fn region_for_param(&mut self, ebr: EarlyParamRegion) -> Region {
        ReEarlyParam(ebr)
    }

    fn const_for_param(&mut self, param: &Const) -> Const {
        param.clone()
    }

    fn expr_for_param_const(&self, param_const: ParamConst) -> Expr {
        Expr::var(Var::ConstGeneric(param_const), None)
    }
}

/// A substitution with an explicit list of generic arguments.
pub(crate) struct GenericArgsDelegate<'a, 'tcx>(
    pub(crate) &'a [GenericArg],
    pub(crate) TyCtxt<'tcx>,
);

impl<'a, 'tcx> GenericsSubstDelegate for GenericArgsDelegate<'a, 'tcx> {
    fn sort_for_param(&mut self, param_ty: ParamTy) -> Result<Sort, !> {
        match self.0.get(param_ty.index as usize) {
            Some(GenericArg::Base(ctor)) => Ok(ctor.sort()),
            Some(arg) => {
                tracked_span_bug!("expected base type for generic parameter, found `{arg:?}`")
            }
            None => tracked_span_bug!("type parameter out of range {param_ty:?}"),
        }
    }

    fn ty_for_param(&mut self, param_ty: ParamTy) -> Ty {
        match self.0.get(param_ty.index as usize) {
            Some(GenericArg::Ty(ty)) => ty.clone(),
            Some(arg) => tracked_span_bug!("expected type for generic parameter, found `{arg:?}`"),
            None => tracked_span_bug!("type parameter out of range {param_ty:?}"),
        }
    }

    fn ctor_for_param(&mut self, param_ty: ParamTy) -> SubsetTyCtor {
        match self.0.get(param_ty.index as usize) {
            Some(GenericArg::Base(ctor)) => ctor.clone(),
            Some(arg) => {
                tracked_span_bug!("expected base type for generic parameter, found `{arg:?}`")
            }
            None => tracked_span_bug!("type parameter out of range"),
        }
    }

    fn region_for_param(&mut self, ebr: EarlyParamRegion) -> Region {
        match self.0.get(ebr.index as usize) {
            Some(GenericArg::Lifetime(re)) => *re,
            Some(arg) => bug!("expected region for generic parameter, found `{arg:?}`"),
            None => bug!("region parameter out of range"),
        }
    }

    fn const_for_param(&mut self, param: &Const) -> Const {
        if let ConstKind::Param(param_const) = &param.kind {
            match self.0.get(param_const.index as usize) {
                Some(GenericArg::Const(cst)) => cst.clone(),
                Some(arg) => bug!("expected const for generic parameter, found `{arg:?}`"),
                None => bug!("generic parameter out of range"),
            }
        } else {
            param.clone()
        }
    }

    fn expr_for_param_const(&self, param_const: ParamConst) -> Expr {
        match self.0.get(param_const.index as usize) {
            Some(GenericArg::Const(cst)) => Expr::from_const(self.1, cst),
            Some(arg) => bug!("expected const for generic parameter, found `{arg:?}`"),
            None => bug!("generic parameter out of range"),
        }
    }
}

/// A substitution meant to be used only for sorts. It'll panic if used on a type. This is used to
/// break cycles during wf checking. During wf-checking we use [`rty::Sort`], but we can't yet
/// generate (in general) an [`rty::GenericArg`] because conversion from [`fhir`] into [`rty`]
/// requires the results of wf checking. Perhaps, we could also solve this problem by doing
/// wf-checking with a different "IR" for sorts that sits in between [`fhir`] and [`rty`].
///
/// [`rty::Sort`]: crate::rty::Sort
/// [`rty::GenericArg`]: crate::rty::GenericArg
/// [`fhir`]: crate::fhir
/// [`rty`]: crate::rty
pub(crate) struct GenericsSubstForSort<F, E>
where
    F: FnMut(ParamTy) -> Result<Sort, E>,
{
    /// Implementation of [`GenericsSubstDelegate::sort_for_param`]
    pub(crate) sort_for_param: F,
}

impl<F, E> GenericsSubstDelegate for GenericsSubstForSort<F, E>
where
    F: FnMut(ParamTy) -> Result<Sort, E>,
{
    type Error = E;

    fn sort_for_param(&mut self, param_ty: ParamTy) -> Result<Sort, E> {
        (self.sort_for_param)(param_ty)
    }

    fn ty_for_param(&mut self, param_ty: ParamTy) -> Ty {
        bug!("unexpected type param {param_ty:?}");
    }

    fn ctor_for_param(&mut self, param_ty: ParamTy) -> SubsetTyCtor {
        bug!("unexpected base type param {param_ty:?}");
    }

    fn region_for_param(&mut self, ebr: EarlyParamRegion) -> Region {
        bug!("unexpected region param {ebr:?}");
    }

    fn const_for_param(&mut self, param: &Const) -> Const {
        bug!("unexpected const param {param:?}");
    }

    fn expr_for_param_const(&self, param_const: ParamConst) -> Expr {
        bug!("unexpected param_const {param_const:?}");
    }
}

#[derive(Debug, Clone, Default)]
pub struct ConstGenericArgs(FxHashMap<u32, Expr>);

impl ConstGenericArgs {
    pub fn empty() -> Self {
        Self(FxHashMap::default())
    }

    pub fn insert(&mut self, index: u32, expr: Expr) {
        self.0.insert(index, expr);
    }

    pub fn lookup(&self, index: u32) -> Expr {
        self.0.get(&index).unwrap().clone()
    }
}

impl<'a, D> GenericsSubstFolder<'a, D> {
    pub(crate) fn new(delegate: D, refine: &'a [Expr]) -> Self {
        Self { current_index: INNERMOST, delegate, refinement_args: refine }
    }
}

impl<D: GenericsSubstDelegate> FallibleTypeFolder for GenericsSubstFolder<'_, D> {
    type Error = D::Error;

    fn try_fold_binder<T: TypeFoldable>(&mut self, t: &Binder<T>) -> Result<Binder<T>, D::Error> {
        self.current_index.shift_in(1);
        let r = t.try_super_fold_with(self)?;
        self.current_index.shift_out(1);
        Ok(r)
    }

    fn try_fold_sort(&mut self, sort: &Sort) -> Result<Sort, D::Error> {
        if let Sort::Param(param_ty) = sort {
            self.delegate.sort_for_param(*param_ty)
        } else {
            sort.try_super_fold_with(self)
        }
    }

    fn try_fold_ty(&mut self, ty: &Ty) -> Result<Ty, D::Error> {
        match ty.kind() {
            TyKind::Param(param_ty) => Ok(self.delegate.ty_for_param(*param_ty)),
            TyKind::Indexed(BaseTy::Param(param_ty), idx) => {
                let idx = idx.try_fold_with(self)?;
                Ok(self
                    .delegate
                    .ctor_for_param(*param_ty)
                    .replace_bound_reft(&idx)
                    .to_ty())
            }
            _ => ty.try_super_fold_with(self),
        }
    }

    fn try_fold_subset_ty(&mut self, sty: &SubsetTy) -> Result<SubsetTy, D::Error> {
        if let BaseTy::Param(param_ty) = &sty.bty {
            Ok(self
                .delegate
                .ctor_for_param(*param_ty)
                .replace_bound_reft(&sty.idx)
                .strengthen(&sty.pred))
        } else {
            sty.try_super_fold_with(self)
        }
    }

    fn try_fold_region(&mut self, re: &Region) -> Result<Region, D::Error> {
        if let ReEarlyParam(ebr) = *re {
            Ok(self.delegate.region_for_param(ebr))
        } else {
            Ok(*re)
        }
    }

    fn try_fold_expr(&mut self, expr: &Expr) -> Result<Expr, D::Error> {
        match expr.kind() {
            ExprKind::Var(Var::EarlyParam(var)) => Ok(self.expr_for_param(var.index)),
            ExprKind::Var(Var::ConstGeneric(param_const)) => {
                Ok(self.delegate.expr_for_param_const(*param_const))
            }
            _ => expr.try_super_fold_with(self),
        }
    }

    fn try_fold_const(&mut self, c: &Const) -> Result<Const, D::Error> {
        Ok(self.delegate.const_for_param(c))
    }
}

impl<D> GenericsSubstFolder<'_, D> {
    fn expr_for_param(&self, idx: u32) -> Expr {
        self.refinement_args[idx as usize].shift_in_escaping(self.current_index.as_u32())
    }
}

pub(crate) struct SortSubst<D> {
    delegate: D,
}

impl<D> SortSubst<D> {
    pub(crate) fn new(delegate: D) -> Self {
        Self { delegate }
    }
}

impl<D: SortSubstDelegate> TypeFolder for SortSubst<D> {
    fn fold_sort(&mut self, sort: &Sort) -> Sort {
        match sort {
            Sort::Var(var) => self.delegate.sort_for_param(*var),
            Sort::BitVec(BvSize::Param(var)) => Sort::BitVec(self.delegate.bv_size_for_param(*var)),
            _ => sort.super_fold_with(self),
        }
    }
}

trait SortSubstDelegate {
    fn sort_for_param(&self, var: ParamSort) -> Sort;
    fn bv_size_for_param(&self, var: ParamSort) -> BvSize;
}

impl SortSubstDelegate for &[SortArg] {
    fn sort_for_param(&self, var: ParamSort) -> Sort {
        match &self[var.index] {
            SortArg::Sort(sort) => sort.clone(),
            SortArg::BvSize(_) => tracked_span_bug!("unexpected bv size for sort param"),
        }
    }

    fn bv_size_for_param(&self, var: ParamSort) -> BvSize {
        match self[var.index] {
            SortArg::BvSize(size) => size,
            SortArg::Sort(_) => tracked_span_bug!("unexpected sort for bv size param"),
        }
    }
}

impl SortSubstDelegate for &[Sort] {
    fn sort_for_param(&self, var: ParamSort) -> Sort {
        self[var.index].clone()
    }

    fn bv_size_for_param(&self, _var: ParamSort) -> BvSize {
        tracked_span_bug!("unexpected bv size parameter")
    }
}
