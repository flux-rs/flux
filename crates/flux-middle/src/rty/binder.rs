use std::slice;

pub use flux_arc_interner::{List, impl_slice_internable};
use flux_common::tracked_span_bug;
use flux_macros::{TypeFoldable, TypeVisitable};
use flux_rustc_bridge::{
    ToRustc,
    ty::{BoundRegion, Region},
};
use itertools::Itertools;
use rustc_data_structures::unord::UnordMap;
use rustc_macros::{Decodable, Encodable, TyDecodable, TyEncodable};
use rustc_middle::ty::{BoundRegionKind, TyCtxt};
use rustc_span::{Span, Symbol};

use super::{
    Expr, GenericArg, InferMode, RefineParam, Sort,
    fold::TypeFoldable,
    subst::{self, BoundVarReplacer, FnMutDelegate},
};

#[derive(Clone, Debug, TyEncodable, TyDecodable)]
pub struct EarlyBinder<T>(pub T);

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

    pub fn try_map<U, E>(self, f: impl FnOnce(T) -> Result<U, E>) -> Result<EarlyBinder<U>, E> {
        Ok(EarlyBinder(f(self.0)?))
    }

    pub fn skip_binder(self) -> T {
        self.0
    }

    pub fn skip_binder_ref(&self) -> &T {
        &self.0
    }

    pub fn instantiate_identity(self) -> T {
        self.0
    }
}

impl<I: IntoIterator> EarlyBinder<I> {
    pub fn iter_identity(self) -> impl Iterator<Item = I::Item> {
        self.0.into_iter()
    }
}

impl<T: TypeFoldable> EarlyBinder<T> {
    pub fn instantiate(self, tcx: TyCtxt, args: &[GenericArg], refine_args: &[Expr]) -> T {
        self.as_ref().instantiate_ref(tcx, args, refine_args)
    }
}

impl<T: TypeFoldable> EarlyBinder<&T> {
    pub fn instantiate_ref(self, tcx: TyCtxt, args: &[GenericArg], refine_args: &[Expr]) -> T {
        self.0
            .try_fold_with(&mut subst::GenericsSubstFolder::new(
                subst::GenericArgsDelegate(args, tcx),
                refine_args,
            ))
            .into_ok()
    }
}

impl EarlyBinder<RefineParam> {
    pub fn name(&self) -> Symbol {
        self.skip_binder_ref().name
    }
}

#[derive(Clone, Eq, PartialEq, Hash, TyEncodable, TyDecodable)]
pub struct Binder<T> {
    vars: List<BoundVariableKind>,
    value: T,
}

impl<T> Binder<T> {
    pub fn bind_with_vars(value: T, vars: BoundVariableKinds) -> Binder<T> {
        Binder { vars, value }
    }

    pub fn dummy(value: T) -> Binder<T> {
        Binder::bind_with_vars(value, List::empty())
    }

    pub fn bind_with_sorts(value: T, sorts: &[Sort]) -> Binder<T> {
        Binder::bind_with_vars(value, sorts.iter().cloned().map_into().collect())
    }

    pub fn bind_with_sort(value: T, sort: Sort) -> Binder<T> {
        Binder::bind_with_sorts(value, &[sort])
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

    pub fn skip_binder_ref(&self) -> &T {
        self.as_ref().skip_binder()
    }

    pub fn rebind<U>(&self, value: U) -> Binder<U> {
        Binder { vars: self.vars.clone(), value }
    }

    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Binder<U> {
        Binder { vars: self.vars, value: f(self.value) }
    }

    pub fn map_ref<U>(&self, f: impl FnOnce(&T) -> U) -> Binder<U> {
        Binder { vars: self.vars.clone(), value: f(&self.value) }
    }

    pub fn try_map<U, E>(self, f: impl FnOnce(T) -> Result<U, E>) -> Result<Binder<U>, E> {
        Ok(Binder { vars: self.vars, value: f(self.value)? })
    }

    #[track_caller]
    pub fn sort(&self) -> Sort {
        match &self.vars[..] {
            [BoundVariableKind::Refine(sort, ..)] => sort.clone(),
            _ => tracked_span_bug!("expected single-sorted binder"),
        }
    }

    pub fn sorts(&self) -> List<Sort> {
        self.vars
            .iter()
            .map(|kind| {
                let BoundVariableKind::Refine(sort, ..) = kind else {
                    tracked_span_bug!("unexpected BoundVariable");
                };
                sort.clone()
            })
            .collect()
    }
}

impl<T> Binder<T>
where
    T: TypeFoldable,
{
    pub fn replace_bound_vars(
        &self,
        mut replace_region: impl FnMut(BoundRegion) -> Region,
        mut replace_expr: impl FnMut(&Sort, InferMode, BoundReftKind) -> Expr,
    ) -> T {
        let mut exprs = UnordMap::default();
        let mut regions = UnordMap::default();
        let delegate = FnMutDelegate::new(
            |breft| {
                exprs
                    .entry(breft.var)
                    .or_insert_with(|| {
                        let (sort, mode, kind) = self.vars[breft.var.as_usize()].expect_refine();
                        replace_expr(sort, mode, kind)
                    })
                    .clone()
            },
            |br| *regions.entry(br.var).or_insert_with(|| replace_region(br)),
        );

        self.value.fold_with(&mut BoundVarReplacer::new(delegate))
    }

    pub fn replace_bound_refts(&self, exprs: &[Expr]) -> T {
        let delegate = FnMutDelegate::new(
            |breft| exprs[breft.var.as_usize()].clone(),
            |br| tracked_span_bug!("unexpected escaping region {br:?}"),
        );
        self.value.fold_with(&mut BoundVarReplacer::new(delegate))
    }

    pub fn replace_bound_reft(&self, expr: &Expr) -> T {
        debug_assert!(matches!(&self.vars[..], [BoundVariableKind::Refine(..)]));
        self.replace_bound_refts(slice::from_ref(expr))
    }

    pub fn replace_bound_refts_with(
        &self,
        mut f: impl FnMut(&Sort, InferMode, BoundReftKind) -> Expr,
    ) -> T {
        let exprs = self
            .vars
            .iter()
            .map(|param| {
                let (sort, mode, kind) = param.expect_refine();
                f(sort, mode, kind)
            })
            .collect_vec();
        self.replace_bound_refts(&exprs)
    }
}

impl<'tcx, V> ToRustc<'tcx> for Binder<V>
where
    V: ToRustc<'tcx, T: rustc_middle::ty::TypeVisitable<TyCtxt<'tcx>>>,
{
    type T = rustc_middle::ty::Binder<'tcx, V::T>;

    fn to_rustc(&self, tcx: TyCtxt<'tcx>) -> Self::T {
        let vars = BoundVariableKind::to_rustc(&self.vars, tcx);
        let value = self.value.to_rustc(tcx);
        rustc_middle::ty::Binder::bind_with_vars(value, vars)
    }
}

#[derive(
    Clone, PartialEq, Eq, Hash, Debug, TyEncodable, TyDecodable, TypeVisitable, TypeFoldable,
)]
pub enum BoundVariableKind {
    Region(BoundRegionKind),
    Refine(Sort, InferMode, BoundReftKind),
}

impl BoundVariableKind {
    fn expect_refine(&self) -> (&Sort, InferMode, BoundReftKind) {
        if let BoundVariableKind::Refine(sort, mode, kind) = self {
            (sort, *mode, *kind)
        } else {
            tracked_span_bug!("expected `BoundVariableKind::Refine`")
        }
    }

    pub fn expect_sort(&self) -> &Sort {
        self.expect_refine().0
    }

    pub fn expect_bound_reft_kind(&self) -> BoundReftKind {
        self.expect_refine().2
    }

    /// Returns `true` if the bound variable kind is [`Refine`].
    ///
    /// [`Refine`]: BoundVariableKind::Refine
    #[must_use]
    pub fn is_refine(&self) -> bool {
        matches!(self, Self::Refine(..))
    }

    // We can't implement [`ToRustc`] on [`List<BoundVariableKind>`] because of coherence so we add
    // it here
    fn to_rustc<'tcx>(
        vars: &[Self],
        tcx: TyCtxt<'tcx>,
    ) -> &'tcx rustc_middle::ty::List<rustc_middle::ty::BoundVariableKind> {
        tcx.mk_bound_variable_kinds_from_iter(vars.iter().flat_map(|kind| {
            match kind {
                BoundVariableKind::Region(brk) => {
                    Some(rustc_middle::ty::BoundVariableKind::Region(*brk))
                }
                BoundVariableKind::Refine(..) => None,
            }
        }))
    }
}

impl From<Sort> for BoundVariableKind {
    fn from(sort: Sort) -> Self {
        Self::Refine(sort, InferMode::EVar, BoundReftKind::Anon)
    }
}

pub type BoundVariableKinds = List<BoundVariableKind>;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord, Encodable, Decodable)]
pub enum BoundReftKind {
    Anon,
    Named(Symbol),
}

impl_slice_internable!(BoundVariableKind);

// --------------------------------------------------------------------------------------------------

#[derive(Clone, Debug)]
pub struct BinderProvenance {
    /// Whence?
    pub span: Option<Span>,
    /// Why?
    pub originator: BinderOriginator,
}

impl BinderProvenance {
    pub fn unknown() -> Self {
        BinderProvenance { span: None, originator: BinderOriginator::Unknown }
    }

    pub fn bound_reft_kind(kind: BoundReftKind) -> Self {
        BinderProvenance { span: None, originator: BinderOriginator::UnfoldBoundReft(kind) }
    }

    pub fn new(originator: BinderOriginator) -> Self {
        BinderProvenance { span: None, originator }
    }

    pub fn with_span(self, span: Span) -> Self {
        BinderProvenance { span: Some(span), originator: self.originator }
    }

    pub fn opt_symbol(&self) -> Option<Symbol> {
        match &self.originator {
            BinderOriginator::FnArg(Some(name)) => Some(*name),
            BinderOriginator::UnfoldBoundReft(BoundReftKind::Named(name)) => Some(*name),
            _ => None,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum BinderOriginator {
    /// Unknown origin
    Unknown,
    /// Unfolded BoundReft
    UnfoldBoundReft(BoundReftKind),
    /// Argument from the definition of a function
    FnArg(Option<Symbol>),
    // /// Subtyping check
    // Sub(ConstrReason),
    // /// Function subtyping check
    // FnSub,
    // /// Function call
    // Call,
    // // /// The return of a function call
    // // CallReturn(CallReturn),
    // /// Unfold a local pointer
    // UnfoldPtr,
    // /// Unfold a strong ref
    // UnfoldStrgRef,
    // /// Assume an ensures
    // AssumeEnsures,
    // /// Check an invariant
    // CheckInvariant,
    // /// For use applying the mut ref hack
    // MutRefHack,
    // /// Subtyping projection types
    // /// (NOTE: not differentiating between generic arg tys)
    // SubProjTy,
    // SubtypeProjTy,
    // SubtypeProjBase,
}
