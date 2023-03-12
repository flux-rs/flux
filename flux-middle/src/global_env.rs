use std::{cell::RefCell, collections::hash_map, string::ToString};

use flux_errors::FluxSession;
use rustc_errors::FatalError;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    def_id::{DefId, LocalDefId},
    LangItem,
};
use rustc_middle::ty::{TyCtxt, Variance};
pub use rustc_span::{symbol::Ident, Symbol};

pub use crate::rustc::lowering::UnsupportedFnSig;
use crate::{
    early_ctxt::EarlyCtxt,
    fhir::{self, VariantIdx},
    rty::{
        self,
        normalize::Defns,
        refining::{self, Refiner},
        Binder,
    },
    rustc,
};

type VariantMap = FxHashMap<DefId, rty::Opaqueness<Vec<rty::PolyVariant>>>;
type FnSigMap = FxHashMap<DefId, rty::PolySig>;

pub struct Queries {
    pub type_of: fn(&GlobalEnv, LocalDefId) -> rty::Binder<rty::Ty>,
}

pub struct GlobalEnv<'sess, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub sess: &'sess FluxSession,
    generics: RefCell<FxHashMap<DefId, rty::Generics>>,
    predicates: RefCell<FxHashMap<DefId, rty::GenericPredicates>>,
    qualifiers: Vec<rty::Qualifier>,
    uifs: FxHashMap<Symbol, rty::UifDef>,
    fn_sigs: RefCell<FxHashMap<DefId, rty::PolySig>>,
    /// Names of 'local' qualifiers to be used when checking a given `DefId`.
    fn_quals: FxHashMap<DefId, FxHashSet<String>>,
    early_cx: EarlyCtxt<'sess, 'tcx>,
    adt_defs: RefCell<FxHashMap<DefId, rty::AdtDef>>,
    adt_variants: RefCell<VariantMap>,
    defns: Defns,
    queries: Queries,
}

impl<'sess, 'tcx> GlobalEnv<'sess, 'tcx> {
    pub fn new(
        early_cx: EarlyCtxt<'sess, 'tcx>,
        adt_defs: FxHashMap<DefId, rty::AdtDef>,
        defns: Defns,
        qualifiers: Vec<rty::Qualifier>,
        uifs: FxHashMap<Symbol, rty::UifDef>,
        queries: Queries,
    ) -> Self {
        let mut fn_quals = FxHashMap::default();
        for (def_id, names) in early_cx.map.fn_quals() {
            let names = names.iter().map(|ident| ident.name.to_string()).collect();
            fn_quals.insert(def_id.to_def_id(), names);
        }
        GlobalEnv {
            generics: RefCell::new(FxHashMap::default()),
            predicates: RefCell::new(FxHashMap::default()),
            fn_sigs: RefCell::new(FnSigMap::default()),
            adt_defs: RefCell::new(adt_defs),
            adt_variants: RefCell::new(VariantMap::default()),
            qualifiers,
            tcx: early_cx.tcx,
            sess: early_cx.sess,
            early_cx,
            uifs,
            fn_quals,
            defns,
            queries,
        }
    }

    pub fn register_generics(
        &mut self,
        generics: impl IntoIterator<Item = (DefId, rty::Generics)>,
    ) {
        self.generics.get_mut().extend(generics);
    }

    pub fn register_variants(
        &mut self,
        variants: impl IntoIterator<Item = (DefId, rty::Opaqueness<Vec<rty::PolyVariant>>)>,
    ) {
        self.adt_variants.get_mut().extend(variants);
    }

    pub fn register_fn_sigs(&mut self, fn_sigs: impl IntoIterator<Item = (DefId, rty::PolySig)>) {
        self.fn_sigs.get_mut().extend(fn_sigs);
    }

    pub fn map(&self) -> &fhir::Map {
        &self.early_cx.map
    }

    pub fn defns(&self) -> &Defns {
        &self.defns
    }

    fn fn_quals(&self, did: DefId) -> Vec<String> {
        match self.fn_quals.get(&did) {
            None => vec![],
            Some(names) => names.iter().map(ToString::to_string).collect(),
        }
    }

    pub fn qualifiers(&self, did: DefId) -> impl Iterator<Item = &rty::Qualifier> {
        let names = self.fn_quals(did);
        self.qualifiers
            .iter()
            .filter(move |qualifier| qualifier.global || names.contains(&qualifier.name))
    }

    pub fn uifs(&self) -> impl Iterator<Item = &rty::UifDef> {
        self.uifs.values()
    }

    pub fn lookup_fn_sig(&self, def_id: DefId) -> Result<rty::PolySig, UnsupportedFnSig> {
        match self.fn_sigs.borrow_mut().entry(def_id) {
            hash_map::Entry::Occupied(entry) => Ok(entry.get().clone()),
            hash_map::Entry::Vacant(entry) => {
                let fn_sig = if let Some(fn_sig) = self.early_cx.cstore.fn_sig(def_id) {
                    fn_sig
                } else {
                    let fn_sig = rustc::lowering::lower_fn_sig_of(self.tcx, def_id)?.skip_binder();
                    Refiner::default(self, &self.generics_of(def_id)).refine_fn_sig(&fn_sig)
                };
                Ok(entry.insert(fn_sig).clone())
            }
        }
    }

    pub fn variances_of(&self, did: DefId) -> &[Variance] {
        self.tcx.variances_of(did)
    }

    pub fn adt_def(&self, def_id: impl Into<DefId>) -> rty::AdtDef {
        let def_id = def_id.into();
        self.adt_defs
            .borrow_mut()
            .entry(def_id)
            .or_insert_with(|| {
                if let Some(adt_def) = self.early_cx.cstore.adt_def(def_id) {
                    adt_def.clone()
                } else {
                    rty::AdtDef::new(self.tcx.adt_def(def_id), rty::Sort::unit(), vec![], false)
                }
            })
            .clone()
    }

    pub fn mk_box(&self, ty: rty::Ty, alloc: rty::Ty) -> rty::Ty {
        let def_id = self.tcx.require_lang_item(LangItem::OwnedBox, None);
        let adt_def = self.adt_def(def_id);

        // this is harcoding that `Box` has two type parameters and
        // it is indexed by unit. We leave this as a reminder in case
        // that ever changes.
        debug_assert_eq!(self.generics_of(def_id).params.len(), 2);
        debug_assert!(adt_def.sort().is_unit());

        let bty =
            rty::BaseTy::adt(adt_def, vec![rty::GenericArg::Ty(ty), rty::GenericArg::Ty(alloc)]);
        rty::Ty::indexed(bty, rty::Index::unit())
    }

    pub fn variant(
        &self,
        def_id: DefId,
        variant_idx: VariantIdx,
    ) -> rty::Opaqueness<rty::PolyVariant> {
        self.adt_variants
            .borrow_mut()
            .entry(def_id)
            .or_insert_with(|| {
                if let Some(variants) = self.early_cx.cstore.variants(def_id) {
                    variants.map(<[_]>::to_vec)
                } else {
                    rty::Opaqueness::Transparent(
                        self.tcx
                            .adt_def(def_id)
                            .variants()
                            .iter()
                            .map(|variant_def| {
                                let variant_def = rustc::lowering::lower_variant_def(
                                    self.tcx,
                                    self.sess,
                                    def_id,
                                    variant_def,
                                )
                                .unwrap_or_else(|_| FatalError.raise());
                                Refiner::default(self, &self.generics_of(def_id))
                                    .refine_variant_def(&variant_def)
                            })
                            .collect(),
                    )
                }
            })
            .as_ref()
            .map(|variants| variants[variant_idx.as_usize()].clone())
    }

    pub fn predicates_of(&self, def_id: DefId) -> rty::GenericPredicates {
        self.predicates
            .borrow_mut()
            .entry(def_id)
            .or_insert_with(|| {
                let predicates = self.tcx.predicates_of(def_id);
                let predicates =
                    rustc::lowering::lower_generic_predicates(self.tcx, self.sess, predicates)
                        .unwrap_or_else(|_| FatalError.raise());

                Refiner::default(self, &self.generics_of(def_id))
                    .refine_generic_predicates(&predicates)
            })
            .clone()
    }

    pub fn generics_of(&self, def_id: impl Into<DefId>) -> rty::Generics {
        let def_id = def_id.into();
        self.generics
            .borrow_mut()
            .entry(def_id)
            .or_insert_with(|| {
                let generics = rustc::lowering::lower_generics(
                    self.tcx,
                    self.sess,
                    self.tcx.generics_of(def_id),
                )
                .unwrap_or_else(|_| FatalError.raise());
                refining::refine_generics(&generics)
            })
            .clone()
    }

    pub fn index_sorts_of(&self, def_id: DefId) -> &[fhir::Sort] {
        self.early_cx.index_sorts_of(def_id)
    }

    pub fn early_bound_sorts_of(&self, def_id: DefId) -> &[fhir::Sort] {
        self.early_cx.early_bound_sorts_of(def_id)
    }

    pub fn refine_default(&self, generics: &rty::Generics, rustc_ty: &rustc::ty::Ty) -> rty::Ty {
        Refiner::default(self, generics).refine_ty(rustc_ty)
    }

    pub fn refine_with_holes(&self, generics: &rty::Generics, rustc_ty: &rustc::ty::Ty) -> rty::Ty {
        Refiner::with_holes(self, generics).refine_ty(rustc_ty)
    }

    pub fn instantiate_arg_for_fun(
        &self,
        generics: &rty::Generics,
        param: &rty::GenericParamDef,
        arg: &rustc::ty::GenericArg,
    ) -> rty::GenericArg {
        Refiner::new(self, generics, |bty| {
            let sort = bty.sort();
            let mut ty = rty::Ty::indexed(bty, rty::Expr::nu());
            if !sort.is_unit() {
                ty = rty::Ty::constr(rty::Expr::hole(), ty);
            }
            rty::Binder::new(ty, sort)
        })
        .refine_generic_arg(param, arg)
    }

    pub fn instantiate_arg_for_constructor(
        &self,
        generics: &rty::Generics,
        param: &rty::GenericParamDef,
        arg: &rustc::ty::GenericArg,
    ) -> rty::GenericArg {
        Refiner::with_holes(self, generics).refine_generic_arg(param, arg)
    }

    pub fn type_of(&self, def_id: DefId) -> Binder<rty::Ty> {
        if let Some(local_id) = def_id.as_local() {
            (self.queries.type_of)(self, local_id)
        } else {
            self.early_cx
                .cstore
                .type_of(def_id)
                .cloned()
                .unwrap_or_else(|| {
                    let rustc_ty = self.lower_type_of(def_id);
                    let ty = self.refine_default(&self.generics_of(def_id), &rustc_ty);
                    Binder::new(ty, rty::Sort::unit())
                })
        }
    }

    pub(crate) fn lower_type_of(&self, def_id: DefId) -> rustc::ty::Ty {
        rustc::lowering::lower_type_of(self.tcx, self.sess, def_id)
            .unwrap_or_else(|_| FatalError.raise())
    }

    pub fn early_cx(&self) -> &EarlyCtxt<'sess, 'tcx> {
        &self.early_cx
    }

    pub fn hir(&self) -> rustc_middle::hir::map::Map<'tcx> {
        self.tcx.hir()
    }
}
