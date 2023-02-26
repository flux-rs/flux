use std::{cell::RefCell, collections::hash_map, string::ToString};

use flux_common::{bug, dbg};
use flux_config as config;
use flux_errors::{ErrorGuaranteed, FluxSession};
use itertools::Itertools;
use rustc_errors::FatalError;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{def::DefKind, def_id::DefId, LangItem};
use rustc_middle::ty::{TyCtxt, Variance};
pub use rustc_span::{symbol::Ident, Symbol};

pub use crate::rustc::lowering::UnsupportedFnSig;
use crate::{
    early_ctxt::EarlyCtxt,
    fhir::{self, VariantIdx},
    rty::{self, fold::TypeFoldable, normalize::Defns, refining, Binder},
    rustc,
};

#[derive(Debug)]
pub struct OpaqueStructErr(pub DefId);

type VariantMap = FxHashMap<DefId, rty::Opaqueness<Vec<rty::PolyVariant>>>;
type FnSigMap = FxHashMap<DefId, rty::PolySig>;

pub struct GlobalEnv<'sess, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub sess: &'sess FluxSession,
    generics: RefCell<FxHashMap<DefId, rty::Generics>>,
    qualifiers: Vec<rty::Qualifier>,
    uifs: FxHashMap<Symbol, rty::UifDef>,
    fn_sigs: RefCell<FxHashMap<DefId, rty::PolySig>>,
    /// Names of 'local' qualifiers to be used when checking a given `DefId`.
    fn_quals: FxHashMap<DefId, FxHashSet<String>>,
    early_cx: EarlyCtxt<'sess, 'tcx>,
    adt_defs: RefCell<FxHashMap<DefId, rty::AdtDef>>,
    adt_variants: RefCell<VariantMap>,
    defns: Defns,
}

impl<'sess, 'tcx> GlobalEnv<'sess, 'tcx> {
    pub fn new(early_cx: EarlyCtxt<'sess, 'tcx>) -> Result<Self, ErrorGuaranteed> {
        let mut defns: FxHashMap<Symbol, rty::Defn> = FxHashMap::default();
        for defn in early_cx.map.defns() {
            let defn = rty::conv::conv_defn(&early_cx, defn);
            defns.insert(defn.name, defn);
        }
        let defns = Defns::new(defns).map_err(|cycle| {
            let span = early_cx.map.defn(cycle[0]).unwrap().expr.span;
            early_cx
                .sess
                .emit_err(errors::DefinitionCycle::new(span, cycle))
        })?;

        let adt_defs = mk_adt_defs(&early_cx);

        let qualifiers = early_cx
            .map
            .qualifiers()
            .map(|qualifier| rty::conv::conv_qualifier(&early_cx, qualifier).normalize(&defns))
            .collect();

        let uifs = early_cx
            .map
            .uifs()
            .map(|uif| (uif.name, rty::conv::conv_uif(&early_cx, uif)))
            .collect();

        let mut fn_quals = FxHashMap::default();
        for (def_id, names) in early_cx.map.fn_quals() {
            let names = names.iter().map(|ident| ident.name.to_string()).collect();
            fn_quals.insert(def_id.to_def_id(), names);
        }
        let mut genv = GlobalEnv {
            generics: RefCell::new(FxHashMap::default()),
            fn_sigs: RefCell::new(FnSigMap::default()),
            adt_defs: RefCell::new(adt_defs),
            adt_variants: RefCell::new(VariantMap::default()),
            qualifiers,
            tcx: early_cx.tcx,
            sess: early_cx.sess,
            early_cx,
            uifs,
            defns,
            fn_quals,
        };
        genv.register_generics();
        genv.register_struct_def_variants();
        genv.register_enum_def_variants();
        genv.register_fn_sigs();

        Ok(genv)
    }

    fn register_generics(&mut self) {
        for (def_id, generics) in self.early_cx.map.generics() {
            let rust_generics = rustc::lowering::lower_generics(
                self.tcx,
                self.sess,
                self.tcx.generics_of(def_id.to_def_id()),
            )
            .unwrap_or_else(|_| FatalError.raise());
            self.generics
                .get_mut()
                .insert(def_id.to_def_id(), rty::conv::conv_generics(&rust_generics, generics));
        }
    }

    fn register_struct_def_variants(&mut self) {
        let map = &self.early_cx.map;
        for struct_def in map.structs() {
            let def_id = struct_def.def_id;
            let variants = rty::conv::ConvCtxt::conv_struct_def_variant(self, struct_def)
                .map(|v| vec![v.normalize(&self.defns)]);
            if config::dump_fhir() {
                dbg::dump_item_info(self.tcx, def_id, "rty", &variants).unwrap();
            }

            self.adt_variants
                .get_mut()
                .insert(def_id.to_def_id(), variants);
        }
    }

    fn register_enum_def_variants(&mut self) {
        let map = &self.early_cx.map;
        for enum_def in map.enums() {
            let def_id = enum_def.def_id;
            let variants = rty::conv::ConvCtxt::conv_enum_def_variants(self, enum_def)
                .into_iter()
                .map(|variant| variant.normalize(&self.defns))
                .collect_vec();
            self.adt_variants
                .get_mut()
                .insert(def_id.to_def_id(), rty::Opaqueness::Transparent(variants));
        }
    }

    fn register_fn_sigs(&mut self) {
        let map = &self.early_cx.map;
        for (def_id, fn_sig) in map.fn_sigs() {
            let fn_sig = rty::conv::conv_fn_sig(self, fn_sig).normalize(&self.defns);
            if config::dump_rty() {
                dbg::dump_item_info(self.tcx, def_id, "rty", &fn_sig).unwrap();
            }
            self.fn_sigs.get_mut().insert(def_id.to_def_id(), fn_sig);
        }
    }

    pub fn map(&self) -> &fhir::Map {
        &self.early_cx.map
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
                    refining::refine_fn_sig(self, &self.generics_of(def_id), &fn_sig, rty::Expr::tt)
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
    ) -> Result<rty::PolyVariant, OpaqueStructErr> {
        Ok(self
            .adt_variants
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
                                refining::refine_variant_def(self, def_id, &variant_def)
                            })
                            .collect(),
                    )
                }
            })
            .as_ref()
            .ok_or(OpaqueStructErr(def_id))?[variant_idx.as_usize()]
        .clone())
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

    pub fn refine_with_true(&self, generics: &rty::Generics, rustc_ty: &rustc::ty::Ty) -> rty::Ty {
        refining::refine_ty(self, generics, rustc_ty, rty::Expr::tt)
    }

    pub fn refine_with_holes(&self, generics: &rty::Generics, rustc_ty: &rustc::ty::Ty) -> rty::Ty {
        refining::refine_ty(self, generics, rustc_ty, rty::Expr::hole)
    }

    pub fn instantiate_generic_arg(
        &self,
        generics: &rty::Generics,
        param: &rty::GenericParamDef,
        arg: &rustc::ty::GenericArg,
    ) -> rty::GenericArg {
        refining::refine_generic_arg(self, generics, param, arg, rty::Expr::hole)
    }

    pub fn type_of(&self, def_id: DefId) -> Binder<rty::Ty> {
        if let Some(local_id) = def_id.as_local() {
            match self.tcx.def_kind(def_id) {
                DefKind::TyAlias => {
                    let alias = self.early_cx.map.get_type_alias(local_id);
                    rty::conv::expand_type_alias(self, alias)
                }
                DefKind::TyParam => {
                    match &self.early_cx.get_generic_param(local_id).kind {
                        fhir::GenericParamDefKind::Type { default: Some(ty) } => {
                            rty::conv::conv_ty(self, ty)
                        }
                        _ => bug!("non-type def"),
                    }
                }
                kind => {
                    bug!("`{:?}` not supported", kind.descr(def_id))
                }
            }
        } else {
            self.early_cx
                .cstore
                .type_of(def_id)
                .cloned()
                .unwrap_or_else(|| {
                    let rustc_ty = self.lower_type_of(def_id);
                    let ty = self.refine_with_true(&self.generics_of(def_id), &rustc_ty);
                    Binder::new(ty, rty::Sort::unit())
                })
        }
    }

    pub(crate) fn lower_type_of(&self, def_id: DefId) -> rustc::ty::Ty {
        rustc::lowering::lower_type_of(self.tcx, self.sess, def_id)
            .unwrap_or_else(|_| FatalError.raise())
    }

    pub(crate) fn early_cx(&self) -> &EarlyCtxt<'sess, 'tcx> {
        &self.early_cx
    }

    pub fn hir(&self) -> rustc_middle::hir::map::Map<'tcx> {
        self.tcx.hir()
    }
}

fn mk_adt_defs(early_cx: &EarlyCtxt) -> FxHashMap<DefId, rty::AdtDef> {
    let mut map = FxHashMap::default();
    for struct_def in early_cx.map.structs() {
        map.insert(
            struct_def.def_id.to_def_id(),
            rty::conv::adt_def_for_struct(early_cx, struct_def),
        );
    }
    for enum_def in early_cx.map.enums() {
        map.insert(enum_def.def_id.to_def_id(), rty::conv::adt_def_for_enum(early_cx, enum_def));
    }

    map
}

mod errors {
    use flux_macros::Diagnostic;
    use rustc_span::{Span, Symbol};

    #[derive(Diagnostic)]
    #[diag(wf::definition_cycle, code = "FLUX")]
    pub struct DefinitionCycle {
        #[primary_span]
        #[label]
        span: Span,
        msg: String,
    }

    impl DefinitionCycle {
        pub(super) fn new(span: Span, cycle: Vec<Symbol>) -> Self {
            let root = format!("`{}`", cycle[0]);
            let names: Vec<String> = cycle.iter().map(|s| format!("`{s}`")).collect();
            let msg = format!("{} -> {}", names.join(" -> "), root);
            Self { span, msg }
        }
    }
}
