use std::{cell::RefCell, collections::hash_map, iter, string::ToString};

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
    rty::{self, fold::TypeFoldable, normalize::Defns, Binder},
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
                    self.default_fn_sig(def_id)?
                };
                Ok(entry.insert(fn_sig).clone())
            }
        }
    }

    fn default_fn_sig(&self, def_id: DefId) -> Result<rty::PolySig, UnsupportedFnSig> {
        let fn_sig = rustc::lowering::lower_fn_sig_of(self.tcx, def_id)?.skip_binder();
        Ok(self.refine_fn_sig(&self.generics_of(def_id), &fn_sig, rty::Expr::tt))
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
                            .map(|variant_def| self.default_variant_def(def_id, variant_def))
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
                self.refine_generics(&generics)
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
        self.refine_ty(generics, rustc_ty, rty::Expr::tt)
    }

    pub fn refine_with_holes(&self, generics: &rty::Generics, rustc_ty: &rustc::ty::Ty) -> rty::Ty {
        self.refine_ty(generics, rustc_ty, rty::Expr::hole)
    }

    pub fn instantiate_generic_arg(
        &self,
        generics: &rty::Generics,
        param: &rty::GenericParamDef,
        arg: &rustc::ty::GenericArg,
    ) -> rty::GenericArg {
        self.refine_generic_arg(generics, param, arg, rty::Expr::hole)
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

    fn default_variant_def(
        &self,
        adt_def_id: DefId,
        variant_def: &rustc_middle::ty::VariantDef,
    ) -> rty::PolyVariant {
        if let Ok(variant_def) =
            rustc::lowering::lower_variant_def(self.tcx, self.sess, adt_def_id, variant_def)
        {
            let generics = self.generics_of(adt_def_id);
            let fields = variant_def
                .field_tys
                .iter()
                .map(|ty| self.refine_with_true(&generics, ty))
                .collect_vec();
            let rustc::ty::TyKind::Adt(def_id, substs) = variant_def.ret.kind() else {
                panic!();
            };
            let substs = iter::zip(&generics.params, substs)
                .map(|(param, arg)| self.refine_generic_arg(&generics, param, arg, rty::Expr::tt))
                .collect_vec();
            let bty = rty::BaseTy::adt(self.adt_def(*def_id), substs);
            let ret = rty::Ty::indexed(bty, rty::Index::unit());
            let value = rty::VariantDef::new(fields, ret);
            Binder::new(value, rty::Sort::unit())
        } else {
            FatalError.raise()
        }
    }

    fn refine_fn_sig(
        &self,
        generics: &rty::Generics,
        fn_sig: &rustc::ty::FnSig,
        mk_pred: fn() -> rty::Expr,
    ) -> rty::PolySig {
        let args = fn_sig
            .inputs()
            .iter()
            .map(|ty| self.refine_ty(generics, ty, mk_pred))
            .collect_vec();
        let ret = self.refine_ty(generics, &fn_sig.output(), mk_pred);
        let output = rty::Binder::new(rty::FnOutput::new(ret, vec![]), rty::Sort::unit());
        rty::PolySig::new([], rty::FnSig::new(vec![], args, output))
    }

    fn refine_ty(
        &self,
        generics: &rty::Generics,
        ty: &rustc::ty::Ty,
        mk_pred: fn() -> rty::Expr,
    ) -> rty::Ty {
        let ty = self.refine_ty_inner(generics, ty, mk_pred);
        if ty.sort().is_unit() {
            ty.skip_binders()
        } else {
            rty::Ty::exists(ty)
        }
    }

    fn refine_generic_arg(
        &self,
        generics: &rty::Generics,
        param: &rty::GenericParamDef,
        arg: &rustc::ty::GenericArg,
        mk_pred: fn() -> rty::Expr,
    ) -> rty::GenericArg {
        match (&param.kind, arg) {
            (rty::GenericParamDefKind::Type { .. }, rustc::ty::GenericArg::Ty(ty)) => {
                rty::GenericArg::Ty(self.refine_ty(generics, ty, mk_pred))
            }
            (rty::GenericParamDefKind::BaseTy, rustc::ty::GenericArg::Ty(ty)) => {
                rty::GenericArg::BaseTy(self.refine_ty_inner(generics, ty, mk_pred))
            }
            (rty::GenericParamDefKind::Lifetime, rustc::ty::GenericArg::Lifetime(_)) => {
                rty::GenericArg::Lifetime
            }
            _ => bug!("mismatched generic arg `{arg:?}` `{param:?}`"),
        }
    }

    fn refine_ty_inner(
        &self,
        generics: &rty::Generics,
        ty: &rustc::ty::Ty,
        mk_pred: fn() -> rty::Expr,
    ) -> Binder<rty::Ty> {
        let bty = match ty.kind() {
            rustc::ty::TyKind::Closure(did, _substs) => rty::BaseTy::Closure(*did),
            rustc::ty::TyKind::Never => rty::BaseTy::Never,
            rustc::ty::TyKind::Ref(ty, rustc::ty::Mutability::Mut) => {
                rty::BaseTy::Ref(rty::RefKind::Mut, self.refine_ty(generics, ty, mk_pred))
            }
            rustc::ty::TyKind::Ref(ty, rustc::ty::Mutability::Not) => {
                rty::BaseTy::Ref(rty::RefKind::Shr, self.refine_ty(generics, ty, mk_pred))
            }
            rustc::ty::TyKind::Float(float_ty) => rty::BaseTy::Float(*float_ty),
            rustc::ty::TyKind::Tuple(tys) => {
                let tys = tys
                    .iter()
                    .map(|ty| self.refine_ty(generics, ty, mk_pred))
                    .collect();
                rty::BaseTy::Tuple(tys)
            }
            rustc::ty::TyKind::Array(ty, len) => {
                rty::BaseTy::Array(self.refine_ty(generics, ty, mk_pred), len.clone())
            }
            rustc::ty::TyKind::Param(param_ty) => {
                match generics.param_at(param_ty.index as usize, self).kind {
                    rty::GenericParamDefKind::Type { .. } => {
                        return Binder::new(rty::Ty::param(*param_ty), rty::Sort::unit());
                    }
                    rty::GenericParamDefKind::BaseTy => rty::BaseTy::Param(*param_ty),
                    rty::GenericParamDefKind::Lifetime => bug!(),
                }
            }
            rustc::ty::TyKind::Adt(def_id, substs) => {
                let adt_def = self.adt_def(*def_id);
                let substs = iter::zip(&self.generics_of(*def_id).params, substs)
                    .map(|(param, arg)| self.refine_generic_arg(generics, param, arg, mk_pred))
                    .collect_vec();
                rty::BaseTy::adt(adt_def, substs)
            }
            rustc::ty::TyKind::Bool => rty::BaseTy::Bool,
            rustc::ty::TyKind::Int(int_ty) => rty::BaseTy::Int(*int_ty),
            rustc::ty::TyKind::Uint(uint_ty) => rty::BaseTy::Uint(*uint_ty),
            rustc::ty::TyKind::Str => rty::BaseTy::Str,
            rustc::ty::TyKind::Slice(ty) => {
                rty::BaseTy::Slice(self.refine_ty(generics, ty, mk_pred))
            }
            rustc::ty::TyKind::Char => rty::BaseTy::Char,
            rustc::ty::TyKind::FnSig(_) => todo!("refine_ty: FnSig"),
            rustc::ty::TyKind::RawPtr(ty, mu) => {
                rty::BaseTy::RawPtr(self.refine_with_true(generics, ty), *mu)
            }
        };
        let pred = mk_pred();
        let sort = bty.sort();
        let idx = rty::Expr::nu().eta_expand_tuple(&sort);
        let ty = if pred.is_trivially_true() {
            rty::Ty::indexed(bty, idx)
        } else {
            rty::Ty::constr(pred, rty::Ty::indexed(bty, idx))
        };
        Binder::new(ty, sort)
    }

    fn refine_generics(&self, generics: &rustc::ty::Generics) -> rty::Generics {
        let params = generics
            .params
            .iter()
            .map(|param| {
                let kind = match param.kind {
                    rustc::ty::GenericParamDefKind::Lifetime => rty::GenericParamDefKind::Lifetime,
                    rustc::ty::GenericParamDefKind::Type { has_default } => {
                        rty::GenericParamDefKind::Type { has_default }
                    }
                };
                rty::GenericParamDef {
                    kind,
                    index: param.index,
                    name: param.name,
                    def_id: param.def_id,
                }
            })
            .collect();
        rty::Generics {
            params,
            parent_count: generics.orig.parent_count,
            parent: generics.orig.parent,
        }
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
