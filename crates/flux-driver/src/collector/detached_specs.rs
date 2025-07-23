use std::collections::HashMap;

use flux_common::span_bug;
use flux_syntax::surface::{self};
use rustc_errors::ErrorGuaranteed;
use rustc_hir::{
    OwnerId,
    def::{DefKind, Res},
    def_id::{CRATE_DEF_ID, LocalDefId},
};
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::DefId;

use crate::collector::{FluxAttrs, SpecCollector, errors, surface::Ident};

type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

struct DetachedItems {
    items: HashMap<Ident, (surface::Item, Option<DefId>)>,
    inherent_impls: HashMap<Ident, (surface::DetachedImpl, Option<DefId>)>,
    // trait_impls: HashMap<(Ident, Ident), (surface::Item, Option<DefId>)>,
}

impl DetachedItems {
    fn new(detached_specs: surface::DetachedSpecs) -> Self {
        let mut items = HashMap::default();
        let mut inherent_impls = HashMap::default();
        for item in detached_specs.items.into_iter() {
            if let surface::ItemKind::InherentImpl(detached_impl) = item.kind {
                inherent_impls.insert(item.ident, (detached_impl, None));
            } else {
                items.insert(item.ident, (item, None));
            }
        }
        DetachedItems { items, inherent_impls }
    }
}

pub(super) struct DetachedSpecsCollector<'a, 'sess, 'tcx> {
    inner: &'a mut SpecCollector<'sess, 'tcx>,
}

impl<'a, 'sess, 'tcx> DetachedSpecsCollector<'a, 'sess, 'tcx> {
    pub(super) fn collect(
        inner: &'a mut SpecCollector<'sess, 'tcx>,
        attrs: &mut FluxAttrs,
    ) -> Result {
        if let Some(detached_specs) = attrs.detached_specs() {
            Self { inner }.run(detached_specs, CRATE_DEF_ID)?;
        };
        Ok(())
    }
    #[allow(
        clippy::disallowed_methods,
        reason = "this is pre-extern specs so it's fine: https://flux-rs.zulipchat.com/#narrow/channel/486369-verify-std/topic/detached-specs/near/529548357"
    )]
    fn run(&mut self, detached_specs: surface::DetachedSpecs, parent: LocalDefId) -> Result {
        let mut detached_items = DetachedItems::new(detached_specs);

        resolve_idents_in_scope(self.inner.tcx, parent, &mut detached_items);

        for (ident, (item, def_id)) in detached_items.items {
            let def_id = self.unwrap_def_id(ident, def_id)?;
            if let Some(def_id) = def_id.as_local() {
                let owner_id = self.inner.tcx.local_def_id_to_hir_id(def_id).owner;
                self.collect_detached_item(owner_id, item)?;
            }
        }
        for (ident, (detached_impl, def_id)) in detached_items.inherent_impls {
            let def_id = self.unwrap_def_id(ident, def_id)?;
            self.collect_detached_impl(def_id, detached_impl)?;
            // panic!("TRACE: inherent_impls {ident:?} => {impls:?}");
        }
        Ok(())
    }

    fn unwrap_def_id(&mut self, ident: Ident, def_id: Option<DefId>) -> Result<DefId> {
        let Some(def_id) = def_id else {
            return Err(self.inner.errors.emit(errors::AttrMapErr {
                span: ident.span,
                message: format!("unresolved identifier `{ident}`"),
            }));
        };
        Ok(def_id)
    }

    fn collect_detached_enum(
        &mut self,
        ident: Ident,
        owner_id: OwnerId,
        enum_def: surface::EnumDef,
    ) -> Result {
        let entry = self
            .inner
            .specs
            .enums
            .entry(owner_id)
            .or_insert(surface::EnumDef {
                generics: None,
                refined_by: None,
                variants: vec![],
                invariants: vec![],
                reflected: false,
            });

        if entry.is_nontrivial() {
            let name = self.inner.tcx.def_path_str(owner_id.to_def_id());
            return Err(self.inner.errors.emit(errors::AttrMapErr {
                span: ident.span,
                message: format!("multiple specs for `{name}`"),
            }));
        } else {
            *entry = enum_def;
        }
        Ok(())
    }

    fn collect_detached_struct(
        &mut self,
        ident: Ident,
        owner_id: OwnerId,
        struct_def: surface::StructDef,
    ) -> Result {
        let entry = self
            .inner
            .specs
            .structs
            .entry(owner_id)
            .or_insert(surface::StructDef {
                generics: None,
                refined_by: None,
                fields: vec![],
                opaque: false,
                invariants: vec![],
            });

        if entry.is_nontrivial() {
            let name = self.inner.tcx.def_path_str(owner_id.to_def_id());
            return Err(self.inner.errors.emit(errors::AttrMapErr {
                span: ident.span,
                message: format!("multiple specs for `{name}`"),
            }));
        } else {
            *entry = struct_def;
        }
        Ok(())
    }

    fn collect_detached_fn_sig(&mut self, owner_id: OwnerId, fn_sig: surface::FnSig) -> Result {
        let spec = self
            .inner
            .specs
            .fn_sigs
            .entry(owner_id)
            .or_insert(surface::FnSpec { fn_sig: None, qual_names: None, reveal_names: None });

        if spec.fn_sig.is_some() {
            let name = self.inner.tcx.def_path_str(owner_id.to_def_id());
            return Err(self.inner.errors.emit(errors::AttrMapErr {
                span: fn_sig.span,
                message: format!("multiple specs for `{name}`"),
            }));
        }

        spec.fn_sig = Some(fn_sig);
        Ok(())
    }

    fn collect_detached_impl(
        &mut self,
        ty_def_id: DefId,
        detached_impl: surface::DetachedImpl,
    ) -> Result {
        Ok(())
        // let mut table = HashMap::default();
        // for if let surface::Item::InherentImpl(ident, detached_impl) = item {
        //         inherent_impls.insert(ident, (detached_impl, None));
        // } else {

        // for impl_def_id in self.inner.tcx.inherent_impls(def_id) {
        //    update-table-with-impl-def-id
        // }
        // for entry in table {
        //   if unbound(entry) report error else { link }
        // }
        //
    }

    fn collect_detached_item(&mut self, owner_id: OwnerId, item: surface::Item) -> Result {
        match item.kind {
            surface::ItemKind::FnSig(item) => self.collect_detached_fn_sig(owner_id, item.kind),
            surface::ItemKind::Struct(struct_def) => {
                self.collect_detached_struct(item.ident, owner_id, struct_def)
            }
            surface::ItemKind::Enum(enum_def) => {
                self.collect_detached_enum(item.ident, owner_id, enum_def)
            }
            surface::ItemKind::Mod(detached_specs) => self.run(detached_specs, owner_id.def_id),
            _ => {
                span_bug!(item.ident.span, "unexpected detached item!")
            }
        }
    }
}

fn resolve_idents_in_scope(tcx: TyCtxt, scope: LocalDefId, detached_items: &mut DetachedItems) {
    for child in tcx.module_children_local(scope) {
        let ident = child.ident;
        if let Res::Def(kind, def_id) = child.res {
            if let DefKind::Fn = kind
                && let Some(val) = detached_items.items.get_mut(&ident)
                && matches!(val.0.kind, surface::ItemKind::FnSig(_))
                && val.1.is_none()
            {
                val.1 = Some(def_id);
            }
            if let DefKind::Mod = kind
                && let Some(val) = detached_items.items.get_mut(&ident)
                && matches!(val.0.kind, surface::ItemKind::Mod(_))
                && val.1.is_none()
            {
                val.1 = Some(def_id);
            }
            if let DefKind::Struct = kind
                && let Some(val) = detached_items.items.get_mut(&ident)
                && matches!(val.0.kind, surface::ItemKind::Struct(_))
                && val.1.is_none()
            {
                val.1 = Some(def_id);
            }
            if let DefKind::Enum = kind
                && let Some(val) = detached_items.items.get_mut(&ident)
                && matches!(val.0.kind, surface::ItemKind::Enum(_))
                && val.1.is_none()
            {
                val.1 = Some(def_id);
            }
            if matches!(kind, DefKind::Struct | DefKind::Enum)
                && let Some(val) = detached_items.inherent_impls.get_mut(&ident)
            {
                val.1 = Some(def_id)
            }
        }
    }
}
