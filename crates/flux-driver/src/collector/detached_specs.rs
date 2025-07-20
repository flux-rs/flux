use std::collections::HashMap;

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
        let mut idents = detached_specs
            .items
            .into_iter()
            .map(|item| (item.ident(), (item, None)))
            .collect();

        resolve_idents_in_scope(self.inner.tcx, parent, &mut idents);

        for (ident, (item, def_id)) in idents {
            let Some(def_id) = def_id else {
                return Err(self.inner.errors.emit(errors::AttrMapErr {
                    span: ident.span,
                    message: format!("unresolved identifier `{ident}`"),
                }));
            };
            if let Some(def_id) = def_id.as_local() {
                let owner_id = self.inner.tcx.local_def_id_to_hir_id(def_id).owner;
                self.collect_detached_item(owner_id, item)?;
            }
        }
        Ok(())
    }

    fn collect_detached_struct_def(
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

    fn collect_detached_item(&mut self, owner_id: OwnerId, item: surface::Item) -> Result {
        match item {
            surface::Item::FnSig(_, fn_sig) => self.collect_detached_fn_sig(owner_id, *fn_sig),
            surface::Item::StructDef(ident, struct_def) => {
                self.collect_detached_struct_def(ident, owner_id, *struct_def)
            }
            surface::Item::Mod(_, detached_specs) => self.run(detached_specs, owner_id.def_id),
        }
    }
}

fn resolve_idents_in_scope(
    tcx: TyCtxt,
    scope: LocalDefId,
    items: &mut HashMap<Ident, (surface::Item, Option<DefId>)>,
) {
    for child in tcx.module_children_local(scope) {
        let ident = child.ident;
        if let Res::Def(kind, def_id) = child.res {
            if let DefKind::Fn = kind
                && let Some(val) = items.get_mut(&ident)
                && matches!(val.0, surface::Item::FnSig(_, _))
                && val.1.is_none()
            {
                val.1 = Some(def_id);
            }
            if let DefKind::Mod = kind
                && let Some(val) = items.get_mut(&ident)
                && matches!(val.0, surface::Item::Mod(_, _))
                && val.1.is_none()
            {
                val.1 = Some(def_id);
            }
            if let DefKind::Struct = kind
                && let Some(val) = items.get_mut(&ident)
                && matches!(val.0, surface::Item::StructDef(_, _))
                && val.1.is_none()
            {
                val.1 = Some(def_id);
            }
        }
    }
}
