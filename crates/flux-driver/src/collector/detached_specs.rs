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
            surface::Item::Mod(_, detached_specs) => self.run(detached_specs, owner_id.def_id),
        }
    }
}

// struct DetachedIdentResolver<'a> {
//     items: &'a mut HashMap<Ident, (surface::Item, Option<DefId>)>,
// }
//
// impl<'tcx> hir::intravisit::Visitor<'tcx> for DetachedIdentResolver<'_> {
//     fn visit_item(&mut self, item: &'tcx Item<'tcx>) {
//         if let ItemKind::Fn { ident, .. } = item.kind
//             && let Some(val) = self.items.get_mut(&ident)
//             && matches!(val.0, surface::Item::FnSig(_, _))
//             && val.1.is_none()
//         {
//             val.1 = Some(item.owner_id.def_id);
//         }
//         if let ItemKind::Mod(ident, ..) = item.kind
//             && let Some(val) = self.items.get_mut(&ident)
//             && matches!(val.0, surface::Item::Mod(_, _))
//             && val.1.is_none()
//         {
//             val.1 = Some(item.owner_id.def_id);
//         }
//     }
// }

fn resolve_idents_in_scope(
    tcx: TyCtxt,
    scope: LocalDefId,
    items: &mut HashMap<Ident, (surface::Item, Option<DefId>)>,
) {
    // let scope = LocalModDefId::new_unchecked(scope);
    // tcx.hir_visit_item_likes_in_module(scope, &mut DetachedIdentResolver { items });
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
        }
    }
}
