use std::collections::{HashMap, hash_map::Entry};

use flux_common::span_bug;
use flux_syntax::surface::{self, Span};
use rustc_errors::ErrorGuaranteed;
use rustc_hir::{
    OwnerId,
    def::{DefKind, Res},
    def_id::{CRATE_DEF_ID, LocalDefId},
};
use rustc_middle::ty::{AssocKind, Ty, TyCtxt};
use rustc_span::{Symbol, def_id::DefId};

use crate::collector::{FluxAttrs, SpecCollector, errors, hir::PrimTy, surface::Ident};
type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

#[derive(PartialEq, Eq, Debug, Hash)]
enum ImplKey {
    /// for impl of types with an explicit DefId type constructor
    Ident(Symbol),
    /// for impl of primitive types
    Prim(PrimTy),
}

// pub enum PrimTy {
//     Int(IntTy),
//     Uint(UintTy),
//     Float(FloatTy),
//     Str,
//     Bool,
//     Char,
// }
impl From<Ty<'_>> for ImplKey {
    fn from(ty: Ty) -> Self {
        match ty.kind() {
        //     rustc_middle::ty::TyKind::Bool => ImplKey::Prim(PrimTy::Bool),
        //     rustc_middle::ty::TyKind::Char => ImplKey::Prim(PrimTy::Char),
        //     // rustc_middle::ty::TyKind::Int(int_ty) => ImplKey::Prim(PrimTy::Int(*int_ty)),
        //     // rustc_middle::ty::TyKind::Uint(uint_ty) => ImplKey::Prim(PrimTy::Uint(*uint_ty)),
        //     // rustc_middle::ty::TyKind::Float(float_ty) => ImplKey::Prim(PrimTy::Float(*float_ty)),
        //     rustc_middle::ty::TyKind::Str => ImplKey::Prim(PrimTy::Str),
        //     rustc_middle::ty::TyKind::Adt(adt_def, _) => {
        //         ImplKey::Ident(adt_def.did().as_local().map_or_else(
        //             || Symbol::intern(&format!("{:?}", adt_def.did())),
        //             |local_def_id| Symbol::intern(&format!("{:?}", local_def_id)),
        //         ))
        //     }
        //     rustc_middle::ty::TyKind::Tuple(_) => ImplKey::Ident(Symbol::intern("tuple")),
        //     rustc_middle::ty::TyKind::Array(_, _) => ImplKey::Ident(Symbol::intern("array")),
        //     rustc_middle::ty::TyKind::Slice(_) => ImplKey::Ident(Symbol::intern("slice")),
        //     rustc_middle::ty::TyKind::RawPtr(_, _) => ImplKey::Ident(Symbol::intern("raw_ptr")),
        //     rustc_middle::ty::TyKind::Ref(_, _, _) => ImplKey::Ident(Symbol::intern("ref")),
        //     rustc_middle::ty::TyKind::FnDef(def_id, _) => {
        //         ImplKey::Ident(Symbol::intern(&format!("{:?}", def_id)))
        //     }
        //     rustc_middle::ty::TyKind::FnPtr(_) => ImplKey::Ident(Symbol::intern("fn_ptr")),
        //     rustc_middle::ty::TyKind::Closure(def_id, _) => {
        //         ImplKey::Ident(Symbol::intern(&format!("{:?}", def_id)))
        //     }
        //     rustc_middle::ty::TyKind::CoroutineClosure(def_id, _) => {
        //         ImplKey::Ident(Symbol::intern(&format!("{:?}", def_id)))
        //     }
        //     rustc_middle::ty::TyKind::Coroutine(def_id, _) => {
        //         ImplKey::Ident(Symbol::intern(&format!("{:?}", def_id)))
        //     }
        //     rustc_middle::ty::TyKind::CoroutineWitness(def_id, _) => {
        //         ImplKey::Ident(Symbol::intern(&format!("{:?}", def_id)))
        //     }
        //     rustc_middle::ty::TyKind::Never => ImplKey::Ident(Symbol::intern("never")),
        //     rustc_middle::ty::TyKind::Dynamic(_, _, _) => ImplKey::Ident(Symbol::intern("dyn")),
        //     rustc_middle::ty::TyKind::Foreign(def_id) => {
        //         ImplKey::Ident(Symbol::intern(&format!("{:?}", def_id)))
        //     }
        //     rustc_middle::ty::TyKind::Alias(_, _) => ImplKey::Ident(Symbol::intern("alias")),
        //     rustc_middle::ty::TyKind::Param(param_ty) => ImplKey::Ident(param_ty.name),
        //     rustc_middle::ty::TyKind::Bound(_, _) => ImplKey::Ident(Symbol::intern("bound")),
        //     rustc_middle::ty::TyKind::Placeholder(_) => {
        //         ImplKey::Ident(Symbol::intern("placeholder"))
        //     }
        //     rustc_middle::ty::TyKind::Infer(_) => ImplKey::Ident(Symbol::intern("infer")),
        //     rustc_middle::ty::TyKind::Error(_) => ImplKey::Ident(Symbol::intern("error")),
        // }
        }
    }
}

type TraitImplKey = (ImplKey, Symbol);

struct DetachedItems {
    items: HashMap<Ident, (surface::Item, Option<DefId>)>,
    inherent_impls: HashMap<Ident, (surface::DetachedInherentImpl, Option<DefId>)>,
    trait_impls: HashMap<TraitImplKey, (surface::DetachedTraitImpl, Option<LocalDefId>, Span)>,
}

impl DetachedItems {
    fn new(detached_specs: surface::DetachedSpecs, collector: &mut SpecCollector) -> Result<Self> {
        let mut items = HashMap::default();
        let mut inherent_impls: HashMap<Ident, (surface::DetachedInherentImpl, Option<DefId>)> =
            HashMap::default();
        let mut trait_impls = HashMap::default();
        for item in detached_specs.items {
            match item.kind {
                surface::ItemKind::InherentImpl(detached_impl) => {
                    if let Some(existing) = inherent_impls.get_mut(&item.ident) {
                        existing.0.extend(detached_impl);
                    } else {
                        inherent_impls.insert(item.ident, (detached_impl, None));
                    }
                }
                surface::ItemKind::TraitImpl(detached_impl) => {
                    let key = (ImplKey::Ident(item.ident.name), detached_impl.trait_.name);
                    let span = item.ident.span;
                    if let std::collections::hash_map::Entry::Vacant(e) = trait_impls.entry(key) {
                        e.insert((detached_impl, None, span));
                    } else {
                        return Err(collector.errors.emit(errors::AttrMapErr {
                            span,
                            message: format!("multiple impls for `{}`", item.ident.name),
                        }));
                    }
                }
                _ => {
                    items.insert(item.ident, (item, None));
                }
            }
        }
        Ok(DetachedItems { items, inherent_impls, trait_impls })
    }

    fn resolve(&mut self, tcx: TyCtxt, scope: LocalDefId) {
        self.resolve_items(tcx, scope);
        self.resolve_inherent_impls(tcx, scope);
        self.resolve_trait_impls(tcx);
    }

    fn resolve_trait_impls(&mut self, tcx: TyCtxt) {
        for (trait_id, impl_ids) in tcx.all_local_trait_impls(()) {
            if let Some(trait_symbol) = tcx.opt_item_name(*trait_id) {
                for impl_id in impl_ids {
                    if let Some(poly_trait_ref) = tcx.impl_trait_ref(*impl_id) {
                        // let self_ty = poly_trait_ref.instantiate_identity().self_ty();
                        // let self_symbol = Symbol::intern(&format!("{self_ty:?}"));
                        let self_key = poly_trait_ref.instantiate_identity().self_ty().into();
                        if let Some(val) = self.trait_impls.get_mut(&(self_key, trait_symbol)) {
                            val.1 = Some(*impl_id);
                        }
                    }
                }
            }
        }
    }

    fn resolve_inherent_impls(&mut self, tcx: TyCtxt, scope: LocalDefId) {
        for child in tcx.module_children_local(scope) {
            let ident = child.ident;
            if let Res::Def(kind, def_id) = child.res
                && matches!(kind, DefKind::Struct | DefKind::Enum)
                && let Some(val) = self.inherent_impls.get_mut(&ident)
            {
                val.1 = Some(def_id);
            }
        }
    }

    fn resolve_items(&mut self, tcx: TyCtxt, scope: LocalDefId) {
        for child in tcx.module_children_local(scope) {
            let ident = child.ident;

            if let Res::Def(kind, def_id) = child.res {
                if let DefKind::Fn = kind
                    && let Some(val) = self.items.get_mut(&ident)
                    && matches!(val.0.kind, surface::ItemKind::FnSig(_))
                    && val.1.is_none()
                {
                    val.1 = Some(def_id);
                }
                if let DefKind::Mod = kind
                    && let Some(val) = self.items.get_mut(&ident)
                    && matches!(val.0.kind, surface::ItemKind::Mod(_))
                    && val.1.is_none()
                {
                    val.1 = Some(def_id);
                }
                if let DefKind::Struct = kind
                    && let Some(val) = self.items.get_mut(&ident)
                    && matches!(val.0.kind, surface::ItemKind::Struct(_))
                    && val.1.is_none()
                {
                    val.1 = Some(def_id);
                }
                if let DefKind::Enum = kind
                    && let Some(val) = self.items.get_mut(&ident)
                    && matches!(val.0.kind, surface::ItemKind::Enum(_))
                    && val.1.is_none()
                {
                    val.1 = Some(def_id);
                }
            }
        }
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

    fn run(&mut self, detached_specs: surface::DetachedSpecs, parent: LocalDefId) -> Result {
        let mut detached_items = DetachedItems::new(detached_specs, self.inner)?;

        detached_items.resolve(self.inner.tcx, parent);

        for (ident, (item, def_id)) in detached_items.items {
            if let Some(def_id) = self.unwrap_def_id(ident, def_id)? {
                let owner_id = self.inner.tcx.local_def_id_to_hir_id(def_id).owner;
                self.collect_detached_item(owner_id, item)?;
            }
        }
        for (ident, (inherent_impl, def_id)) in detached_items.inherent_impls {
            if let Some(def_id) = self.unwrap_def_id(ident, def_id)? {
                self.collect_inherent_impl(def_id, inherent_impl)?;
            }
        }
        for ((_, _), (trait_impl, impl_id, _)) in detached_items.trait_impls {
            if let Some(impl_id) = impl_id {
                self.collect_trait_impl(impl_id, trait_impl)?;
            }
        }
        Ok(())
    }

    #[allow(
        clippy::disallowed_methods,
        reason = "this is pre-extern specs so it's fine: https://flux-rs.zulipchat.com/#narrow/channel/486369-verify-std/topic/detached-specs/near/529548357"
    )]
    fn unwrap_def_id(&mut self, ident: Ident, def_id: Option<DefId>) -> Result<Option<LocalDefId>> {
        let Some(def_id) = def_id else {
            return Err(self.inner.errors.emit(errors::AttrMapErr {
                span: ident.span,
                message: format!("unresolved identifier `{ident}`"),
            }));
        };
        Ok(def_id.as_local())
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

    fn collect_fn_sig(&mut self, owner_id: OwnerId, fn_sig: surface::FnSig) -> Result {
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

    fn collect_trait_impl(
        &mut self,
        impl_id: LocalDefId,
        trait_impl: surface::DetachedTraitImpl,
    ) -> Result {
        let mut table: HashMap<Symbol, (surface::FnSig, Option<DefId>, Span)> = HashMap::default();
        // 1. make a table of the impl-items
        for item in trait_impl.items {
            let key = item.ident.name;
            if let Entry::Occupied(_) = table.entry(key) {
                return Err(self.inner.errors.emit(errors::AttrMapErr {
                    span: item.ident.span,
                    message: format!("multiple specs for `{}`", item.ident),
                }));
            } else {
                table.insert(item.ident.name, (item.kind, None, item.ident.span));
            }
        }

        // 2. walk over all associated-items, resolving the items
        for item in self
            .inner
            .tcx
            .associated_items(impl_id)
            .in_definition_order()
        {
            if let AssocKind::Fn { name, .. } = item.kind
                && let Some(val) = table.get_mut(&name)
                && val.1.is_none()
            {
                val.1 = Some(item.def_id);
            }
        }

        // 3. Attach the `fn_sig` to the resolved `DefId`
        for (name, (fn_sig, def_id, span)) in table {
            let ident = Ident { name, span };
            if let Some(def_id) = self.unwrap_def_id(ident, def_id)? {
                let owner_id = self.inner.tcx.local_def_id_to_hir_id(def_id).owner;
                self.collect_fn_sig(owner_id, fn_sig)?;
            }
        }

        Ok(())
    }

    fn collect_inherent_impl(
        &mut self,
        ty_def_id: LocalDefId,
        inherent_impl: surface::DetachedInherentImpl,
    ) -> Result {
        let mut table: HashMap<Symbol, (surface::FnSig, Option<DefId>, Span)> = HashMap::default();
        // 1. make a table of the impl-items
        for item in inherent_impl.items {
            let key = item.ident.name;
            if let Entry::Occupied(_) = table.entry(key) {
                return Err(self.inner.errors.emit(errors::AttrMapErr {
                    span: item.ident.span,
                    message: format!("multiple specs for `{}`", item.ident),
                }));
            } else {
                table.insert(item.ident.name, (item.kind, None, item.ident.span));
            }
        }
        // 2. walk over all the impl-def-ids resolving the items
        for impl_id in self.inner.tcx.inherent_impls(ty_def_id) {
            for item in self
                .inner
                .tcx
                .associated_items(impl_id)
                .in_definition_order()
            {
                if let AssocKind::Fn { name, .. } = item.kind
                    && let Some(val) = table.get_mut(&name)
                    && val.1.is_none()
                {
                    val.1 = Some(item.def_id);
                }
            }
        }

        // 3. Attach the `fn_sig` to the resolved `DefId`
        for (name, (fn_sig, def_id, span)) in table {
            let ident = Ident { name, span };
            if let Some(def_id) = self.unwrap_def_id(ident, def_id)? {
                let owner_id = self.inner.tcx.local_def_id_to_hir_id(def_id).owner;
                self.collect_fn_sig(owner_id, fn_sig)?;
            }
        }

        Ok(())
    }

    fn collect_detached_item(&mut self, owner_id: OwnerId, item: surface::Item) -> Result {
        match item.kind {
            surface::ItemKind::FnSig(item) => self.collect_fn_sig(owner_id, item.kind),
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
