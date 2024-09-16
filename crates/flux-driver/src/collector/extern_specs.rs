use flux_rustc_bridge::lowering;
use rustc_hir as hir;
use rustc_hir::{def_id::DefId, BodyId, OwnerId};
use rustc_middle::ty::TyCtxt;
use rustc_span::ErrorGuaranteed;

use super::{FluxAttrs, SpecCollector};

type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

pub(super) struct ExternSpecCollector<'a, 'sess, 'tcx> {
    inner: &'a mut SpecCollector<'sess, 'tcx>,
    /// The block corresponding to the `const _: () = { ... }` annotated with `flux::extern_spec`
    block: &'tcx hir::Block<'tcx>,
}

struct ExternImplItem {
    impl_id: DefId,
    item_id: DefId,
}

impl<'a, 'sess, 'tcx> ExternSpecCollector<'a, 'sess, 'tcx> {
    pub(super) fn collect(inner: &'a mut SpecCollector<'sess, 'tcx>, body_id: BodyId) -> Result {
        Self::new(inner, body_id)?.run()
    }

    fn new(inner: &'a mut SpecCollector<'sess, 'tcx>, body_id: BodyId) -> Result<Self> {
        let body = inner.tcx.hir().body(body_id);
        if let hir::ExprKind::Block(block, _) = body.value.kind {
            Ok(Self { inner, block })
        } else {
            Err(inner
                .errors
                .emit(errors::MalformedExternSpec::new(body.value.span)))
        }
    }

    fn run(mut self) -> Result {
        let item = self.item_at(0)?;

        let attrs = self
            .inner
            .parse_attrs_and_report_dups(item.owner_id.def_id)?;

        match &item.kind {
            hir::ItemKind::Fn(..) => self.collect_extern_fn(item, attrs),
            hir::ItemKind::Enum(enum_def, _) => {
                self.collect_extern_enum(item.owner_id, enum_def, attrs)
            }
            hir::ItemKind::Struct(variant, _) => {
                self.collect_extern_struct(item.owner_id, variant, attrs)
            }
            hir::ItemKind::Trait(_, _, _, bounds, items) => {
                self.collect_extern_trait(item.owner_id, bounds, items, attrs)
            }
            hir::ItemKind::Impl(impl_) => self.collect_extern_impl(item.owner_id, impl_, attrs),
            _ => Err(self.malformed()),
        }
    }

    fn collect_extern_fn(&mut self, item: &hir::Item, attrs: FluxAttrs) -> Result {
        self.inner.collect_fn_spec(item.owner_id, attrs)?;

        let extern_id = self.extract_extern_id_from_fn(item)?;
        self.inner
            .specs
            .insert_extern_id(item.owner_id.def_id, extern_id);

        Ok(())
    }

    fn collect_extern_struct(
        &mut self,
        struct_id: OwnerId,
        variant: &hir::VariantData,
        attrs: FluxAttrs,
    ) -> Result {
        let dummy_struct = self.item_at(1)?;
        self.inner.specs.insert_dummy(dummy_struct.owner_id);

        let extern_id = self.extract_extern_id_from_struct(dummy_struct).unwrap();
        self.inner
            .specs
            .insert_extern_id(struct_id.def_id, extern_id);

        self.inner.collect_struct_def(struct_id, attrs, variant)?;

        Ok(())
    }

    fn collect_extern_enum(
        &mut self,
        enum_id: OwnerId,
        enum_def: &hir::EnumDef,
        attrs: FluxAttrs,
    ) -> Result {
        let dummy_struct = self.item_at(1)?;
        self.inner.specs.insert_dummy(dummy_struct.owner_id);

        let extern_id = self.extract_extern_id_from_struct(dummy_struct).unwrap();
        self.inner.specs.insert_extern_id(enum_id.def_id, extern_id);

        self.inner.collect_enum_def(enum_id, attrs, enum_def)?;

        Ok(())
    }

    fn collect_extern_impl(
        &mut self,
        impl_id: OwnerId,
        impl_: &hir::Impl,
        attrs: FluxAttrs,
    ) -> Result {
        self.inner.collect_impl(impl_id, attrs)?;

        let dummy_item = self.item_at(1)?;
        self.inner.specs.insert_dummy(dummy_item.owner_id);

        // If this is a trait impl compute the impl_id from the trait_ref
        let mut impl_of_trait = None;
        if let hir::ItemKind::Impl(dummy_impl) = dummy_item.kind {
            impl_of_trait =
                Some(self.extract_extern_id_from_impl(dummy_item.owner_id, dummy_impl)?);

            self.inner.specs.insert_dummy(self.item_at(2)?.owner_id);
        }

        let mut extern_impl_id = impl_of_trait;
        for item in impl_.items {
            let item_id = item.id.owner_id.def_id;
            let extern_item = if let hir::AssocItemKind::Fn { .. } = item.kind {
                let attrs = self.inner.parse_attrs_and_report_dups(item_id)?;
                self.collect_extern_impl_fn(impl_of_trait, item, attrs)?
            } else {
                continue;
            };

            if *extern_impl_id.get_or_insert(extern_item.impl_id) != extern_item.impl_id {
                return Err(self.invalid_impl_block());
            }
        }

        if let Some(extern_impl_id) = extern_impl_id {
            self.inner
                .specs
                .insert_extern_id(impl_id.def_id, extern_impl_id);
        }

        Ok(())
    }

    fn collect_extern_impl_fn(
        &mut self,
        impl_of_trait: Option<DefId>,
        item: &hir::ImplItemRef,
        attrs: FluxAttrs,
    ) -> Result<ExternImplItem> {
        let item_id = item.id.owner_id;
        self.inner.collect_fn_spec(item_id, attrs)?;

        let extern_item = self.extract_extern_id_from_impl_fn(impl_of_trait, item)?;
        self.inner
            .specs
            .insert_extern_id(item_id.def_id, extern_item.item_id);

        Ok(extern_item)
    }

    fn collect_extern_trait(
        &mut self,
        trait_id: OwnerId,
        bounds: &hir::GenericBounds,
        items: &[hir::TraitItemRef],
        attrs: FluxAttrs,
    ) -> Result {
        self.inner.collect_trait(trait_id, attrs)?;

        let extern_trait_id = self.extract_extern_id_from_trait(bounds)?;
        self.inner
            .specs
            .insert_extern_id(trait_id.def_id, extern_trait_id);

        for item in items {
            let item_id = item.id.owner_id.def_id;
            if let hir::AssocItemKind::Fn { .. } = item.kind {
                let attrs = self.inner.parse_attrs_and_report_dups(item_id)?;
                self.collect_extern_trait_fn(extern_trait_id, item, attrs)?;
            } else {
                continue;
            }
        }

        Ok(())
    }

    fn collect_extern_trait_fn(
        &mut self,
        extern_trait_id: DefId,
        item: &hir::TraitItemRef,
        attrs: FluxAttrs,
    ) -> Result {
        let item_id = item.id.owner_id;
        self.inner.collect_fn_spec(item_id, attrs)?;

        let extern_fn_id = self.extract_extern_id_from_trait_fn(extern_trait_id, item)?;
        self.inner
            .specs
            .insert_extern_id(item.id.owner_id.def_id, extern_fn_id);

        Ok(())
    }

    fn extract_extern_id_from_struct(&self, item: &hir::Item) -> Result<DefId> {
        if let hir::ItemKind::Struct(data, ..) = item.kind
            && let Some(extern_field) = data.fields().last()
            && let ty = self.tcx().type_of(extern_field.def_id)
            && let Some(adt_def) = ty.skip_binder().ty_adt_def()
        {
            Ok(adt_def.did())
        } else {
            Err(self.malformed())
        }
    }

    fn extract_extern_id_from_fn(&self, item: &hir::Item) -> Result<DefId> {
        if let hir::ItemKind::Fn(_, _, body_id) = item.kind {
            self.extract_callee_from_body(body_id)
        } else {
            Err(self.malformed())
        }
    }

    fn extract_extern_id_from_impl_fn(
        &self,
        impl_of_trait: Option<DefId>,
        item: &hir::ImplItemRef,
    ) -> Result<ExternImplItem> {
        if let hir::ImplItemKind::Fn(_, body_id) = self.tcx().hir().impl_item(item.id).kind {
            let callee_id = self.extract_callee_from_body(body_id)?;
            if let Some(extern_impl_id) = impl_of_trait {
                let map = self.tcx().impl_item_implementor_ids(extern_impl_id);
                if let Some(extern_item_id) = map.get(&callee_id) {
                    Ok(ExternImplItem { impl_id: extern_impl_id, item_id: *extern_item_id })
                } else {
                    Err(self.item_not_in_trait_impl(item.id.owner_id, callee_id, extern_impl_id))
                }
            } else {
                let opt_extern_impl_id = self.tcx().impl_of_method(callee_id);
                if let Some(extern_impl_id) = opt_extern_impl_id {
                    debug_assert!(self.tcx().trait_id_of_impl(extern_impl_id).is_none());
                    Ok(ExternImplItem { impl_id: extern_impl_id, item_id: callee_id })
                } else {
                    Err(self.invalid_item_in_inherent_impl(item.id.owner_id, callee_id))
                }
            }
        } else {
            Err(self.malformed())
        }
    }

    fn extract_extern_id_from_trait(&self, bounds: &hir::GenericBounds) -> Result<DefId> {
        if let Some(bound) = bounds.first()
            && let Some(trait_ref) = bound.trait_ref()
            && let Some(trait_id) = trait_ref.trait_def_id()
        {
            Ok(trait_id)
        } else {
            Err(self.malformed())
        }
    }

    fn extract_extern_id_from_trait_fn(
        &self,
        trait_id: DefId,
        item: &hir::TraitItemRef,
    ) -> Result<DefId> {
        if let hir::TraitItemKind::Fn(_, trait_fn) = self.tcx().hir().trait_item(item.id).kind
            && let hir::TraitFn::Provided(body_id) = trait_fn
        {
            let callee_id = self.extract_callee_from_body(body_id)?;
            if let Some(callee_trait_id) = self.tcx().trait_of_item(callee_id)
                && trait_id == callee_trait_id
            {
                Ok(callee_id)
            } else {
                // I can't figure out how to trigger this with generated with the extern spec
                // macro that type checks but leaving it here as a precaution.
                Err(self.item_not_in_trait(item.id.owner_id, callee_id, trait_id))
            }
        } else {
            Err(self.malformed())
        }
    }

    fn extract_extern_id_from_impl(&self, impl_id: OwnerId, impl_: &hir::Impl) -> Result<DefId> {
        if let Some(item) = impl_.items.first()
            && let hir::AssocItemKind::Fn { .. } = item.kind
            && let Some((clause, _)) = self
                .tcx()
                .predicates_of(item.id.owner_id.def_id)
                .predicates
                .first()
            && let Some(poly_trait_pred) = clause.as_trait_clause()
            && let Some(trait_pred) = poly_trait_pred.no_bound_vars()
        {
            let trait_ref = trait_pred.trait_ref;
            lowering::resolve_trait_ref_impl_id(self.tcx(), impl_id.to_def_id(), trait_ref)
                .map(|(impl_id, _)| impl_id)
                .ok_or_else(|| self.cannot_resolve_trait_impl())
        } else {
            Err(self.malformed())
        }
    }

    fn extract_callee_from_body(&self, body_id: hir::BodyId) -> Result<DefId> {
        let owner = self.tcx().hir().body_owner_def_id(body_id);
        let typeck = self.tcx().typeck(owner);
        if let hir::ExprKind::Block(b, _) = self.tcx().hir().body(body_id).value.kind
            && let Some(e) = b.expr
            && let hir::ExprKind::Call(callee, _) = e.kind
            && let rustc_middle::ty::FnDef(callee_id, _) = typeck.node_type(callee.hir_id).kind()
        {
            Ok(*callee_id)
        } else {
            Err(self.malformed())
        }
    }

    /// Returns the item inside the const block at position `i` starting from the end.
    #[track_caller]
    fn item_at(&self, i: usize) -> Result<&'tcx hir::Item<'tcx>> {
        let stmts = self.block.stmts;
        let index = stmts
            .len()
            .checked_sub(i + 1)
            .ok_or_else(|| self.malformed())?;
        let st = stmts.get(index).ok_or_else(|| self.malformed())?;
        if let hir::StmtKind::Item(item_id) = st.kind {
            Ok(self.tcx().hir().item(item_id))
        } else {
            Err(self.malformed())
        }
    }

    #[track_caller]
    fn malformed(&self) -> ErrorGuaranteed {
        self.inner
            .errors
            .emit(errors::MalformedExternSpec::new(self.block.span))
    }

    #[track_caller]
    fn item_not_in_trait_impl(
        &self,
        local_id: OwnerId,
        extern_id: DefId,
        extern_impl_id: DefId,
    ) -> ErrorGuaranteed {
        let tcx = self.tcx();
        self.inner.errors.emit(errors::ItemNotInTraitImpl {
            span: self
                .tcx()
                .def_ident_span(local_id)
                .unwrap_or_else(|| tcx.def_span(local_id)),
            name: tcx.def_path_str(extern_id),
            extern_impl_span: tcx.def_span(extern_impl_id),
        })
    }

    fn invalid_item_in_inherent_impl(
        &self,
        local_id: OwnerId,
        extern_id: DefId,
    ) -> ErrorGuaranteed {
        let tcx = self.tcx();
        self.inner.errors.emit(errors::InvalidItemInInherentImpl {
            span: self
                .tcx()
                .def_ident_span(local_id)
                .unwrap_or_else(|| tcx.def_span(local_id)),
            name: tcx.def_path_str(extern_id),
            extern_item_span: tcx.def_span(extern_id),
        })
    }

    #[track_caller]
    fn invalid_impl_block(&self) -> ErrorGuaranteed {
        self.inner
            .errors
            .emit(errors::InvalidImplBlock { span: self.block.span })
    }

    #[track_caller]
    fn cannot_resolve_trait_impl(&self) -> ErrorGuaranteed {
        self.inner
            .errors
            .emit(errors::CannotResolveTraitImpl { span: self.block.span })
    }

    #[track_caller]
    fn item_not_in_trait(
        &self,
        local_id: OwnerId,
        extern_id: DefId,
        extern_trait_id: DefId,
    ) -> ErrorGuaranteed {
        let tcx = self.tcx();
        self.inner.errors.emit(errors::ItemNotInTrait {
            span: self
                .tcx()
                .def_ident_span(local_id)
                .unwrap_or_else(|| tcx.def_span(local_id)),
            name: tcx.def_path_str(extern_id),
            extern_trait_span: tcx.def_span(extern_trait_id),
        })
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.inner.tcx
    }
}

mod errors {
    use flux_errors::E0999;
    use flux_macros::Diagnostic;
    use rustc_span::Span;

    #[derive(Diagnostic)]
    #[diag(driver_malformed_extern_spec, code = E0999)]
    pub(super) struct MalformedExternSpec {
        #[primary_span]
        span: Span,
    }

    impl MalformedExternSpec {
        pub(super) fn new(span: Span) -> Self {
            Self { span }
        }
    }

    #[derive(Diagnostic)]
    #[diag(driver_cannot_resolve_trait_impl, code = E0999)]
    #[note]
    pub(super) struct CannotResolveTraitImpl {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(driver_invalid_impl_block, code = E0999)]
    pub(super) struct InvalidImplBlock {
        #[primary_span]
        #[label]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(driver_item_not_in_trait_impl, code = E0999)]
    pub(super) struct ItemNotInTraitImpl {
        #[primary_span]
        #[label]
        pub span: Span,
        pub name: String,
        #[note]
        pub extern_impl_span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(driver_invalid_item_in_inherent_impl, code = E0999)]
    pub(super) struct InvalidItemInInherentImpl {
        #[primary_span]
        #[label]
        pub span: Span,
        pub name: String,
        #[note]
        pub extern_item_span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(driver_item_not_in_trait, code = E0999)]
    pub(super) struct ItemNotInTrait {
        #[primary_span]
        #[label]
        pub span: Span,
        pub name: String,
        #[note]
        pub extern_trait_span: Span,
    }
}
