use std::iter;

use flux_middle::ExternSpecMappingErr;
use flux_rustc_bridge::lowering;
use flux_syntax::surface;
use rustc_errors::Diagnostic;
use rustc_hir as hir;
use rustc_hir::{
    BodyId, OwnerId,
    def_id::{DefId, LocalDefId},
};
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::{ErrorGuaranteed, Span, symbol::kw};

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
        let body = inner.tcx.hir_body(body_id);
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
            hir::ItemKind::Fn { .. } => self.collect_extern_fn(item, attrs),
            hir::ItemKind::Enum(_, _, enum_def) => {
                self.collect_extern_enum(item.owner_id, enum_def, attrs)
            }
            hir::ItemKind::Struct(_, _, variant) => {
                self.collect_extern_struct(item.owner_id, variant, attrs)
            }
            hir::ItemKind::Trait(_, _, _, _, _, bounds, items) => {
                self.collect_extern_trait(item.owner_id, bounds, items, attrs)
            }
            hir::ItemKind::Impl(impl_) => self.collect_extern_impl(item.owner_id, impl_, attrs),
            _ => Err(self.malformed()),
        }
    }

    fn collect_extern_fn(&mut self, item: &hir::Item, mut attrs: FluxAttrs) -> Result {
        if attrs.has_attrs() {
            let mut sig = attrs.fn_sig();
            let no_panic_spec = attrs.no_panic_spec();
            if let Some(fn_sig) = &mut sig {
                fn_sig.no_panic = no_panic_spec;
            }
            self.inner.check_fn_sig_name(item.owner_id, sig.as_ref())?;
            let node_id = self.inner.next_node_id();
            self.inner.insert_item(
                item.owner_id,
                surface::Item {
                    attrs: attrs.into_attr_vec(),
                    kind: surface::ItemKind::Fn(sig),
                    node_id,
                },
            )?;
        }

        let extern_id = self.extract_extern_id_from_fn(item)?;
        self.insert_extern_id(item.owner_id.def_id, extern_id)?;
        self.check_generics(item.owner_id, extern_id)?;

        Ok(())
    }

    fn collect_extern_struct(
        &mut self,
        struct_id: OwnerId,
        variant: &hir::VariantData,
        attrs: FluxAttrs,
    ) -> Result {
        let dummy_struct = self.item_at(1)?;
        self.inner.specs.insert_dummy(dummy_struct.owner_id.def_id);

        let extern_id = self.extract_extern_id_from_struct(dummy_struct).unwrap();
        self.insert_extern_id(struct_id.def_id, extern_id)?;
        self.check_generics(struct_id, extern_id)?;

        if let Some(ctor_id) = variant.ctor_def_id() {
            self.inner.specs.insert_dummy(ctor_id);
        }

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
        self.inner.specs.insert_dummy(dummy_struct.owner_id.def_id);

        let extern_id = self.extract_extern_id_from_struct(dummy_struct).unwrap();
        self.insert_extern_id(enum_id.def_id, extern_id)?;
        self.check_generics(enum_id, extern_id)?;

        self.inner.collect_enum_def(enum_id, attrs, enum_def)?;

        // Add stuff about Ctor
        // Get the AdtDef for the enum
        let extern_enum_def = self.tcx().adt_def(extern_id);

        // Collect all constructor DefIds from variants
        let extern_variants = extern_enum_def.variants();
        let enum_variants = enum_def.variants;
        let extern_len = extern_variants.len();
        let enum_len = enum_variants.len();
        if extern_len != enum_len {
            let reason = format!("expected {extern_len:?} variants but only have {enum_len:?}");
            return Err(self.invalid_enum_extern_spec(reason));
        }
        for (extern_variant, variant) in extern_enum_def.variants().iter().zip(enum_def.variants) {
            if let Some(extern_ctor) = extern_variant.ctor_def_id()
                && let Some(ctor) = variant.data.ctor_def_id()
                && self.tcx().def_kind(extern_ctor) == self.tcx().def_kind(ctor)
            {
                self.insert_extern_id(ctor, extern_ctor)?;
            } else {
                let reason = format!(
                    "extern variant `{}` incompatible with specified `{}`",
                    extern_variant.ident(self.tcx()),
                    rustc_hir_pretty::id_to_string(&self.tcx(), variant.hir_id)
                );
                return Err(self.invalid_enum_extern_spec(reason));
            }
        }
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
        self.inner.specs.insert_dummy(dummy_item.owner_id.def_id);

        // If this is a trait impl compute the impl_id from the trait_ref
        let mut impl_of_trait = None;
        if let hir::ItemKind::Impl(dummy_impl) = &dummy_item.kind {
            impl_of_trait =
                Some(self.extract_extern_id_from_impl(dummy_item.owner_id, dummy_impl)?);

            self.inner
                .specs
                .insert_dummy(self.item_at(2)?.owner_id.def_id);
        }

        let mut extern_impl_id = impl_of_trait;
        for item_id in impl_.items {
            let item = self.tcx().hir_impl_item(*item_id);
            let extern_item = if let hir::ImplItemKind::Fn { .. } = item.kind {
                let attrs = self
                    .inner
                    .parse_attrs_and_report_dups(item_id.owner_id.def_id)?;
                self.collect_extern_impl_fn(impl_of_trait, item, attrs)?
            } else {
                continue;
            };

            if *extern_impl_id.get_or_insert(extern_item.impl_id) != extern_item.impl_id {
                return Err(self.invalid_impl_block());
            }
        }

        if let Some(extern_impl_id) = extern_impl_id {
            self.check_generics(impl_id, extern_impl_id)?;
            self.insert_extern_id(impl_id.def_id, extern_impl_id)?;
        }

        Ok(())
    }

    fn collect_extern_impl_fn(
        &mut self,
        impl_of_trait: Option<DefId>,
        item: &hir::ImplItem,
        mut attrs: FluxAttrs,
    ) -> Result<ExternImplItem> {
        if attrs.has_attrs() {
            let mut sig = attrs.fn_sig();
            let no_panic_spec = attrs.no_panic_spec();
            if let Some(fn_sig) = &mut sig {
                fn_sig.no_panic = no_panic_spec;
            }
            self.inner.check_fn_sig_name(item.owner_id, sig.as_ref())?;
            let node_id = self.inner.next_node_id();
            self.inner.insert_impl_item(
                item.owner_id,
                surface::ImplItemFn { attrs: attrs.into_attr_vec(), sig, node_id },
            )?;
        }

        let extern_impl_item = self.extract_extern_id_from_impl_fn(impl_of_trait, item)?;
        self.insert_extern_id(item.owner_id.def_id, extern_impl_item.item_id)?;
        self.check_generics(item.owner_id, extern_impl_item.item_id)?;

        Ok(extern_impl_item)
    }

    fn collect_extern_trait(
        &mut self,
        trait_id: OwnerId,
        bounds: &hir::GenericBounds,
        items: &[hir::TraitItemId],
        attrs: FluxAttrs,
    ) -> Result {
        self.inner.collect_trait(trait_id, attrs)?;

        let extern_trait_id = self.extract_extern_id_from_trait(bounds)?;
        self.insert_extern_id(trait_id.def_id, extern_trait_id)?;
        self.check_generics(trait_id, extern_trait_id)?;

        for item_id in items {
            let item = self.tcx().hir_trait_item(*item_id);
            if let hir::TraitItemKind::Fn { .. } = item.kind {
                let attrs = self
                    .inner
                    .parse_attrs_and_report_dups(item.owner_id.def_id)?;
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
        item: &hir::TraitItem,
        mut attrs: FluxAttrs,
    ) -> Result {
        let item_id = item.owner_id;
        if attrs.has_attrs() {
            let mut sig = attrs.fn_sig();
            let no_panic_spec = attrs.no_panic_spec();
            if let Some(fn_sig) = &mut sig {
                fn_sig.no_panic = no_panic_spec;
            }
            self.inner.check_fn_sig_name(item.owner_id, sig.as_ref())?;
            let node_id = self.inner.next_node_id();
            self.inner.insert_trait_item(
                item.owner_id,
                surface::TraitItemFn { attrs: attrs.into_attr_vec(), sig, node_id },
            )?;
        }

        let extern_fn_id = self.extract_extern_id_from_trait_fn(extern_trait_id, item)?;
        self.insert_extern_id(item.owner_id.def_id, extern_fn_id)?;
        self.check_generics(item_id, extern_fn_id)?;

        Ok(())
    }

    fn extract_extern_id_from_struct(&self, item: &hir::Item) -> Result<DefId> {
        if let hir::ItemKind::Struct(_, _, data) = item.kind
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
        if let hir::ItemKind::Fn { body, .. } = item.kind {
            self.extract_callee_from_body(body)
        } else {
            Err(self.malformed())
        }
    }

    fn extract_extern_id_from_impl_fn(
        &self,
        impl_of_trait: Option<DefId>,
        item: &hir::ImplItem,
    ) -> Result<ExternImplItem> {
        if let hir::ImplItemKind::Fn(_, body_id) = item.kind {
            let callee_id = self.extract_callee_from_body(body_id)?;
            if let Some(extern_impl_id) = impl_of_trait {
                let map = self.tcx().impl_item_implementor_ids(extern_impl_id);
                if let Some(extern_item_id) = map.get(&callee_id) {
                    Ok(ExternImplItem { impl_id: extern_impl_id, item_id: *extern_item_id })
                } else {
                    Err(self.item_not_in_trait_impl(item.owner_id, callee_id, extern_impl_id))
                }
            } else {
                let opt_extern_impl_id = self.tcx().impl_of_assoc(callee_id);
                if let Some(extern_impl_id) = opt_extern_impl_id {
                    debug_assert!(!self.tcx().impl_is_of_trait(extern_impl_id));
                    Ok(ExternImplItem { impl_id: extern_impl_id, item_id: callee_id })
                } else {
                    Err(self.invalid_item_in_inherent_impl(item.owner_id, callee_id))
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
        item: &hir::TraitItem,
    ) -> Result<DefId> {
        if let hir::TraitItemKind::Fn(_, trait_fn) = item.kind
            && let hir::TraitFn::Provided(body_id) = trait_fn
        {
            let callee_id = self.extract_callee_from_body(body_id)?;
            if let Some(callee_trait_id) = self.tcx().trait_of_assoc(callee_id)
                && trait_id == callee_trait_id
            {
                Ok(callee_id)
            } else {
                // I can't figure out how to trigger this via code generated with the extern spec
                // macro that also type checks but leaving it here as a precaution.
                Err(self.item_not_in_trait(item.owner_id, callee_id, trait_id))
            }
        } else {
            Err(self.malformed())
        }
    }

    fn extract_extern_id_from_impl(&self, impl_id: OwnerId, impl_: &hir::Impl) -> Result<DefId> {
        if let Some(item_id) = impl_.items.first()
            && let hir::ImplItemKind::Fn { .. } = self.tcx().hir_impl_item(*item_id).kind
            && let Some((clause, _)) = self
                .tcx()
                .predicates_of(item_id.owner_id.def_id)
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
        let owner = self.tcx().hir_body_owner_def_id(body_id);
        let typeck = self.tcx().typeck(owner);
        if let hir::ExprKind::Block(b, _) = self.tcx().hir_body(body_id).value.kind
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
            Ok(self.tcx().hir_item(item_id))
        } else {
            Err(self.malformed())
        }
    }

    fn insert_extern_id(&mut self, local_id: LocalDefId, extern_id: DefId) -> Result {
        self.inner
            .specs
            .insert_extern_spec_id_mapping(local_id, extern_id)
            .map_err(|err| {
                match err {
                    ExternSpecMappingErr::IsLocal(extern_id_local) => {
                        self.emit(errors::ExternSpecForLocalDef {
                            span: ident_or_def_span(self.tcx(), local_id),
                            local_def_span: ident_or_def_span(self.tcx(), extern_id_local),
                            name: self.tcx().def_path_str(extern_id),
                        })
                    }
                    ExternSpecMappingErr::Dup(previous_extern_spec) => {
                        self.emit(errors::DupExternSpec {
                            span: ident_or_def_span(self.tcx(), local_id),
                            previous_span: ident_or_def_span(self.tcx(), previous_extern_spec),
                            name: self.tcx().def_path_str(extern_id),
                        })
                    }
                }
            })
    }

    fn check_generics(&mut self, local_id: OwnerId, extern_id: DefId) -> Result {
        let tcx = self.tcx();
        let local_params = &tcx.generics_of(local_id).own_params;
        let extern_params = &tcx.generics_of(extern_id).own_params;

        let mismatch = 'mismatch: {
            if local_params.len() != extern_params.len() {
                break 'mismatch true;
            }
            for (local_param, extern_param) in iter::zip(local_params, extern_params) {
                if !cmp_generic_param_def(local_param, extern_param) {
                    break 'mismatch true;
                }
                // We skip the self parameter because its id is the same as the trait's id, which
                // has already been inserted.
                if local_param.name != kw::SelfUpper {
                    #[expect(clippy::disallowed_methods)]
                    self.insert_extern_id(local_param.def_id.expect_local(), extern_param.def_id)?;
                }
            }
            false
        };
        if mismatch {
            let local_hir_generics = tcx.hir_get_generics(local_id.def_id).unwrap();
            let span = local_hir_generics.span;
            Err(self.emit(errors::MismatchedGenerics {
                span,
                extern_def: tcx.def_span(extern_id),
                def_descr: tcx.def_descr(extern_id),
            }))
        } else {
            Ok(())
        }
    }

    #[track_caller]
    fn malformed(&self) -> ErrorGuaranteed {
        self.emit(errors::MalformedExternSpec::new(self.block.span))
    }

    #[track_caller]
    fn invalid_enum_extern_spec(&self, reason: String) -> ErrorGuaranteed {
        self.emit(errors::InvalidEnumExternSpec::new(self.block.span, reason))
    }

    #[track_caller]
    fn item_not_in_trait_impl(
        &self,
        local_id: OwnerId,
        extern_id: DefId,
        extern_impl_id: DefId,
    ) -> ErrorGuaranteed {
        let tcx = self.tcx();
        self.emit(errors::ItemNotInTraitImpl {
            span: ident_or_def_span(tcx, local_id),
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
        self.emit(errors::InvalidItemInInherentImpl {
            span: ident_or_def_span(tcx, local_id),
            name: tcx.def_path_str(extern_id),
            extern_item_span: tcx.def_span(extern_id),
        })
    }

    #[track_caller]
    fn invalid_impl_block(&self) -> ErrorGuaranteed {
        self.emit(errors::InvalidImplBlock { span: self.block.span })
    }

    #[track_caller]
    fn cannot_resolve_trait_impl(&self) -> ErrorGuaranteed {
        self.emit(errors::CannotResolveTraitImpl { span: self.block.span })
    }

    #[track_caller]
    fn item_not_in_trait(
        &self,
        local_id: OwnerId,
        extern_id: DefId,
        extern_trait_id: DefId,
    ) -> ErrorGuaranteed {
        let tcx = self.tcx();
        self.emit(errors::ItemNotInTrait {
            span: ident_or_def_span(tcx, local_id),
            name: tcx.def_path_str(extern_id),
            extern_trait_span: tcx.def_span(extern_trait_id),
        })
    }

    #[track_caller]
    fn emit<'b>(&'b self, err: impl Diagnostic<'b>) -> ErrorGuaranteed {
        self.inner.errors.emit(err)
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.inner.tcx
    }
}

fn cmp_generic_param_def(a: &ty::GenericParamDef, b: &ty::GenericParamDef) -> bool {
    if a.name != b.name {
        return false;
    }
    if a.index != b.index {
        return false;
    }
    matches!(
        (&a.kind, &b.kind),
        (ty::GenericParamDefKind::Lifetime, ty::GenericParamDefKind::Lifetime)
            | (ty::GenericParamDefKind::Type { .. }, ty::GenericParamDefKind::Type { .. })
            | (ty::GenericParamDefKind::Const { .. }, ty::GenericParamDefKind::Const { .. })
    )
}

fn ident_or_def_span(tcx: TyCtxt, def_id: impl Into<DefId>) -> Span {
    let def_id = def_id.into();
    tcx.def_ident_span(def_id)
        .unwrap_or_else(|| tcx.def_span(def_id))
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
    #[diag(driver_invalid_enum_extern_spec, code = E0999)]
    pub(super) struct InvalidEnumExternSpec {
        #[primary_span]
        span: Span,
        reason: String,
    }

    impl InvalidEnumExternSpec {
        pub(super) fn new(span: Span, reason: String) -> Self {
            Self { span, reason }
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

    #[derive(Diagnostic)]
    #[diag(driver_extern_spec_for_local_def, code = E0999)]
    pub(super) struct ExternSpecForLocalDef {
        #[primary_span]
        pub span: Span,
        #[help]
        pub local_def_span: Span,
        pub name: String,
    }

    #[derive(Diagnostic)]
    #[diag(driver_dup_extern_spec, code = E0999)]
    pub(super) struct DupExternSpec {
        #[primary_span]
        #[label]
        pub span: Span,
        #[note]
        pub previous_span: Span,
        pub name: String,
    }

    #[derive(Diagnostic)]
    #[diag(driver_mismatched_generics, code = E0999)]
    #[note]
    pub(super) struct MismatchedGenerics {
        #[primary_span]
        #[label]
        pub span: Span,
        #[label(driver_extern_def_label)]
        pub extern_def: Span,
        pub def_descr: &'static str,
    }
}
