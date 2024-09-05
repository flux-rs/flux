use flux_middle::rustc::lowering;
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

        let attrs = self.inner.parse_flux_attrs(item.owner_id.def_id)?;
        self.inner.report_dups(&attrs)?;

        match &item.kind {
            hir::ItemKind::Fn(..) => self.collect_extern_fn(item, attrs),
            hir::ItemKind::Enum(enum_def, _) => {
                self.collect_extern_enum(item.owner_id, enum_def, attrs)
            }
            hir::ItemKind::Struct(variant, _) => {
                self.collect_extern_struct(item.owner_id, variant, attrs)
            }
            hir::ItemKind::Trait(_, _, _, bounds, _) => {
                self.collect_extern_trait(item.owner_id, bounds, attrs)
            }
            hir::ItemKind::Impl(impl_) => self.collect_extern_impl(item.owner_id, impl_, attrs),
            _ => Err(self.malformed()),
        }
    }

    fn collect_extern_fn(&mut self, item: &hir::Item, attrs: FluxAttrs) -> Result {
        let fn_spec = self.inner.collect_fn_spec(item.owner_id, attrs)?;

        if fn_spec.fn_sig.is_none() {
            return Err(self.missing_fn_sig(item.owner_id));
        }

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

        let struct_def = self.inner.collect_struct_def(struct_id, attrs, variant)?;

        // We consider extern specs on a unit struct as opaque
        struct_def.opaque = variant.fields().len() == 0;

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

        let dummy_struct = self.item_at(1)?;
        self.inner.specs.insert_dummy(dummy_struct.owner_id);

        let mut extern_impl_id = None;
        for item in impl_.items {
            let new_impl_id = self.collect_extern_spec_impl_item(item)?;
            if *extern_impl_id.get_or_insert(new_impl_id) != new_impl_id {
                todo!()
            }
        }

        if let Some(extern_impl_id) = extern_impl_id {
            self.inner
                .specs
                .insert_extern_id(impl_id.def_id, extern_impl_id);
        }

        Ok(())
    }

    fn collect_extern_spec_impl_item(&mut self, item: &hir::ImplItemRef) -> Result<DefId> {
        let attrs = self.inner.parse_flux_attrs(item.id.owner_id.def_id)?;
        self.inner.report_dups(&attrs)?;

        match item.kind {
            hir::AssocItemKind::Fn { .. } => self.collect_extern_impl_fn(item, attrs),
            rustc_hir::AssocItemKind::Const | rustc_hir::AssocItemKind::Type => todo!(),
        }
    }

    fn collect_extern_impl_fn(
        &mut self,
        item: &hir::ImplItemRef,
        attrs: FluxAttrs,
    ) -> Result<DefId> {
        let fn_spec = self.inner.collect_fn_spec(item.id.owner_id, attrs)?;
        if fn_spec.fn_sig.is_none() {
            return Err(self.missing_fn_sig(item.id.owner_id));
        }

        let extern_id = self.extract_extern_id_from_impl_fn(item)?;
        self.inner
            .specs
            .insert_extern_id(item.id.owner_id.def_id, extern_id);

        self.tcx().impl_of_method(extern_id).ok_or_else(|| todo!())
    }

    fn collect_extern_trait(
        &mut self,
        trait_id: OwnerId,
        bounds: &hir::GenericBounds,
        attrs: FluxAttrs,
    ) -> Result {
        self.inner.collect_trait(trait_id, attrs)?;

        let extern_id = self.extract_extern_id_from_trait(bounds)?;
        self.inner
            .specs
            .insert_extern_id(trait_id.def_id, extern_id);

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
        let typeck_result = self.tcx().typeck(item.owner_id);
        if let hir::ItemKind::Fn(_, _, body_id) = item.kind
            && let hir::ExprKind::Block(b, _) = self.tcx().hir().body(body_id).value.kind
            && let Some(e) = b.expr
            && let hir::ExprKind::Call(callee, _) = e.kind
            && let hir::ExprKind::Path(qself) = &callee.kind
            && let hir::def::Res::Def(_, def_id) = typeck_result.qpath_res(qself, callee.hir_id)
        {
            Ok(def_id)
        } else {
            Err(self.malformed())
        }
    }

    fn extract_extern_id_from_impl_fn(&self, item: &hir::ImplItemRef) -> Result<DefId> {
        let typeck = self.tcx().typeck(item.id.owner_id);
        if let hir::ImplItemKind::Fn(_, body_id) = self.tcx().hir().impl_item(item.id).kind
            && let hir::ExprKind::Block(b, _) = self.tcx().hir().body(body_id).value.kind
            && let Some(e) = b.expr
            && let hir::ExprKind::Call(callee, _) = e.kind
            && let rustc_middle::ty::FnDef(callee_id, args) = typeck.node_type(callee.hir_id).kind()
        {
            let caller_id = item.id.owner_id.to_def_id();
            if self.tcx().trait_of_item(*callee_id).is_some() {
                self.resolve_trait_method(caller_id, *callee_id, args)
            } else {
                Ok(*callee_id)
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

    fn resolve_trait_method(
        &self,
        caller_id: DefId,
        callee_id: DefId,
        args: rustc_middle::ty::GenericArgsRef<'tcx>,
    ) -> Result<DefId> {
        lowering::resolve_call_from(self.tcx(), caller_id, callee_id, args)
            .map(|(resolved_id, _)| resolved_id)
            .ok_or_else(|| todo!())
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.inner.tcx
    }

    #[track_caller]
    fn item_at(&self, i: usize) -> Result<&'tcx hir::Item<'tcx>> {
        let stmts = self.block.stmts;
        let st = stmts
            .get(stmts.len() - i - 1)
            .ok_or_else(|| self.malformed())?;
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
    fn missing_fn_sig(&self, fn_id: OwnerId) -> ErrorGuaranteed {
        self.inner
            .errors
            .emit(errors::MissingFnSigForExternSpec::new(self.tcx().def_span(fn_id.def_id)))
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
    #[diag(driver_missing_fn_sig_for_extern_spec, code = E0999)]
    pub(super) struct MissingFnSigForExternSpec {
        #[primary_span]
        pub span: Span,
    }

    impl MissingFnSigForExternSpec {
        pub(super) fn new(span: Span) -> Self {
            Self { span }
        }
    }
}
