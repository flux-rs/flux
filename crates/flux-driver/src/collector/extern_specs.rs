use rustc_hir as hir;
use rustc_hir::{def_id::DefId, BodyId, OwnerId};
use rustc_middle::ty::TyCtxt;
use rustc_span::ErrorGuaranteed;

use super::{FluxAttrs, SpecCollector};

type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

pub(super) struct ExternSpecCollector<'a, 'sess, 'tcx> {
    inner: &'a mut SpecCollector<'sess, 'tcx>,
    block: &'tcx hir::Block<'tcx>,
    idx: usize,
}

impl<'a, 'sess, 'tcx> ExternSpecCollector<'a, 'sess, 'tcx> {
    pub(super) fn collect(inner: &'a mut SpecCollector<'sess, 'tcx>, body_id: BodyId) -> Result {
        Self::new(inner, body_id)?.run()
    }

    fn new(inner: &'a mut SpecCollector<'sess, 'tcx>, body_id: BodyId) -> Result<Self> {
        let body = inner.tcx.hir().body(body_id);
        if let hir::ExprKind::Block(block, _) = body.value.kind {
            Ok(Self { inner, block, idx: block.stmts.len() })
        } else {
            Err(inner
                .errors
                .emit(errors::MalformedExternSpec::new(body.value.span)))
        }
    }

    fn run(mut self) -> Result {
        let item = self.pop_item()?;

        let attrs = self.inner.parse_flux_attrs(item.owner_id.def_id)?;
        self.inner.report_dups(&attrs)?;

        match &item.kind {
            hir::ItemKind::Fn(..) => self.collect_extern_spec_fn(item, attrs),
            hir::ItemKind::Enum(_, _) => todo!(),
            hir::ItemKind::Struct(variant, _) => {
                self.collect_extern_spec_struct(item.owner_id, variant, attrs)
            }
            hir::ItemKind::Trait(_, _, _, _, _) => todo!(),
            hir::ItemKind::Impl(_) => todo!(),
            _ => todo!(),
        }
    }

    fn collect_extern_spec_fn(&mut self, item: &hir::Item, attrs: FluxAttrs) -> Result {
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

    fn collect_extern_spec_struct(
        &mut self,
        struct_id: OwnerId,
        variant: &hir::VariantData,
        attrs: FluxAttrs,
    ) -> Result {
        self.inner.collect_struct_def(struct_id, attrs, variant)?;

        let item = self.pop_item()?;
        self.inner.specs.insert_dummy(item.owner_id.def_id);
        let extern_id = self.extract_extern_id_from_struct(item).unwrap();
        self.inner
            .specs
            .insert_extern_id(struct_id.def_id, extern_id);

        // If there are no fields, we consider the struct opaque
        let struct_def = self.inner.specs.structs.get_mut(&struct_id).unwrap();
        struct_def.opaque = variant.fields().len() == 0;

        Ok(())
    }

    fn collect_extern_spec_impl(&mut self, impl_: &hir::Impl) -> Result {
        Ok(())
    }

    fn extract_extern_id_from_struct(&mut self, item: &hir::Item) -> Result<DefId> {
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

    fn extract_extern_id_from_fn(&mut self, item: &hir::Item) -> Result<DefId> {
        // Regular functions
        if let hir::ItemKind::Fn(_, _, body_id) = &item.kind
            && let hir::Node::Expr(e) = self.tcx().hir_node(body_id.hir_id)
            && let hir::ExprKind::Block(b, _) = e.kind
            && let Some(e) = b.expr
            && let hir::ExprKind::Call(callee, _) = &e.kind
            && let hir::ExprKind::Path(qself) = &callee.kind
            && let typeck_result = self.tcx().typeck(item.owner_id)
            && let hir::def::Res::Def(_, def_id) = typeck_result.qpath_res(qself, callee.hir_id)
        {
            Ok(def_id)
        } else {
            Err(self.malformed())
        }
    }

    //     // impl functions
    //     if let hir::Node::ImplItem(i) = self.tcx.hir_node_by_def_id(def_id)
    //         && let hir::ImplItemKind::Fn(_, body_id) = &i.kind
    //         && let hir::Node::Expr(e) = self.tcx.hir_node(body_id.hir_id)
    //         && let hir::ExprKind::Block(b, _) = e.kind
    //         && let Some(e) = b.expr
    //         && let hir::ExprKind::Call(callee, _) = &e.kind
    //         && let hir::ExprKind::Path(qself) = &callee.kind
    //     {
    //         let typeck_result = self.tcx.typeck(def_id);

    //         if let rustc_middle::ty::FnDef(fn_def, args) =
    //             typeck_result.node_type(callee.hir_id).kind()
    //             && let Some((callee_id, _)) =
    //                 flux_middle::rustc::lowering::resolve_call_from(self.tcx, def_id, *fn_def, args)
    //         {
    //             return Ok(callee_id);
    //         }
    //         if let def::Res::Def(_, def_id) = typeck_result.qpath_res(qself, callee.hir_id) {
    //             return Ok(def_id);
    //         }
    //     }
    //     Err(self
    //         .errors
    //         .emit(errors::MalformedExternSpec { span: self.tcx.def_span(def_id) }))
    // }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.inner.tcx
    }

    fn pop_item(&mut self) -> Result<&'tcx hir::Item<'tcx>> {
        let st = self
            .block
            .stmts
            .get(self.idx - 1)
            .ok_or_else(|| self.malformed())?;
        self.idx -= 1;
        if let hir::StmtKind::Item(item_id) = st.kind {
            Ok(self.tcx().hir().item(item_id))
        } else {
            Err(self.malformed())
        }
    }

    fn malformed(&mut self) -> ErrorGuaranteed {
        self.inner
            .errors
            .emit(errors::MalformedExternSpec::new(self.block.span))
    }

    fn missing_fn_sig(&mut self, fn_id: OwnerId) -> ErrorGuaranteed {
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
