use liquid_rust_common::errors::ErrorReported;
use liquid_rust_syntax::{ast::FnSig, parse_fn_sig, ParseErrorKind};
use rustc_ast::{tokenstream::TokenStream, AttrKind, Attribute, MacArgs};
use rustc_hash::FxHashMap;
use rustc_hir::{
    def_id::LocalDefId, itemlikevisit::ItemLikeVisitor, ForeignItem, ImplItem, Item, ItemKind,
    TraitItem,
};
use rustc_middle::ty::TyCtxt;
use rustc_session::Session;
use rustc_span::Span;

pub(crate) struct SpecCollector<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    specs: FxHashMap<LocalDefId, FnSpec>,
    sess: &'a Session,
    error_reported: bool,
}

pub struct FnSpec {
    pub fn_sig: FnSig,
    pub assume: bool,
}

impl<'tcx, 'a> SpecCollector<'tcx, 'a> {
    pub(crate) fn collect(
        tcx: TyCtxt<'tcx>,
        sess: &'a Session,
    ) -> Result<FxHashMap<LocalDefId, FnSpec>, ErrorReported> {
        let mut collector = Self {
            tcx,
            sess,
            specs: FxHashMap::default(),
            error_reported: false,
        };

        tcx.hir().visit_all_item_likes(&mut collector);

        if collector.error_reported {
            Err(ErrorReported)
        } else {
            Ok(collector.specs)
        }
    }

    fn parse_annotations(&mut self, def_id: LocalDefId, attributes: &[Attribute]) {
        let mut fn_sig = None;
        let mut assume = false;
        for attribute in attributes {
            if let AttrKind::Normal(attr_item, ..) = &attribute.kind {
                // Be sure we are in a `liquid` attribute.
                let segments = match attr_item.path.segments.as_slice() {
                    [first, segments @ ..] if first.ident.as_str() == "lr" => segments,
                    _ => continue,
                };

                match segments {
                    [second] if &*second.ident.as_str() == "ty" => {
                        if fn_sig.is_some() {
                            self.emit_error("Duplicated function signature.", attr_item.span());
                            return;
                        }

                        if let MacArgs::Delimited(span, _, tokens) = &attr_item.args {
                            fn_sig = self.parse_fn_annot(tokens.clone(), span.entire());
                        } else {
                            self.emit_error("Invalid liquid annotation.", attr_item.span())
                        }
                    }
                    [second] if &*second.ident.as_str() == "assume" => {
                        assume = true;
                    }
                    _ => self.emit_error("Invalid liquid annotation.", attr_item.span()),
                }
            }
        }
        if let Some(fn_sig) = fn_sig {
            self.specs.insert(def_id, FnSpec { fn_sig, assume });
        }
    }

    fn parse_fn_annot(&mut self, tokens: TokenStream, input_span: Span) -> Option<FnSig> {
        match parse_fn_sig(tokens, input_span) {
            Ok(fn_sig) => Some(fn_sig),
            Err(err) => {
                let msg = match err.kind {
                    ParseErrorKind::UnexpectedEOF => "type annotation ended unexpectedly",
                    ParseErrorKind::UnexpectedToken => "unexpected token",
                    ParseErrorKind::IntTooLarge => "integer literal is too large",
                };

                self.emit_error(msg, err.span);
                None
            }
        }
    }

    fn emit_error(&mut self, message: &str, span: Span) {
        self.error_reported = true;
        self.sess.span_err(span, message);
    }
}

impl<'hir> ItemLikeVisitor<'hir> for SpecCollector<'_, '_> {
    fn visit_item(&mut self, item: &'hir Item<'hir>) {
        if let ItemKind::Fn(..) = item.kind {
            let hir_id = item.hir_id();
            let def_id = self.tcx.hir().local_def_id(hir_id);
            let attrs = self.tcx.hir().attrs(hir_id);
            self.parse_annotations(def_id, attrs);
        }
    }

    fn visit_trait_item(&mut self, _trait_item: &'hir TraitItem<'hir>) {}
    fn visit_impl_item(&mut self, _impl_item: &'hir ImplItem<'hir>) {}
    fn visit_foreign_item(&mut self, _foreign_item: &'hir ForeignItem<'hir>) {}
}
