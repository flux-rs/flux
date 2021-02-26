use liquid_rust_parser::{parse_fn_decl, ParseErrorKind};

use rustc_ast::{AttrKind, Attribute};
use rustc_ast_pretty::pprust::tts_to_string;
use rustc_errors::{Diagnostic, Handler};
use rustc_hir::{
    def_id::DefId, itemlikevisit::ItemLikeVisitor, ForeignItem, ImplItem, Item, ItemKind, TraitItem,
};
use rustc_middle::ty::TyCtxt;
use rustc_span::{BytePos, Pos, Span};

pub(crate) struct Collector<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    handler: &'a Handler,
    diagnostics: &'a mut Vec<Diagnostic>,
}

impl<'tcx, 'a> Collector<'tcx, 'a> {
    fn new(tcx: TyCtxt<'tcx>, handler: &'a Handler, diagnostics: &'a mut Vec<Diagnostic>) -> Self {
        Self {
            tcx,
            handler,
            diagnostics,
        }
    }

    fn push_error(&mut self, message: &str, span: Span) {
        self.handler
            .struct_span_fatal(span, message)
            .buffer(self.diagnostics);
    }

    fn push_warning(&mut self, message: &str, span: Span) {
        self.handler
            .struct_span_warn(span, message)
            .buffer(self.diagnostics);
    }

    fn parse_annotations(&mut self, def_id: DefId, attributes: &[Attribute]) {
        let mut parsed_annotation = false;

        for attribute in attributes {
            if let AttrKind::Normal(attr_item, ..) = &attribute.kind {
                // Be sure we are in a `liquid` attribute.
                let segments = match attr_item.path.segments.as_slice() {
                    [first, segments @ ..] if first.ident.as_str() == "liquid" => segments,
                    _ => continue,
                };

                // Emit a warning if we already have an annotation for this item.
                if parsed_annotation {
                    self.push_warning("Ignoring duplicated annotation.", attr_item.span());
                }

                match segments {
                    [second] => match &*second.ident.as_str() {
                        "ty" => {
                            let tokens = attr_item.args.inner_tokens();
                            // FIXME: Is it possible to avoid this allocation?
                            let input = tts_to_string(&tokens);
                            let input_span = tokens.span().unwrap();

                            self.parse_ty_annotation(def_id, &input, input_span);

                            parsed_annotation = true;
                        }
                        _ => self.push_error("Invalid liquid annotation.", attr_item.span()),
                    },
                    _ => self.push_error("Invalid liquid annotation.", attr_item.span()),
                }
            }
        }
    }

    fn parse_ty_annotation(&mut self, _def_id: DefId, input: &str, input_span: Span) {
        match parse_fn_decl(&input.trim_matches('"')) {
            Ok(_fn_decl) => {
                // FIXME: lower the AST and store the types.
            }
            Err(err) => {
                // Turn the relative span of the parsing error into an absolute one.
                let lo = input_span.lo() + BytePos::from_usize(err.span.start + 1);
                let hi = input_span.lo() + BytePos::from_usize(err.span.end + 1);
                let span = Span::new(lo, hi, input_span.ctxt());

                use ParseErrorKind::*;
                let msg = match err.kind {
                    UnexpectedEOF => "Type annotation ended unexpectedly.",
                    UnexpectedToken(_token) => "Unexpected token.",
                };

                self.push_error(msg, span);
            }
        }
    }

    pub(crate) fn collect(
        tcx: TyCtxt<'tcx>,
        handler: &'a Handler,
        diagnostics: &'a mut Vec<Diagnostic>,
    ) {
        let mut collector = Self::new(tcx, handler, diagnostics);

        tcx.hir().krate().visit_all_item_likes(&mut collector);
    }
}

impl<'hir, 'tcx, 'a> ItemLikeVisitor<'hir> for Collector<'tcx, 'a> {
    fn visit_item(&mut self, item: &'hir Item<'hir>) {
        if let ItemKind::Fn(..) = item.kind {
            let def_id = self.tcx.hir().local_def_id(item.hir_id()).to_def_id();
            self.parse_annotations(def_id, item.attrs);
        }
    }

    fn visit_trait_item(&mut self, _trait_item: &'hir TraitItem<'hir>) {}
    fn visit_impl_item(&mut self, _impl_item: &'hir ImplItem<'hir>) {}
    fn visit_foreign_item(&mut self, _foreign_item: &'hir ForeignItem<'hir>) {}
}
