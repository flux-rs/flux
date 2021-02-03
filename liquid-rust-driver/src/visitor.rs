use crate::lower::{Lower, LowerCtx};

use liquid_rust_core::ast::*;
use liquid_rust_parser::{parse_ty, ParseErrorKind};

use rustc_ast::ast::{AttrItem, AttrKind, Attribute};
use rustc_ast_pretty::pprust::tts_to_string;
use rustc_errors::{Diagnostic, Handler};
use rustc_hir::{
    def_id::DefId, itemlikevisit::ItemLikeVisitor, ForeignItem, ImplItem, Item, ItemKind, TraitItem,
};
use rustc_middle::ty::TyCtxt;
use rustc_span::{BytePos, Pos, Span};
use std::{collections::HashMap, ops::Range};

pub struct DefCollector<'tcx, 'vis> {
    tcx: TyCtxt<'tcx>,
    annotations: HashMap<DefId, FnTy>,
    handler: &'vis Handler,
    buffer: &'vis mut Vec<Diagnostic>,
}

impl<'tcx, 'vis> DefCollector<'tcx, 'vis> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        handler: &'vis Handler,
        buffer: &'vis mut Vec<Diagnostic>,
    ) -> Self {
        Self {
            tcx,
            annotations: HashMap::default(),
            buffer,
            handler,
        }
    }

    pub fn annotations(self) -> HashMap<DefId, FnTy> {
        self.annotations
    }

    fn buffer_error(&mut self, span: Span, msg: &str) {
        self.handler
            .struct_span_fatal(span, msg)
            .buffer(self.buffer);
    }

    fn extract_annotations(&mut self, attrs: &[Attribute]) -> Option<FnTy> {
        for attr in attrs {
            if let AttrKind::Normal(AttrItem { path, args, .. }, ..) = &attr.kind {
                let path = path
                    .segments
                    .iter()
                    .map(|segment| segment.ident.as_str())
                    .fold(String::new(), |acc, x| acc + "::" + &*x);

                if let "::liquid::ty" = path.as_str() {
                    let tokens = args.inner_tokens();

                    let input_span = tokens.span().unwrap();

                    let map_span = |span: Range<usize>| {
                        let lo = input_span.lo() + BytePos::from_usize(span.start + 1);
                        let hi = input_span.lo() + BytePos::from_usize(span.end + 1);
                        Span::new(lo, hi, input_span.ctxt())
                    };

                    let input = tts_to_string(&tokens);

                    let ast = match parse_ty(&input.trim_matches('"')) {
                        Ok(ast) => ast,
                        Err(err) => {
                            use ParseErrorKind::*;

                            let span = map_span(err.span);
                            let msg = match err.kind {
                                UnexpectedEOF => "Type annotation ended unexpectedly.".to_owned(),
                                UnexpectedToken(token) => {
                                    format!("Unexpected token `{}`.", token)
                                }
                                InvalidToken => "Invalid token".to_owned(),
                            };

                            self.buffer_error(span, &msg);

                            continue;
                        }
                    };

                    let mut lcx = LowerCtx::new();
                    let res = ast.lower(&mut lcx);

                    return Some(res);
                }
            }
        }
        None
    }
}

impl<'hir, 'tcx, 'vis> ItemLikeVisitor<'hir> for DefCollector<'tcx, 'vis> {
    fn visit_item(&mut self, item: &'hir Item<'hir>) {
        if let ItemKind::Fn(..) = item.kind {
            let def_id = self.tcx.hir().local_def_id(item.hir_id).to_def_id();

            if let Some(ty) = self.extract_annotations(item.attrs) {
                self.annotations.insert(def_id, ty);
            };
        }
    }

    fn visit_trait_item(&mut self, _trait_item: &'hir TraitItem<'hir>) {}
    fn visit_impl_item(&mut self, _impl_item: &'hir ImplItem<'hir>) {}
    fn visit_foreign_item(&mut self, _foreign_item: &'hir ForeignItem<'hir>) {}
}
