use liquid_rust_parser::{
    parse_ty,
    resolution::{solve_ty, ResolutionErrorKind},
    ParseErrorKind,
};
use liquid_rust_ty::Ty;

use rustc_ast::ast::{AttrItem, AttrKind, Attribute};
use rustc_ast_pretty::pprust::tts_to_string;
use rustc_errors::{Diagnostic, Handler};
use rustc_hir::{
    def_id::DefId, itemlikevisit::ItemLikeVisitor, ImplItem, Item, ItemKind, TraitItem,
};
use rustc_middle::ty::TyCtxt;
use rustc_span::{BytePos, Span};
use std::{collections::HashMap, ops::Range};

pub struct DefCollector<'tcx, 'vis> {
    tcx: TyCtxt<'tcx>,
    annotations: HashMap<DefId, Ty>,
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

    pub fn annotations(self) -> HashMap<DefId, Ty> {
        self.annotations
    }

    fn buffer_error(&mut self, span: Span, msg: &str) {
        self.handler
            .struct_span_fatal(span, msg)
            .buffer(self.buffer);
    }

    fn extract_annotations(&mut self, attrs: &[Attribute]) -> Option<Ty> {
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
                        let lo = input_span.lo() + BytePos(span.start as u32 + 1);
                        let hi = input_span.lo() + BytePos(span.end as u32 + 1);
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
                            };

                            self.buffer_error(span, &msg);

                            continue;
                        }
                    };

                    let ty = match solve_ty(&ast) {
                        Ok(ty) => ty,
                        Err(err) => {
                            use ResolutionErrorKind::*;

                            let span = map_span(err.span);
                            let msg = match err.kind {
                                        UnboundIdent(ident) => format!("Unbound identifier `{}`.", ident),
                                        InvalidUnaryOp(un_op, ty) => format!("Invalid unary operation `{:?}` for type `{:?}`.", un_op, ty),
                                        InvalidBinaryOp(bin_op, ty1, ty2) => format!("Invalid binary operation `{:?}` between types `{:?}` and `{:?}`.", bin_op, ty1, ty2),
                                        NonBoolPredicate => format!("Non-boolean predicate."),
                                        FuncArgument => format!("Using functions as arguments is not supported yet.")
                                    };

                            self.buffer_error(span, &msg);

                            continue;
                        }
                    };

                    return Some(ty);
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
}
