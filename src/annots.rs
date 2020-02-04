extern crate regex;

use super::syntax::ast::{AttrKind, AttrStyle, Attribute, FnAnnots};
use super::syntax::{err_msg, err_span, ParseError, ParsingCtxt};
use crate::context::{ErrorReported, LiquidRustCtxt};
use regex::Regex;
use rustc_hir::intravisit::{self, Visitor as HirVisitor};
use rustc_hir::{self, Crate, Item, ItemKind, Local};
use rustc_span::{MultiSpan, Span, Symbol};
use std::collections::HashMap;

pub fn collect<'a, 'lr>(
    cx: &'a LiquidRustCtxt<'a, 'lr>,
    krate: &'lr Crate<'lr>,
) -> Result<Vec<FnAnnots>, ErrorReported> {
    cx.track_errors(|| {
        let mut vis = AnnotsCollector::new(cx);
        krate.visit_all_item_likes(&mut vis.as_deep_visitor());
        let annots = vis.annots();
        annots
    })
}

struct AnnotsCollector<'a, 'lr> {
    cx: &'a LiquidRustCtxt<'a, 'lr>,
    annots: Vec<FnAnnots>,
    type_annot_regex: Regex,
    parsing: ParsingCtxt,
}

impl<'a, 'lr> AnnotsCollector<'a, 'lr> {
    fn new(cx: &'a LiquidRustCtxt<'a, 'lr>) -> Self {
        AnnotsCollector {
            cx: cx,
            annots: Vec::new(),
            type_annot_regex: Regex::new(r"^/\*\*@[^@]*@\*/$").unwrap(),
            parsing: ParsingCtxt::new(),
        }
    }

    fn extract_annots(&self, attrs: &[Attribute]) -> Vec<(Span, Symbol)> {
        attrs
            .iter()
            .filter_map(|attr| self.extract_annot(attr))
            .collect::<Vec<_>>()
    }

    fn extract_annot(&self, attr: &Attribute) -> Option<(Span, Symbol)> {
        let regex = &self.type_annot_regex;
        match *attr {
            Attribute {
                kind: AttrKind::DocComment(symbol),
                style: AttrStyle::Outer,
                span,
                ..
            } if regex.is_match(&symbol.as_str()) => Some((span, symbol)),
            _ => None,
        }
    }

    fn lint_multiple_annots(&self, annots: &[(Span, Symbol)]) {
        let spans: Vec<Span> = annots.iter().map(|(span, _)| *span).collect::<Vec<_>>();
        self.cx
            .span_lint(MultiSpan::from_spans(spans), "multiple annotations");
    }

    fn lint_parse_error<'input>(&self, err: &ParseError<'input>, span: Span) {
        self.cx
            .span_lint_label(err_span(err, span.lo(), span.ctxt()), &err_msg(err))
    }

    fn annots(self) -> Vec<FnAnnots> {
        self.annots
    }
}

// TODO: Collect annotations from trait impls and impls methods
impl<'a, 'lr> HirVisitor<'lr> for AnnotsCollector<'a, 'lr> {
    type Map = rustc::hir::map::Map<'lr>;

    fn nested_visit_map(&mut self) -> intravisit::NestedVisitorMap<Self::Map> {
        intravisit::NestedVisitorMap::OnlyBodies(&self.cx.hir())
    }

    fn visit_item(&mut self, item: &'lr Item<'lr>) {
        if let ItemKind::Fn(_, _, body_id) = item.kind {
            let annots = self.extract_annots(&item.attrs);
            let fn_ty = if let [(span, symbol)] = annots[..] {
                let symbol = &symbol.as_str();
                match self.parsing.parse_fn_annot(span, symbol) {
                    Ok(fn_ty) => Some(fn_ty),
                    Err(err) => {
                        self.lint_parse_error(&err, span);
                        None
                    }
                }
            } else {
                None
            };
            if annots.len() > 1 {
                self.lint_multiple_annots(&annots);
            }
            self.annots.push(FnAnnots {
                fn_ty,
                body_id: body_id,
                locals: HashMap::new(),
            });
            intravisit::walk_item(self, item);
        }
    }

    fn visit_local(&mut self, local: &'lr Local<'lr>) {
        let annots = self.extract_annots(&local.attrs);
        if annots.len() > 1 {
            self.lint_multiple_annots(&annots)
        } else if let [(span, symbol)] = annots[..] {
            let symbol = &symbol.as_str();
            let result = self.parsing.parse_local_annot(span, symbol);
            match result {
                Ok(refine) => {
                    let last = self.annots.last_mut().expect("no body visited");
                    last.locals.insert(local.hir_id, refine);
                }
                Err(err) => self.lint_parse_error(&err, span),
            }
        }
        rustc_hir::intravisit::walk_local(self, local);
    }
}
