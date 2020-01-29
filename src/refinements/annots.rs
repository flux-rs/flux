extern crate regex;

use super::syntax::{err_msg, err_span, FnRefinesParser, LocalRefineParser, ParseError};
use crate::context::{ErrorReported, LiquidRustContext};
use crate::refinements::syntax::ast::{FnType, Refine};
use regex::Regex;
pub use rustc_hir::intravisit::{self, Visitor as HirVisitor};
use rustc_hir::{self, BodyId, Crate, HirId, Item, ItemKind, Local};
use rustc_span::{MultiSpan, Span, Symbol};
use std::collections::HashMap;
use syntax::ast::{AttrKind, AttrStyle, Attribute};

#[derive(Debug)]
pub struct FnAnnots {
    pub body_id: BodyId,
    pub fn_ty: Option<FnType>,
    pub locals: HashMap<HirId, Refine>,
}

pub fn collect<'a, 'tcx>(
    cx: &'a LiquidRustContext<'a, 'tcx>,
    krate: &'tcx Crate<'tcx>,
) -> Result<Vec<FnAnnots>, ErrorReported> {
    cx.track_errors(|| {
        let mut vis = RefinesCollector::new(cx);
        krate.visit_all_item_likes(&mut vis.as_deep_visitor());
        vis.annots()
    })
}

struct RefinesCollector<'a, 'tcx> {
    cx: &'a LiquidRustContext<'a, 'tcx>,
    annots: Vec<FnAnnots>,
    type_annot_regex: Regex,
    fn_annot_parser: FnRefinesParser,
    local_annot_parser: LocalRefineParser,
}

impl<'a, 'tcx> RefinesCollector<'a, 'tcx> {
    fn new(cx: &'a LiquidRustContext<'a, 'tcx>) -> Self {
        RefinesCollector {
            cx: cx,
            annots: Vec::new(),
            type_annot_regex: Regex::new(r"^/\*\*@[^@]*@\*/$").unwrap(),
            fn_annot_parser: FnRefinesParser::new(),
            local_annot_parser: LocalRefineParser::new(),
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
impl<'a, 'tcx> HirVisitor<'tcx> for RefinesCollector<'a, 'tcx> {
    type Map = rustc::hir::map::Map<'tcx>;

    fn nested_visit_map(&mut self) -> intravisit::NestedVisitorMap<Self::Map> {
        intravisit::NestedVisitorMap::OnlyBodies(&self.cx.hir())
    }

    fn visit_item(&mut self, item: &'tcx Item<'tcx>) {
        if let ItemKind::Fn(_, _, body_id) = item.kind {
            let annots = self.extract_annots(&item.attrs);
            let fn_ty = if let [(span, symbol)] = annots[..] {
                let symbol = &symbol.as_str();
                match self.fn_annot_parser.parse(span.lo(), span.ctxt(), symbol) {
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

    fn visit_local(&mut self, local: &'tcx Local<'tcx>) {
        let annots = self.extract_annots(&local.attrs);
        if annots.len() > 1 {
            self.lint_multiple_annots(&annots)
        } else if let [(span, symbol)] = annots[..] {
            let symbol = &symbol.as_str();
            let result = self
                .local_annot_parser
                .parse(span.lo(), span.ctxt(), symbol);
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
