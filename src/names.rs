use super::syntax::ast::{FnAnnots, HirRes, Ident, Name};
use super::syntax::mut_visit::MutVisitor;
use crate::context::{ErrorReported, LiquidRustCtxt};
pub use rustc_hir::intravisit::{self, Visitor as HirVisitor};
use rustc_hir::{self, Block, Body, Local, Param, PatKind};
use rustc_span::{MultiSpan, Symbol};
use std::collections::HashMap;
use std::hash::Hash;

pub fn resolve_hir_bindings(
    cx: &LiquidRustCtxt,
    annots: &mut Vec<FnAnnots>,
) -> Result<(), ErrorReported> {
    cx.track_errors(|| {
        for fn_annots in annots {
            let body = cx.hir().body(fn_annots.body_id);
            let mut vis = HirNameResolver {
                cx,
                fn_annots,
                env: Env::new(),
            };
            vis.visit_body(body);
        }
    })
}

struct Env<K, V> {
    stack: Vec<HashMap<K, V>>,
}

impl<K: Hash + Eq, V> Env<K, V> {
    fn new() -> Self {
        Env {
            stack: vec![HashMap::new()],
        }
    }

    fn push_frame(&mut self) {
        self.stack.push(HashMap::new());
    }

    fn pop_frame(&mut self) {
        self.stack.pop();
    }

    fn add_binding(&mut self, k: K, v: V) {
        let frame = self.stack.last_mut().expect("Empty Stack");
        frame.insert(k, v);
    }

    fn lookup(&self, k: &K) -> Option<&V> {
        for frame in self.stack.iter().rev() {
            if let Some(v) = frame.get(k) {
                return Some(v);
            }
        }
        None
    }
}

struct HirNameResolver<'a, 'tcx> {
    cx: &'a LiquidRustCtxt<'a, 'tcx>,
    fn_annots: &'a mut FnAnnots,
    env: Env<Symbol, HirRes>,
}

impl<'a, 'tcx> HirVisitor<'tcx> for HirNameResolver<'a, 'tcx> {
    type Map = rustc::hir::map::Map<'tcx>;

    fn nested_visit_map(&mut self) -> rustc_hir::intravisit::NestedVisitorMap<Self::Map> {
        intravisit::NestedVisitorMap::OnlyBodies(&self.cx.hir())
    }

    fn visit_body(&mut self, body: &'tcx Body<'tcx>) {
        if let Some(fn_typ) = &mut self.fn_annots.fn_ty {
            self.env.push_frame();
            let mut inputs = fn_typ.inputs.iter_mut();
            let mut params = body.params.iter();

            loop {
                match (inputs.next(), params.next()) {
                    (Some(ref mut refine), Some(Param { pat, .. })) => {
                        if let PatKind::Binding(_, hir_id, ident, None) = pat.kind {
                            if ident.name == refine.name.ident.name {
                                self.env
                                    .add_binding(ident.name, HirRes::Binding(hir_id, pat.span));
                                HirIdExprVisitor::new(self.cx, &self.env).visit_refine(refine);
                            } else {
                                lint_name_mismatch(self.cx, refine.name.ident, ident);
                            }
                        } else {
                            lint_pat_not_supported(self.cx, pat);
                        }
                    }

                    (Some(ref mut refine), None) => self
                        .cx
                        .span_lint(refine.span, "extra parameter in refinement"),

                    (None, Some(Param { span, .. })) => {
                        self.cx.span_lint(*span, "parameter without refinement")
                    }

                    (None, None) => break,
                }
            }
            let output = &mut fn_typ.output;
            self.env
                .add_binding(output.name.ident.name, HirRes::ReturnValue);
            HirIdExprVisitor::new(self.cx, &self.env).visit_refine(output);
            self.env.pop_frame();
        }
        for param in body.params {
            param.pat.each_binding(|_, hir_id, span, ident| {
                self.env
                    .add_binding(ident.name, HirRes::Binding(hir_id, span));
            })
        }
        intravisit::walk_body(self, body)
    }

    fn visit_block(&mut self, block: &'tcx Block<'tcx>) {
        self.env.push_frame();
        intravisit::walk_block(self, block);
        self.env.pop_frame();
    }

    fn visit_local(&mut self, local: &'tcx Local<'tcx>) {
        local.pat.each_binding(|_, hir_id, span, ident| {
            self.env
                .add_binding(ident.name, HirRes::Binding(hir_id, span));
        });
        let locals = &mut self.fn_annots.locals;
        if let Some(refine) = locals.get_mut(&local.hir_id) {
            // TODO: Add support for pattern matching
            if let PatKind::Binding(_, _, ident, None) = local.pat.kind {
                if ident.name == refine.name.ident.name {
                    HirIdExprVisitor::new(self.cx, &self.env).visit_refine(refine);
                } else {
                    lint_name_mismatch(self.cx, refine.name.ident, ident);
                }
            } else {
                lint_pat_not_supported(self.cx, local.pat);
            }
        }

        intravisit::walk_local(self, local);
    }
}

struct HirIdExprVisitor<'a, 'tcx> {
    cx: &'a LiquidRustCtxt<'a, 'tcx>,
    env: &'a Env<Symbol, HirRes>,
}

impl<'a, 'tcx> HirIdExprVisitor<'a, 'tcx> {
    fn new(cx: &'a LiquidRustCtxt<'a, 'tcx>, env: &'a Env<Symbol, HirRes>) -> Self {
        HirIdExprVisitor { cx, env }
    }
}

impl<'a, 'tcx> MutVisitor<'a> for HirIdExprVisitor<'a, 'tcx> {
    fn visit_name(&mut self, name: &mut Name) {
        if let Some(hir_res) = self.env.lookup(&name.ident.name) {
            name.hir_res = *hir_res;
        } else {
            lint_name_not_found(self.cx, name.ident);
        }
    }
}

fn lint_name_not_found(cx: &LiquidRustCtxt, ident: Ident) {
    cx.span_lint(
        ident.span,
        &format!("cannot find value {} in this scope", ident.name),
    );
}

fn lint_name_mismatch(cx: &LiquidRustCtxt, found: Ident, expected: Ident) {
    let mut span = MultiSpan::from_span(found.span);
    span.push_span_label(found.span, format!("found `{}`", found));
    span.push_span_label(expected.span, format!("expected `{}`", expected));
    cx.span_lint(span, "binding name mismatch");
}

fn lint_pat_not_supported(cx: &LiquidRustCtxt, pat: &rustc_hir::Pat) {
    cx.span_lint(
        pat.span,
        "pattern matching is not supported in refined local bindings yet",
    )
}
