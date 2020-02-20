use super::syntax::ast::{BodyAnnots, HirRes, Ident, Name};
use super::syntax::mut_visit::MutVisitor;
use crate::context::{ErrorReported, LiquidRustCtxt};
pub use rustc_hir::intravisit::{self, Visitor as HirVisitor};
use rustc_hir::{self, Block, Body, HirId, Local, Param, PatKind};
use rustc_span::{MultiSpan, Symbol};
use std::collections::HashMap;

pub fn resolve_hir_bindings(
    cx: &LiquidRustCtxt,
    annots: &mut Vec<BodyAnnots>,
) -> Result<(), ErrorReported> {
    cx.track_errors(|| {
        for body_annots in annots {
            let body = cx.hir().body(body_annots.body_id);
            let mut vis = HirNameResolver {
                cx,
                body_annots,
                env: NameCtxt::new(),
            };
            vis.visit_body(body);
        }
    })
}

struct HirNameResolver<'a, 'lr, 'tcx> {
    cx: &'a LiquidRustCtxt<'lr, 'tcx>,
    body_annots: &'a mut BodyAnnots,
    env: NameCtxt,
}

impl<'tcx> HirVisitor<'tcx> for HirNameResolver<'_, '_, 'tcx> {
    type Map = rustc::hir::map::Map<'tcx>;

    fn nested_visit_map(&mut self) -> rustc_hir::intravisit::NestedVisitorMap<Self::Map> {
        intravisit::NestedVisitorMap::OnlyBodies(&self.cx.hir())
    }

    fn visit_body(&mut self, body: &'tcx Body<'tcx>) {
        if let Some(fn_typ) = &mut self.body_annots.fn_ty {
            self.env.push_frame();
            let mut inputs = fn_typ.inputs.iter_mut();
            let mut params = body.params.iter();
            let env = &mut self.env;
            loop {
                match (inputs.next(), params.next()) {
                    (Some(ref mut refine), Some(Param { pat, .. })) => {
                        pat.each_binding(|_, hir_id, _, ident| {
                            env.add_binding(ident.name, hir_id);
                        });
                        if let PatKind::Binding(_, hir_id, ident, None) = pat.kind {
                            if ident.name == refine.binding.name {
                                refine.hir_res = HirRes::Binding(hir_id);
                                HirIdExprVisitor::new(self.cx, env).visit_refine(refine);
                            } else {
                                lint_name_mismatch(self.cx, refine.binding, ident);
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
            output.hir_res = HirRes::ReturnValue;
            env.push_frame();
            env.add_ret_val(output.binding.name);
            HirIdExprVisitor::new(self.cx, env).visit_refine(output);
            env.pop_frame();
        }
        intravisit::walk_body(self, body)
    }

    fn visit_block(&mut self, block: &'tcx Block<'tcx>) {
        self.env.push_frame();
        intravisit::walk_block(self, block);
        self.env.pop_frame();
    }

    fn visit_local(&mut self, local: &'tcx Local<'tcx>) {
        local.pat.each_binding(|_, hir_id, _, ident| {
            self.env.add_binding(ident.name, hir_id);
        });
        let locals = &mut self.body_annots.locals;
        if let Some(refine) = locals.get_mut(&local.hir_id) {
            if let PatKind::Binding(_, hir_id, ident, None) = local.pat.kind {
                if ident.name == refine.binding.name {
                    refine.hir_res = HirRes::Binding(hir_id);
                    HirIdExprVisitor::new(self.cx, &self.env).visit_refine(refine);
                } else {
                    lint_name_mismatch(self.cx, refine.binding, ident);
                }
            } else {
                lint_pat_not_supported(self.cx, local.pat);
            }
        }
        intravisit::walk_local(self, local);
    }
}

struct HirIdExprVisitor<'a, 'lr, 'tcx> {
    cx: &'a LiquidRustCtxt<'lr, 'tcx>,
    env: &'a NameCtxt,
}

impl<'a, 'lr, 'tcx> HirIdExprVisitor<'a, 'lr, 'tcx> {
    fn new(cx: &'a LiquidRustCtxt<'lr, 'tcx>, env: &'a NameCtxt) -> Self {
        HirIdExprVisitor { cx, env }
    }
}

impl MutVisitor for HirIdExprVisitor<'_, '_, '_> {
    fn visit_name(&mut self, name: &mut Name) {
        if let Some(hir_res) = self.env.lookup(name.ident.name) {
            name.hir_res = hir_res;
        } else {
            lint_name_not_found(self.cx, name.ident);
        }
    }
}

struct NameCtxt {
    stack: Vec<HashMap<Symbol, HirRes>>,
}

impl NameCtxt {
    fn new() -> Self {
        NameCtxt {
            stack: vec![HashMap::new()],
        }
    }

    fn push_frame(&mut self) {
        self.stack.push(HashMap::new());
    }

    fn pop_frame(&mut self) {
        self.stack.pop();
    }

    fn add_binding(&mut self, name: Symbol, hir_id: HirId) {
        let frame = self.stack.last_mut().expect("Empty Stack");
        frame.insert(name, HirRes::Binding(hir_id));
    }

    fn add_ret_val(&mut self, name: Symbol) {
        let frame = self.stack.last_mut().expect("Empty Stack");
        frame.insert(name, HirRes::ReturnValue);
    }

    fn lookup(&self, name: Symbol) -> Option<HirRes> {
        for frame in self.stack.iter().rev() {
            if let Some(v) = frame.get(&name) {
                return Some(*v);
            }
        }
        None
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
