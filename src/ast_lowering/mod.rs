pub mod constant;

use super::refinements::{FnDecl, FnRefines, Refine, RefineCtxt};
use super::syntax::ast;
use super::wf::TypeckTable;
use crate::context::{ErrorReported, LiquidRustCtxt};
use rustc::bug;
use rustc::mir;
use rustc::mir::interpret::LitToConstError;
use rustc::mir::interpret::{ConstValue, Scalar};
use rustc::ty::{self, Ty};
use rustc_span::Span;
use std::collections::HashMap;

pub fn build_refines<'a, 'rcx, 'tcx>(
    cx: &'a LiquidRustCtxt<'a, 'tcx>,
    rcx: &'rcx RefineCtxt<'rcx, 'tcx>,
    annots: &Vec<ast::FnAnnots>,
    typeck_table: &TypeckTable<'tcx>,
) -> Result<Vec<FnRefines<'rcx, 'tcx>>, ErrorReported> {
    cx.track_errors(|| {
        let mut vec = Vec::new();
        for annot in annots {
            vec.push(build_fn_refines(cx, rcx, annot, typeck_table))
        }
        vec
    })
}

fn build_fn_refines<'a, 'rcx, 'tcx>(
    cx: &'a LiquidRustCtxt<'a, 'tcx>,
    rcx: &'rcx RefineCtxt<'rcx, 'tcx>,
    fn_annots: &ast::FnAnnots,
    typeck_table: &TypeckTable<'tcx>,
) -> FnRefines<'rcx, 'tcx> {
    let mir = cx.optimized_mir(fn_annots.body_id);
    let span_to_local = &span_to_mir_local(mir);
    let mut builder = RefineBuilder {
        cx,
        rcx,
        typeck_table,
        span_to_local,
    };

    let mut local_decls = HashMap::new();
    for refine in fn_annots.locals.values() {
        local_decls.insert(
            builder.lookup(refine.name).as_local().unwrap(),
            builder.build_refine(&refine.pred),
        );
    }

    let mut inputs = Vec::new();
    let output: &Refine;
    if let Some(fn_ty) = &fn_annots.fn_ty {
        for refine in &fn_ty.inputs {
            let expr = builder.build_refine(&refine.pred);
            let local = builder.lookup(refine.name).as_local().unwrap();
            local_decls.insert(local, expr);
            inputs.push(expr)
        }
        output = builder.build_refine(&fn_ty.output.pred);
        local_decls.insert(
            builder.lookup(fn_ty.output.name).as_local().unwrap(),
            output,
        );
    } else {
        for _ in 0..mir.arg_count {
            inputs.push(rcx.refine_true);
        }
        output = rcx.refine_true;
    }
    let fn_decl = FnDecl { inputs, output };

    FnRefines {
        body_id: fn_annots.body_id,
        fn_decl,
        local_decls,
    }
}

struct RefineBuilder<'a, 'b, 'rcx, 'tcx> {
    cx: &'a LiquidRustCtxt<'a, 'tcx>,
    rcx: &'rcx RefineCtxt<'rcx, 'tcx>,
    typeck_table: &'b HashMap<ast::ExprId, ty::Ty<'tcx>>,
    span_to_local: &'b HashMap<Span, mir::Local>,
}

impl<'a, 'b, 'rcx, 'tcx> RefineBuilder<'a, 'b, 'rcx, 'tcx> {
    fn build_refine(&mut self, expr: &ast::Expr) -> &'rcx Refine<'rcx, 'tcx> {
        let ty = self.typeck_table[&expr.expr_id];
        let rcx = self.rcx;
        match &expr.kind {
            ast::ExprKind::Binary(lhs_expr, op, rhs_expr) => rcx.mk_binary(
                self.build_refine(lhs_expr),
                op.kind,
                self.build_refine(rhs_expr),
            ),
            ast::ExprKind::Unary(op, expr) => rcx.mk_unary(op.kind, self.build_refine(expr)),
            ast::ExprKind::Name(name) => rcx.mk_place(self.lookup(*name)),
            ast::ExprKind::Lit(lit) => self.lit_to_constant(&lit.node, ty, expr.span),
            ast::ExprKind::Err => bug!(),
        }
    }

    fn lit_to_constant(
        &self,
        lit: &ast::LitKind,
        ty: Ty<'tcx>,
        sp: Span,
    ) -> &'rcx Refine<'rcx, 'tcx> {
        let tcx = *self.cx.tcx();
        let val = match constant::lit_to_const_value(tcx, lit, ty, false) {
            Ok(c) => c,
            Err(LitToConstError::UnparseableFloat) => {
                // FIXME(#31407) this is only necessary because float parsing is buggy
                self.cx
                    .span_lint(sp, "could not evaluate float literal (see issue #31407)");
                // create a dummy value and continue compiling
                ConstValue::Scalar(Scalar::from_u32(0))
            }
            Err(LitToConstError::Reported) => bug!(),
        };
        self.rcx.mk_constant(ty, val)
    }

    fn lookup(&mut self, name: ast::Name) -> mir::Place<'tcx> {
        let local = match name.hir_res {
            ast::HirRes::Binding(_, span) => match self.span_to_local.get(&span) {
                Some(local) => *local,
                None => bug!("couldn't match name to mir local: {:?}", name),
            },
            ast::HirRes::ReturnValue => mir::RETURN_PLACE,
            ast::HirRes::Unresolved => bug!("identifiers must be resolved in the hir"),
        };
        mir::Place {
            local,
            projection: ty::List::empty(),
        }
    }
}

fn span_to_mir_local(body: &mir::Body) -> HashMap<Span, mir::Local> {
    let mut map = HashMap::new();
    for var_info in &body.var_debug_info {
        map.insert(var_info.source_info.span, var_info.place.local);
    }
    map
}
