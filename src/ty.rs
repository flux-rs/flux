extern crate arena;
extern crate rustc_index;

use super::syntax::ast;
use crate::context::{ErrorReported, LiquidRustContext};
use arena::TypedArena;
use rustc::mir::{
    self,
    interpret::{LitToConstError, LitToConstInput},
};
use rustc::{
    bug,
    ty::{self, Ty},
};
use rustc_span::Span;
use std::collections::HashMap;

#[derive(Debug)]
pub enum Expr<'expr, 'tcx> {
    Unary(ast::UnOp, &'expr Expr<'expr, 'tcx>),
    Binary(
        &'expr Expr<'expr, 'tcx>,
        ast::BinOpKind,
        &'expr Expr<'expr, 'tcx>,
    ),
    Const(&'tcx ty::Const<'tcx>),
    Local(mir::Local),
}

pub fn build_tys<'a, 'tcx>(cx: &'a LiquidRustContext<'a, 'tcx>, fn_annots: &'tcx ast::FnAnnots) {
    let typeck_table = &HashMap::new();
    let mir = cx.optimized_mir(fn_annots.body_id);
    let span_to_local = &span_to_mir_local(mir);
    let mut builder = ExprBuilder {
        cx,
        typeck_table,
        span_to_local,
    };

    let mut local_decls = HashMap::new();
    for refine in fn_annots.locals.values() {
        local_decls.insert(
            builder.lookup(refine.name),
            builder.build_expr(&refine.pred),
        );
    }
    let mut inputs = Vec::new();
    let output: &Expr;
    if let Some(fn_ty) = &fn_annots.fn_ty {
        for refine in &fn_ty.inputs {
            let expr = builder.build_expr(&refine.pred);
            let local = builder.lookup(refine.name);
            local_decls.insert(local, expr);
            inputs.push(expr)
        }
        output = builder.build_expr(&fn_ty.output.pred);
        local_decls.insert(builder.lookup(fn_ty.output.name), output);
    } else {
        // for _ in 0..mir.arg_count {
        //     inputs.push(
        //         cx.expr_arena
        //             .alloc(Expr::Const(ty::Const::from_bool(*cx.tcx(), true))),
        //     );
        // }
        // output = cx
        //     .expr_arena
        //     .alloc(Expr::Const(ty::Const::from_bool(*cx.tcx(), true)));
    }
}

struct ExprBuilder<'a, 'lr, 'tcx> {
    cx: &'a LiquidRustContext<'lr, 'tcx>,
    typeck_table: &'a HashMap<ast::ExprId, ty::Ty<'tcx>>,
    span_to_local: &'a HashMap<Span, mir::Local>,
}

impl<'a, 'lr, 'tcx> ExprBuilder<'a, 'lr, 'tcx> {
    fn build_expr(&mut self, expr: &'tcx ast::Expr) -> &'lr Expr<'lr, 'tcx> {
        unimplemented!();
        // self.cx.expr_arena.alloc(self.build_expr_mut(expr))
    }

    fn build_expr_mut(&mut self, expr: &'tcx ast::Expr) -> Expr<'lr, 'tcx> {
        let ty = self.typeck_table[&expr.expr_id];
        match &expr.kind {
            ast::ExprKind::Binary(lhs_expr, op, rhs_expr) => Expr::Binary(
                self.build_expr(lhs_expr),
                op.kind,
                self.build_expr(rhs_expr),
            ),
            ast::ExprKind::Unary(op, expr) => Expr::Unary(*op, self.build_expr(expr)),
            ast::ExprKind::Name(name) => Expr::Local(self.lookup(*name)),
            ast::ExprKind::Lit(lit) => Expr::Const(self.lit_to_const(&lit.node, ty, expr.span)),
            ast::ExprKind::Err => bug!(),
        }
    }

    fn lit_to_const(
        &self,
        lit: &'tcx ast::LitKind,
        ty: Ty<'tcx>,
        sp: Span,
    ) -> &'tcx ty::Const<'tcx> {
        let neg = false;
        match self
            .cx
            .tcx()
            .at(sp)
            .lit_to_const(LitToConstInput { lit, ty, neg })
        {
            Ok(c) => c,
            Err(LitToConstError::UnparseableFloat) => {
                // FIXME(#31407) this is only necessary because float parsing is buggy
                self.cx
                    .span_lint(sp, "could not evaluate float literal (see issue #31407)");
                // create a dummy value and continue compiling
                ty::Const::from_bits(*self.cx.tcx(), 0, ty::ParamEnv::empty().and(ty))
            }
            Err(LitToConstError::Reported) => {
                // create a dummy value and continue compiling
                ty::Const::from_bits(*self.cx.tcx(), 0, ty::ParamEnv::empty().and(ty))
            }
        }
    }

    fn lookup(&mut self, name: ast::Name) -> mir::Local {
        match name.hir_res {
            ast::HirRes::Binding(_, span) => match self.span_to_local.get(&span) {
                Some(local) => *local,
                None => bug!("couldn't match name to mir local: {:?}", name),
            },
            ast::HirRes::ReturnValue => mir::RETURN_PLACE,
            ast::HirRes::Unresolved => bug!("identifiers must be resolved in the hir"),
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
