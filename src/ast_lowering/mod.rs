pub mod constant;

use super::refinements::{FnRefines, FnType, Place, Refine, Var};
use super::syntax::ast;
use super::wf::TypeckTable;
use crate::context::LiquidRustCtxt;
use rustc::mir;
use rustc::mir::interpret::LitToConstError;
use rustc::mir::interpret::{ConstValue, Scalar};
use rustc::ty::{self, Ty};
use rustc_span::{Span, Symbol};
use std::collections::HashMap;
use std::iter;

pub fn build_fn_refines<'a, 'tcx>(
    cx: &'a LiquidRustCtxt<'a, 'tcx>,
    fn_annots: &ast::FnAnnots,
    typeck_table: &TypeckTable<'tcx>,
) -> FnRefines<'tcx> {
    let mir = cx.optimized_mir(fn_annots.body_id);
    let mir_local_table = MirLocalTable::new(cx, mir);
    let builder = RefineBuilder::new(cx, typeck_table, &mir_local_table);

    let fn_ty = if let Some(fn_ty) = &fn_annots.fn_ty {
        builder.build_fn_typ(fn_ty)
    } else {
        let inputs = iter::repeat(cx.refine_true())
            .take(mir.arg_count)
            .collect::<Vec<_>>();
        let output = cx.refine_true();
        FnType { inputs, output }
    };

    let mut local_decls = HashMap::new();
    for refine in fn_annots.locals.values() {
        let local = mir_local_table.lookup_hir_id(refine.hir_res.hir_id());
        local_decls.insert(local, builder.build_refine(&refine.pred, &[]));
    }

    let mut locals = (0..mir.arg_count)
        .map(|i| mir::Local::from_usize(i + 1))
        .collect::<Vec<_>>();
    locals.push(mir::RETURN_PLACE);
    let opened = fn_ty.open(&locals);
    for (input, local) in opened.into_iter().zip(locals) {
        local_decls.insert(local, input);
    }

    FnRefines {
        body_id: fn_annots.body_id,
        fn_ty,
        local_decls,
    }
}

struct RefineBuilder<'a, 'b, 'tcx> {
    cx: &'a LiquidRustCtxt<'a, 'tcx>,
    typeck_table: &'b HashMap<ast::ExprId, ty::Ty<'tcx>>,
    mir_local_table: &'b MirLocalTable<'a, 'tcx>,
}

impl<'a, 'b, 'tcx> RefineBuilder<'a, 'b, 'tcx> {
    fn new(
        cx: &'a LiquidRustCtxt<'a, 'tcx>,
        typeck_table: &'b HashMap<ast::ExprId, ty::Ty<'tcx>>,
        mir_local_table: &'b MirLocalTable<'a, 'tcx>,
    ) -> Self {
        RefineBuilder {
            cx,
            typeck_table,
            mir_local_table,
        }
    }

    pub fn build_fn_typ(&self, fn_typ: &ast::FnType) -> FnType<'tcx> {
        let mut local_bindings = vec![];
        let inputs = fn_typ
            .inputs
            .iter()
            .map(|input| {
                local_bindings.push(input.binding.name);
                self.build_refine(&input.pred, &local_bindings)
            })
            .collect::<Vec<_>>();
        local_bindings.push(fn_typ.output.binding.name);
        let output = self.build_refine(&fn_typ.output.pred, &local_bindings);
        FnType { inputs, output }
    }

    pub fn build_refine(&self, expr: &ast::Expr, local_bindings: &[Symbol]) -> Refine<'tcx> {
        let ty = self.typeck_table[&expr.expr_id];
        match &expr.kind {
            ast::ExprKind::Binary(lhs_expr, op, rhs_expr) => Refine::Binary(
                box self.build_refine(lhs_expr, local_bindings),
                op.kind,
                box self.build_refine(rhs_expr, local_bindings),
            ),
            ast::ExprKind::Unary(op, expr) => {
                Refine::Unary(op.kind, box self.build_refine(expr, local_bindings))
            }
            ast::ExprKind::Name(name) => {
                Refine::Place(Place::from_var(self.var_for_name(*name, local_bindings)))
            }
            ast::ExprKind::Lit(lit) => self.lit_to_constant(&lit.node, ty, expr.span),
            ast::ExprKind::Err => bug!(),
        }
    }

    fn var_for_name(&self, name: ast::Name, local_bindings: &[Symbol]) -> Var {
        match name.hir_res {
            ast::HirRes::Binding(_) => {
                for (i, symb) in local_bindings.iter().rev().enumerate() {
                    if name.ident.name == *symb {
                        return Var::Bound(i);
                    }
                }
                Var::Free(self.mir_local_table.lookup_name(name))
            }
            ast::HirRes::ReturnValue => Var::nu(),
            ast::HirRes::Unresolved => bug!("identifiers must be resolved"),
        }
    }

    fn lit_to_constant(&self, lit: &ast::LitKind, ty: Ty<'tcx>, sp: Span) -> Refine<'tcx> {
        let tcx = self.cx.tcx();
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
        Refine::Constant(ty, val)
    }
}

struct MirLocalTable<'a, 'tcx> {
    cx: &'a LiquidRustCtxt<'a, 'tcx>,
    map: HashMap<Span, mir::Local>,
}

impl<'a, 'tcx> MirLocalTable<'a, 'tcx> {
    fn new(cx: &'a LiquidRustCtxt<'a, 'tcx>, mir: &'tcx mir::Body<'tcx>) -> Self {
        let mut map = HashMap::new();
        for var_info in &mir.var_debug_info {
            map.insert(var_info.source_info.span, var_info.place.local);
        }
        MirLocalTable { cx, map }
    }

    pub fn lookup_hir_id(&self, hir_id: rustc_hir::HirId) -> mir::Local {
        let node = self.cx.hir().get(hir_id);
        if_chain! {
            if let rustc_hir::Node::Binding(pat) = node;
            if let Some(local) = self.map.get(&pat.span);
            then {
                *local
            } else {
                bug!("couldn't match node to mir local:\n{:#?}", node)
            }
        }
    }

    pub fn lookup_name(&self, name: ast::Name) -> mir::Local {
        match name.hir_res {
            ast::HirRes::Binding(hir_id) => self.lookup_hir_id(hir_id),
            ast::HirRes::ReturnValue => mir::RETURN_PLACE,
            ast::HirRes::Unresolved => bug!("identifiers must be resolved"),
        }
    }
}
