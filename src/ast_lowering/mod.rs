pub mod constant;

use super::refinements::{BodyRefts, FunType, Pred, Var};
use super::syntax::ast;
use super::wf::TypeckTable;
use crate::context::{ErrorReported, LiquidRustCtxt};
use rustc::mir;
use rustc::mir::interpret::LitToConstError;
use rustc::mir::interpret::{ConstValue, Scalar};
use rustc::ty::{self, Ty};
use rustc_span::{Span, Symbol};
use std::collections::HashMap;

pub fn build_refts<'a, 'tcx>(
    cx: &LiquidRustCtxt<'a, 'tcx>,
    annots: &[ast::BodyAnnots],
    typeck_table: &TypeckTable<'tcx>,
) -> Result<Vec<BodyRefts<'a, 'tcx>>, ErrorReported> {
    cx.track_errors(|| {
        annots
            .iter()
            .map(|ba| build_body_refts(cx, ba, typeck_table))
            .collect::<Vec<_>>()
    })
}

fn build_body_refts<'a, 'tcx>(
    cx: &LiquidRustCtxt<'a, 'tcx>,
    body_annots: &ast::BodyAnnots,
    typeck_table: &TypeckTable<'tcx>,
) -> BodyRefts<'a, 'tcx> {
    let mir = cx.optimized_mir(body_annots.body_id);
    let mir_local_table = MirLocalTable::new(cx, mir);
    let builder = RefineBuilder::new(cx, typeck_table, &mir_local_table);

    let mut local_decls = HashMap::new();
    for refine in body_annots.locals.values() {
        let local = mir_local_table.lookup_hir_id(refine.hir_res.hir_id());
        local_decls.insert(local, builder.build_refine(&refine.pred, &[]));
    }

    let fun_type = if let Some(fun_type) = &body_annots.fn_ty {
        let fun_type = builder.build_fn_typ(fun_type);
        let mut locals = (0..mir.arg_count)
            .map(|i| mir::Local::from_usize(i + 1))
            .collect::<Vec<_>>();
        locals.push(mir::RETURN_PLACE);
        let opened = cx.open_fun_type_with_locals(fun_type, &locals);
        for (input, local) in opened.into_iter().zip(locals) {
            local_decls.insert(local, input);
        }
        Some(fun_type)
    } else {
        None
    };

    BodyRefts {
        body_id: body_annots.body_id,
        local_decls,
        fun_type,
    }
}

struct RefineBuilder<'a, 'b, 'tcx> {
    cx: &'b LiquidRustCtxt<'a, 'tcx>,
    typeck_table: &'b HashMap<ast::ExprId, ty::Ty<'tcx>>,
    mir_local_table: &'b MirLocalTable<'a, 'b, 'tcx>,
}

impl<'a, 'b, 'tcx> RefineBuilder<'a, 'b, 'tcx> {
    fn new(
        cx: &'b LiquidRustCtxt<'a, 'tcx>,
        typeck_table: &'b HashMap<ast::ExprId, ty::Ty<'tcx>>,
        mir_local_table: &'b MirLocalTable<'a, 'b, 'tcx>,
    ) -> Self {
        RefineBuilder {
            cx,
            typeck_table,
            mir_local_table,
        }
    }

    fn build_fn_typ(&self, fn_typ: &ast::FnType) -> FunType<'a, 'tcx> {
        let mut local_bindings = vec![];
        let inputs = fn_typ
            .inputs
            .iter()
            .map(|input| {
                local_bindings.push(input.binding.name);
                *self.build_refine(&input.pred, &local_bindings)
            })
            .collect::<Vec<_>>();
        local_bindings.push(fn_typ.output.binding.name);
        let output = self.build_refine(&fn_typ.output.pred, &local_bindings);
        self.cx.mk_fun_type(&inputs, output)
    }

    fn build_refine(&self, expr: &ast::Pred, local_bindings: &[Symbol]) -> &'a Pred<'a, 'tcx> {
        let ty = self.typeck_table[&expr.expr_id];
        match &expr.kind {
            ast::ExprKind::Binary(lhs_expr, op, rhs_expr) => self.cx.mk_binary(
                self.build_refine(lhs_expr, local_bindings),
                op.kind,
                self.build_refine(rhs_expr, local_bindings),
            ),
            ast::ExprKind::Unary(op, expr) => self
                .cx
                .mk_unary(op.kind, self.build_refine(expr, local_bindings)),
            ast::ExprKind::Name(name) => self
                .cx
                .mk_place_var(self.var_for_name(*name, local_bindings)),
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

    fn lit_to_constant(&self, lit: &ast::LitKind, ty: Ty<'tcx>, sp: Span) -> &'a Pred<'a, 'tcx> {
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
        self.cx.mk_constant(ty, val)
    }
}

struct MirLocalTable<'a, 'b, 'tcx> {
    cx: &'b LiquidRustCtxt<'a, 'tcx>,
    map: HashMap<Span, mir::Local>,
}

impl<'a, 'b, 'tcx> MirLocalTable<'a, 'b, 'tcx> {
    fn new(cx: &'b LiquidRustCtxt<'a, 'tcx>, mir: &'tcx mir::Body<'tcx>) -> Self {
        let mut map = HashMap::new();
        for var_info in &mir.var_debug_info {
            map.insert(var_info.source_info.span, var_info.place.local);
        }
        MirLocalTable { cx, map }
    }

    fn lookup_hir_id(&self, hir_id: rustc_hir::HirId) -> mir::Local {
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

    fn lookup_name(&self, name: ast::Name) -> mir::Local {
        match name.hir_res {
            ast::HirRes::Binding(hir_id) => self.lookup_hir_id(hir_id),
            ast::HirRes::ReturnValue => mir::RETURN_PLACE,
            ast::HirRes::Unresolved => bug!("identifiers must be resolved"),
        }
    }
}
