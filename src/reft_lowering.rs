extern crate syntax as rust_syntax;

use super::refinements::{Binder, BodyRefts, Operand, Place, Pred, ReftType, Scalar, Var};
use super::syntax::ast;
use super::wf::ReftTypeckTable;
use crate::context::{ErrorReported, LiquidRustCtxt};
use rust_syntax::ast::FloatTy;
use rustc::mir;
use rustc::mir::interpret::truncate;
use rustc::mir::interpret::LitToConstError;
use rustc::ty::{self, Ty};
use rustc_span::{Span, Symbol};
use std::collections::HashMap;

pub fn build_refts<'lr, 'tcx>(
    cx: &LiquidRustCtxt<'lr, 'tcx>,
    annots: &[ast::BodyAnnots],
    reft_table: &ReftTypeckTable<'tcx>,
) -> Result<Vec<BodyRefts<'lr, 'tcx>>, ErrorReported> {
    cx.track_errors(|| {
        annots
            .iter()
            .map(|ba| build_body_refts(cx, ba, reft_table))
            .collect::<Vec<_>>()
    })
}

fn build_body_refts<'lr, 'tcx>(
    cx: &LiquidRustCtxt<'lr, 'tcx>,
    body_annots: &ast::BodyAnnots,
    reft_table: &ReftTypeckTable<'tcx>,
) -> BodyRefts<'lr, 'tcx> {
    let def_id = cx.hir().body_owner_def_id(body_annots.body_id);
    let tables = cx.tcx().typeck_tables_of(def_id);
    let hir_id = cx.hir().as_local_hir_id(def_id).unwrap();
    let ret_ty = tables.liberated_fn_sigs()[hir_id].output();
    let mir = cx.optimized_mir(body_annots.body_id);
    let mir_local_table = MirLocalTable::new(cx, mir);
    let builder = RefineBuilder::new(cx, reft_table, tables, ret_ty, &mir_local_table);

    let mut local_decls = HashMap::new();
    for refine in body_annots.locals.values() {
        let local = mir_local_table.lookup_hir_id(refine.hir_res.hir_id());
        local_decls.insert(local, builder.build_reft(refine, &[]));
    }

    let fun_type = if let Some(fun_type) = &body_annots.fn_ty {
        let fun_type = builder.build_fun_type(fun_type);
        let locals = (0..mir.arg_count)
            .map(|i| mir::Local::from_usize(i + 1))
            .collect::<Vec<_>>();
        let (inputs, output) = cx.split_fun_type(fun_type, &Operand::from_locals(&locals));
        for (input, local) in inputs.into_iter().zip(locals) {
            local_decls.insert(local, input);
        }
        local_decls.insert(mir::RETURN_PLACE, output);
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

struct RefineBuilder<'a, 'lr, 'tcx> {
    cx: &'a LiquidRustCtxt<'lr, 'tcx>,
    reft_table: &'a HashMap<ast::ExprId, ty::Ty<'tcx>>,
    tables: &'a ty::TypeckTables<'tcx>,
    ret_ty: Ty<'tcx>,
    mir_local_table: &'a MirLocalTable<'a, 'lr, 'tcx>,
}

impl<'a, 'lr, 'tcx> RefineBuilder<'a, 'lr, 'tcx> {
    fn new(
        cx: &'a LiquidRustCtxt<'lr, 'tcx>,
        reft_table: &'a HashMap<ast::ExprId, ty::Ty<'tcx>>,
        tables: &'a ty::TypeckTables<'tcx>,
        ret_ty: Ty<'tcx>,
        mir_local_table: &'a MirLocalTable<'a, 'lr, 'tcx>,
    ) -> Self {
        RefineBuilder {
            cx,
            reft_table,
            tables,
            ret_ty,
            mir_local_table,
        }
    }

    fn build_fun_type(&self, fn_typ: &ast::FnType) -> Binder<&'lr ReftType<'lr, 'tcx>> {
        let mut bindings = vec![];
        let inputs = fn_typ
            .inputs
            .iter()
            .map(|input| {
                let reft = self.build_reft(input, &bindings);
                bindings.push(input.binding.name);
                *reft.skip_binder()
            })
            .collect::<Vec<_>>();
        let output = *self.build_reft(&fn_typ.output, &bindings).skip_binder();
        Binder::bind(self.cx.mk_fun_type(inputs, output))
    }

    fn build_reft(
        &self,
        reft: &ast::Reft,
        bindings: &[Symbol],
    ) -> Binder<&'lr ReftType<'lr, 'tcx>> {
        let mut bindings = bindings.to_vec();
        bindings.push(reft.binding.name);
        let pred = self.build_pred(&reft.pred, &bindings);
        Binder::bind(self.cx.mk_reft(self.ty_for_reft(reft), pred))
    }

    fn ty_for_reft(&self, reft: &ast::Reft) -> Ty<'tcx> {
        match reft.hir_res {
            ast::HirRes::Binding(hir_id) => self.tables.node_type(hir_id),
            ast::HirRes::ReturnValue => self.ret_ty,
            ast::HirRes::Unresolved => bug!("names must be resolved"),
        }
    }

    fn build_pred(&self, expr: &ast::Pred, bindings: &[Symbol]) -> &'lr Pred<'lr, 'tcx> {
        let ty = self.reft_table[&expr.expr_id];
        match &expr.kind {
            ast::ExprKind::Binary(lhs_expr, op, rhs_expr) => self.cx.mk_binary(
                self.build_pred(lhs_expr, bindings),
                op.kind,
                self.build_pred(rhs_expr, bindings),
            ),
            ast::ExprKind::Unary(op, expr) => {
                self.cx.mk_unary(op.kind, self.build_pred(expr, bindings))
            }
            ast::ExprKind::Name(name) => self.cx.mk_operand(Operand::Place(Place::from_var(
                self.var_for_name(*name, bindings),
            ))),
            ast::ExprKind::Lit(lit) => self.lit_to_constant(&lit.kind, ty, expr.span),
            ast::ExprKind::Err => bug!(),
        }
    }

    fn var_for_name(&self, name: ast::Name, bindings: &[Symbol]) -> Var {
        match name.hir_res {
            ast::HirRes::Binding(_) => {
                for (i, symb) in bindings.iter().rev().enumerate() {
                    if name.ident.name == *symb {
                        return Var::Bound(i);
                    }
                }
                Var::Local(self.mir_local_table.lookup_name(name))
            }
            ast::HirRes::ReturnValue => Var::nu(),
            ast::HirRes::Unresolved => bug!("identifiers must be resolved"),
        }
    }

    fn lit_to_constant(&self, lit: &ast::LitKind, ty: Ty<'tcx>, sp: Span) -> &'lr Pred<'lr, 'tcx> {
        let scalar = match self.lit_to_scalar(lit, ty, false) {
            Ok(c) => c,
            Err(LitToConstError::UnparseableFloat) => {
                // FIXME(#31407) this is only necessary because float parsing is buggy
                self.cx
                    .span_lint(sp, "could not evaluate float literal (see issue #31407)");
                // create a dummy value and continue compiling
                Scalar::from_bool(true)
            }
            Err(LitToConstError::Reported) => bug!(),
        };
        self.cx.mk_operand(Operand::Constant(ty, scalar))
    }

    pub fn lit_to_scalar(
        &self,
        lit: &ast::LitKind,
        ty: ty::Ty<'tcx>,
        neg: bool,
    ) -> Result<Scalar, LitToConstError> {
        let trunc = |n| {
            let param_ty = ty::ParamEnv::reveal_all().and(ty);
            let width = self
                .cx
                .tcx()
                .layout_of(param_ty)
                .map_err(|_| LitToConstError::Reported)?
                .size;
            let result = truncate(n, width);
            Ok(Scalar::from_uint(result, width))
        };

        let lit = match *lit {
            ast::LitKind::Int(n, _) if neg => {
                let n = n as i128;
                let n = n.overflowing_neg().0;
                trunc(n as u128)?
            }
            ast::LitKind::Int(n, _) => trunc(n)?,
            ast::LitKind::Float(n, _) => {
                let fty = match ty.kind {
                    ty::Float(fty) => fty,
                    _ => bug!(),
                };
                parse_float(n, fty, neg).map_err(|_| LitToConstError::UnparseableFloat)?
            }
            ast::LitKind::Bool(b) => Scalar::from_bool(b),
            ast::LitKind::Err => return Err(LitToConstError::Reported),
        };
        Ok(lit)
    }
}

struct MirLocalTable<'a, 'lr, 'tcx> {
    cx: &'a LiquidRustCtxt<'lr, 'tcx>,
    map: HashMap<Span, mir::Local>,
}

impl<'a, 'lr, 'tcx> MirLocalTable<'a, 'lr, 'tcx> {
    fn new(cx: &'a LiquidRustCtxt<'lr, 'tcx>, mir: &'tcx mir::Body<'tcx>) -> Self {
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

fn parse_float(num: Symbol, fty: FloatTy, neg: bool) -> Result<Scalar, ()> {
    let num = num.as_str();
    use rustc_apfloat::ieee::{Double, Single};
    let scalar = match fty {
        FloatTy::F32 => {
            num.parse::<f32>().map_err(|_| ())?;
            let mut f = num.parse::<Single>().unwrap_or_else(|e| {
                panic!("apfloat::ieee::Single failed to parse `{}`: {:?}", num, e)
            });
            if neg {
                f = -f;
            }
            Scalar::from_f32(f)
        }
        FloatTy::F64 => {
            num.parse::<f64>().map_err(|_| ())?;
            let mut f = num.parse::<Double>().unwrap_or_else(|e| {
                panic!("apfloat::ieee::Double failed to parse `{}`: {:?}", num, e)
            });
            if neg {
                f = -f;
            }
            Scalar::from_f64(f)
        }
    };
    Ok(scalar)
}
