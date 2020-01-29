extern crate rustc_index;

use crate::context::{ErrorReported, LiquidRustContext};
use crate::refinements::syntax::ast::*;
use rustc::mir::{Local, LocalDecl};
use rustc::ty::{self, InferTy, IntVid, Ty, TyKind};
use rustc_index::vec::IndexVec;
use rustc_span::MultiSpan;
use std::cell::Cell;
use std::ops::Deref;
use syntax::ast::IntTy;

pub fn check_fn_ty<'a, 'tcx>(
    cx: &'a LiquidRustContext<'a, 'tcx>,
    fn_ty: &FnType,
    local_decls: &'tcx IndexVec<Local, LocalDecl<'tcx>>,
) -> Result<(), ErrorReported> {
    let mut res = Ok(());
    for input in &fn_ty.inputs {
        res = res.and(check_refine(cx, input, local_decls));
    }
    res = res.and(check_refine(cx, &fn_ty.output, local_decls));
    res
}

pub fn check_refine<'a, 'tcx>(
    cx: &'a LiquidRustContext<'a, 'tcx>,
    refine: &Refine,
    local_decls: &'tcx IndexVec<Local, LocalDecl<'tcx>>,
) -> Result<(), ErrorReported> {
    cx.track_errors(|| {
        let checker = TypeChecker::new(cx, local_decls);
        let ty = checker.infer_type(&refine.pred);
        if ty.kind != TyKind::Bool && ty.kind != TyKind::Error {
            lint_malformed_refinement(cx, refine, ty);
        }
    })
}

struct TypeChecker<'a, 'tcx> {
    cx: &'a LiquidRustContext<'a, 'tcx>,
    local_decls: &'tcx IndexVec<Local, LocalDecl<'tcx>>,
    next_int_var_id: Cell<u32>,
}

impl<'a, 'tcx> TypeChecker<'a, 'tcx> {
    pub fn new(
        cx: &'a LiquidRustContext<'a, 'tcx>,
        local_decls: &'tcx IndexVec<Local, LocalDecl<'tcx>>,
    ) -> Self {
        Self {
            cx,
            local_decls,
            next_int_var_id: Cell::new(0),
        }
    }
    fn lookup(&self, ident: Ident) -> Ty<'tcx> {
        let local = ident
            .mir_local
            .expect("identifiers must be resolved in the mir");
        self.local_decls[local].ty
    }

    fn next_int_var_id(&self) -> IntVid {
        let index = self.next_int_var_id.get();
        self.next_int_var_id.set(index + 1);
        IntVid { index }
    }

    fn next_int_var(&self) -> Ty<'tcx> {
        self.mk_int_var(self.next_int_var_id())
    }

    pub fn infer_type(&self, expr: &Expr) -> Ty<'tcx> {
        match &expr.kind {
            ExprKind::True | ExprKind::False => self.mk_bool(),
            ExprKind::Int(_) => self.next_int_var(),
            ExprKind::Binary(e1, op, e2) => self.infer_bin_op(e1, *op, e2),
            ExprKind::Ident(ident) => self.lookup(*ident),
            ExprKind::Unary(op, e) => self.infer_un_op(*op, e),
        }
    }

    fn infer_un_op(&self, op: UnOp, e: &Expr) -> Ty<'tcx> {
        let ty = self.infer_type(e);
        if ty.kind == TyKind::Error {
            return ty;
        }

        match (op.kind, &ty.kind) {
            (UnOpKind::Deref, TyKind::Ref(_, ty, _)) => ty,
            (UnOpKind::Not, TyKind::Bool) => ty,
            _ => {
                lint_un_op_err(self.cx, op, e, ty);
                self.mk_ty(TyKind::Error)
            }
        }
    }

    fn infer_bin_op(&self, e1: &Expr, op: BinOp, e2: &Expr) -> Ty<'tcx> {
        let ty1 = self.infer_type(e1);
        let ty2 = self.infer_type(e2);
        if ty1.kind == TyKind::Error || ty2.kind == TyKind::Error {
            return ty1;
        }

        match op.kind {
            BinOpKind::Lt | BinOpKind::Gt => match self.unify(ty1, ty2) {
                Some(ty) if ty.is_numeric() => self.mk_bool(),
                _ => {
                    lint_bin_op_err(self.cx, op, e1, ty1, e2, ty2);
                    self.mk_ty(TyKind::Error)
                }
            },

            BinOpKind::Mul | BinOpKind::Div | BinOpKind::Add | BinOpKind::Sub => {
                match self.unify(ty1, ty2) {
                    Some(ty) if ty.is_numeric() => ty,
                    _ => {
                        lint_bin_op_err(self.cx, op, e1, ty1, e2, ty2);
                        self.mk_ty(TyKind::Error)
                    }
                }
            }

            BinOpKind::And | BinOpKind::Or => {
                lint_expected_found(self.cx, e1, self.mk_bool(), ty1);
                lint_expected_found(self.cx, e2, self.mk_bool(), ty2);
                if ty1.is_bool() && ty2.is_bool() {
                    self.mk_bool()
                } else {
                    self.mk_ty(TyKind::Error)
                }
            }
        }
    }

    fn unify(&self, ty1: Ty<'tcx>, ty2: Ty<'tcx>) -> Option<Ty<'tcx>> {
        let both_integral = ty1.is_integral() && ty2.is_integral();
        let both_floating = ty1.is_floating_point() && ty2.is_floating_point();
        if ty1 == ty2 {
            Some(ty1)
        } else if both_integral || both_floating {
            if ty1.is_ty_infer() {
                Some(ty2)
            } else if ty2.is_ty_infer() {
                Some(ty1)
            } else {
                None
            }
        } else {
            None
        }
    }
}

fn lint_malformed_refinement(cx: &LiquidRustContext, refine: &Refine, ty: Ty) {
    let mut mspan = MultiSpan::from_span(refine.pred.span);
    mspan.push_span_label(
        refine.pred.span,
        format!("expected `bool`, found `{:?}`", ty),
    );
    cx.span_lint(mspan, "refinement predicate must be of type `bool`");
}

fn lint_expected_found(cx: &LiquidRustContext, e: &Expr, expected: Ty, found: Ty) {
    if expected == found {
        return;
    }
    let mut spans = MultiSpan::from_span(e.span);
    spans.push_span_label(
        e.span,
        format!("expected `{:?}`, found `{:?}`", expected, found),
    );
    cx.span_lint(spans, "mismatched types")
}

fn lint_un_op_err(cx: &LiquidRustContext, op: UnOp, e: &Expr, ty: Ty) {
    cx.span_lint_label(op.span.to(e.span), &un_op_err_msg(op, ty));
}

fn lint_bin_op_err<'tcx>(
    cx: &LiquidRustContext,
    op: BinOp,
    e1: &Expr,
    ty1: Ty<'tcx>,
    e2: &Expr,
    ty2: Ty<'tcx>,
) {
    let mut mspan = MultiSpan::from_span(op.span);
    mspan.push_span_label(e1.span, format!("{:?}", ty1));
    mspan.push_span_label(e2.span, format!("{:?}", ty2));
    cx.span_lint(mspan, &bin_op_err_msg(ty1, op, ty2));
}

fn un_op_err_msg<'tcx>(op: UnOp, ty: Ty<'tcx>) -> String {
    match op.kind {
        UnOpKind::Deref => format!("type `{:?}` cannot be dereferenced", ty),
        UnOpKind::Not => format!("cannot apply unary operator `!` to type `{:?}`", ty),
    }
}

fn bin_op_err_msg<'tcx>(ty1: Ty<'tcx>, op: BinOp, ty2: Ty<'tcx>) -> String {
    match op.kind {
        BinOpKind::And | BinOpKind::Or => "mismatched types".into(),
        BinOpKind::Lt | BinOpKind::Gt => format!("cannot compare `{:?}` with `{:?}`", ty1, ty2),
        BinOpKind::Mul => format!("cannot multiply `{:?}` to `{:?}`", ty2, ty1),
        BinOpKind::Div => format!("cannot divide `{:?}` by `{:?}`", ty1, ty2),
        BinOpKind::Add => format!("cannot add `{:?}` to `{:?}`", ty1, ty2),
        BinOpKind::Sub => format!("cannot subtract `{:?}` and `{:?}`", ty2, ty1),
    }
}

impl<'a, 'tcx> Deref for TypeChecker<'a, 'tcx> {
    type Target = ty::TyCtxt<'tcx>;

    fn deref(&self) -> &Self::Target {
        &self.cx.tcx()
    }
}
