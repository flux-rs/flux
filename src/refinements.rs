extern crate arena;
extern crate rustc_index;

use super::syntax::ast;
use arena::TypedArena;
use rustc::mir;
pub use rustc::mir::interpret::{ConstValue, Scalar};
use rustc::ty::{Ty, TyCtxt};
use rustc_hir::BodyId;
use std::collections::HashMap;

#[derive(Debug)]
pub struct FnRefines<'rcx, 'tcx> {
    pub body_id: BodyId,
    pub fn_decl: FnDecl<'rcx, 'tcx>,
    pub local_decls: HashMap<mir::Local, &'rcx Refine<'rcx, 'tcx>>,
}

#[derive(Debug)]
pub struct FnDecl<'rcx, 'tcx> {
    pub inputs: Vec<&'rcx Refine<'rcx, 'tcx>>,
    pub output: &'rcx Refine<'rcx, 'tcx>,
}

#[derive(Debug)]
pub enum Refine<'rcx, 'tcx> {
    Unary(ast::UnOpKind, &'rcx Refine<'rcx, 'tcx>),
    Binary(
        &'rcx Refine<'rcx, 'tcx>,
        ast::BinOpKind,
        &'rcx Refine<'rcx, 'tcx>,
    ),
    Constant(Ty<'tcx>, ConstValue<'tcx>),
    Place(mir::Place<'tcx>),
    Nu,
}

pub struct RefineCtxt<'rcx, 'tcx> {
    arena: &'rcx TypedArena<Refine<'rcx, 'tcx>>,
    pub refine_true: &'rcx Refine<'rcx, 'tcx>,
    pub nu: &'rcx Refine<'rcx, 'tcx>,
}

impl<'rcx, 'tcx> RefineCtxt<'rcx, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, arena: &'rcx TypedArena<Refine<'rcx, 'tcx>>) -> Self {
        let refine_true = arena.alloc(Refine::Constant(
            tcx.types.bool,
            ConstValue::Scalar(Scalar::from_bool(true)),
        ));
        let nu = arena.alloc(Refine::Nu);
        RefineCtxt {
            arena,
            refine_true,
            nu,
        }
    }

    pub fn mk_binary(
        &'rcx self,
        lhs: &'rcx Refine<'rcx, 'tcx>,
        op: ast::BinOpKind,
        rhs: &'rcx Refine<'rcx, 'tcx>,
    ) -> &'rcx Refine<'rcx, 'tcx> {
        self.arena.alloc(Refine::Binary(lhs, op, rhs))
    }

    pub fn mk_unary(
        &'rcx self,
        op: ast::UnOpKind,
        expr: &'rcx Refine<'rcx, 'tcx>,
    ) -> &'rcx Refine<'rcx, 'tcx> {
        self.arena.alloc(Refine::Unary(op, expr))
    }

    pub fn mk_place(&'rcx self, place: mir::Place<'tcx>) -> &'rcx Refine<'rcx, 'tcx> {
        self.arena.alloc(Refine::Place(place))
    }

    pub fn mk_constant(
        &'rcx self,
        ty: Ty<'tcx>,
        val: ConstValue<'tcx>,
    ) -> &'rcx Refine<'rcx, 'tcx> {
        self.arena.alloc(Refine::Constant(ty, val))
    }

    pub fn mk_not(&'rcx self, refine: &'rcx Refine<'rcx, 'tcx>) -> &'rcx Refine<'rcx, 'tcx> {
        self.mk_unary(ast::UnOpKind::Not, refine)
    }
}
