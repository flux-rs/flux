use crate::refinements::{
    ty::{BaseTy, BinOp, Constraint, Literal, Predicate, RefinedTy},
    FnContext,
};

use rustc_middle::{
    mir::{Local, Operand, Place},
    ty::{Const, ParamEnv, TyKind},
};

pub(super) trait Synthesis<'tcx> {
    fn synth(&self, fcx: &mut FnContext<'tcx>) -> (Constraint, RefinedTy);
}

impl<'tcx> Synthesis<'tcx> for Local {
    fn synth(&self, fcx: &mut FnContext<'tcx>) -> (Constraint, RefinedTy) {
        let var = fcx.vars[*self];

        (
            Constraint::Pred(Predicate::Lit(Literal::Bool(true))),
            fcx.ctx.ty_vars[&var].clone(),
        )
    }
}

impl<'tcx> Synthesis<'tcx> for Place<'tcx> {
    fn synth(&self, fcx: &mut FnContext<'tcx>) -> (Constraint, RefinedTy) {
        assert_eq!(0, self.projection.iter().count());

        fcx.synth(self.local)
    }
}

impl<'tcx> Synthesis<'tcx> for Const<'tcx> {
    fn synth(&self, fcx: &mut FnContext<'tcx>) -> (Constraint, RefinedTy) {
        let bits = self.eval_bits(fcx.ctx.tcx, ParamEnv::empty(), self.ty);
        let var = fcx.ctx.new_var();

        let (base_ty, literal) = match *self.ty.kind() {
            TyKind::Bool => (BaseTy::Bool, Literal::Bool(bits != 0)),
            TyKind::Uint(uint_ty) => (BaseTy::Uint(uint_ty), Literal::Int(bits as i128)),
            TyKind::Int(int_ty) => (BaseTy::Int(int_ty), Literal::Int(bits as i128)),
            _ => todo!(),
        };

        (
            Constraint::Pred(Predicate::Lit(Literal::Bool(true))),
            RefinedTy::RefBase(
                var,
                base_ty,
                Predicate::BinApp(
                    BinOp::Eq,
                    Box::new(Predicate::Var(var)),
                    Box::new(Predicate::Lit(literal)),
                ),
            ),
        )
    }
}

impl<'tcx> Synthesis<'tcx> for Operand<'tcx> {
    fn synth(&self, fcx: &mut FnContext<'tcx>) -> (Constraint, RefinedTy) {
        match self {
            Operand::Copy(place) | Operand::Move(place) => fcx.synth(*place),
            Operand::Constant(constant) => fcx.synth(*constant.literal),
        }
    }
}
