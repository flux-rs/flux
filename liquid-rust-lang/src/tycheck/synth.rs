use crate::{
    ir::{Literal, Local},
    ty::{BaseTy, Ty, Variable},
    tycheck::{Constraint, TyCtxAt},
};

pub(super) trait Synth<'tcx> {
    fn synth(&self, ctx: &mut TyCtxAt<'tcx>) -> (Constraint, Ty);
}

impl<'tcx> Synth<'tcx> for Literal {
    fn synth(&self, ctx: &mut TyCtxAt<'tcx>) -> (Constraint, Ty) {
        let var = ctx.new_var();

        let base_ty = match self {
            Self::Unit => BaseTy::Unit,
            Self::Bool(_) => BaseTy::Bool,
            Self::Uint(_, size) => BaseTy::Uint(*size),
            Self::Int(_, size) => BaseTy::Int(*size),
            Self::Fn(id) => {
                let ty = ctx
                    .tcx
                    .funcs_ty
                    .get(id)
                    .expect("Functions should always have a type.")
                    .clone();

                return (true.into(), ty);
            }
        };

        let ty = Ty::RefBase(var, base_ty, true.into());

        (true.into(), ty)
    }
}

impl<'tcx> Synth<'tcx> for Variable {
    fn synth(&self, ctx: &mut TyCtxAt<'tcx>) -> (Constraint, Ty) {
        let ty = ctx
            .vars_ty
            .get(self)
            .expect("Variables should always have a type.")
            .clone();

        (true.into(), ty)
    }
}

impl<'tcx> Synth<'tcx> for Local {
    fn synth(&self, ctx: &mut TyCtxAt<'tcx>) -> (Constraint, Ty) {
        let var = *ctx
            .vars
            .get(self)
            .expect("A local should always map to a variable.");

        ctx.synth(&var)
    }
}
