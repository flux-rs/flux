use crate::{
    ir::{Literal, Local, Operand, Rvalue, Statement},
    ty::{BaseTy, Ty},
    tycheck::{Constraint, TyContextAt},
};

pub(super) trait Synth<'tcx> {
    fn synth(&self, ctx: &TyContextAt<'tcx>) -> (Constraint, Ty);
}

impl<'tcx> Synth<'tcx> for Literal {
    fn synth(&self, ctx: &TyContextAt<'tcx>) -> (Constraint, Ty) {
        let var = ctx.new_variable();

        let base_ty = match self {
            Self::Unit => BaseTy::Unit,
            Self::Bool(_) => BaseTy::Bool,
            Self::Uint(_, size) => BaseTy::Uint(*size),
            Self::Int(_, size) => BaseTy::Int(*size),
            Self::Fn(id) => return (true.into(), ctx.type_of_func(id)),
        };

        let ty = Ty::RefBase(var, base_ty, true.into());

        (true.into(), ty)
    }
}

impl<'tcx> Synth<'tcx> for Local {
    fn synth(&self, ctx: &TyContextAt<'tcx>) -> (Constraint, Ty) {
        (true.into(), ctx.type_of_local(self))
    }
}

impl<'tcx> Synth<'tcx> for Statement {
    fn synth(&self, ctx: &TyContextAt<'tcx>) -> (Constraint, Ty) {
        match self {
            // Syn-Assign
            Self::Assign(local, rvalue) => {
                let (rhs_constraint, rhs_ty) = ctx.synth(rvalue);
                let lhs_constraint = ctx.check(local, &rhs_ty);

                (rhs_constraint | lhs_constraint, ctx.refined(BaseTy::Unit))
            }
            Self::Noop => (true.into(), ctx.refined(BaseTy::Unit)),
        }
    }
}

impl<'tcx> Synth<'tcx> for Rvalue {
    fn synth(&self, ctx: &TyContextAt<'tcx>) -> (Constraint, Ty) {
        match self {
            Self::Use(op) => ctx.synth(op),
            Rvalue::BinApp(bin_op, op1, op2) => todo!(),
            Rvalue::UnApp(un_op, op) => todo!(),
        }
    }
}

impl<'tcx> Synth<'tcx> for Operand {
    fn synth(&self, ctx: &TyContextAt<'tcx>) -> (Constraint, Ty) {
        match self {
            Self::Copy(local) | Self::Move(local) => ctx.synth(local),
            Self::Lit(lit) => ctx.synth(lit),
        }
    }
}
