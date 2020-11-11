use crate::{
    ty::Ty,
    tycheck::{Constraint, TyCtxAt},
};

pub(super) trait Check<'tcx> {
    fn check(&self, ctx: &mut TyCtxAt<'tcx>, ty: &Ty) -> Constraint;
}
