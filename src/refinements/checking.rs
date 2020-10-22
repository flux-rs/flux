use crate::refinements::{
    ty::{Constraint, RefinedTy},
    FnContext,
};

pub(super) trait Checking<'tcx> {
    fn check(&self, fcx: &mut FnContext<'tcx>, ty: &RefinedTy) -> Constraint;
}
