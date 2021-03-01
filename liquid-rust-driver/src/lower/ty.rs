use crate::lower::{Lower, LowerCtx, LowerResult};

use liquid_rust_lrir::ty::BaseTy;

use rustc_middle::ty;

impl<'tcx> Lower<'tcx> for ty::Ty<'tcx> {
    type Output = BaseTy;

    fn lower(&self, _lcx: LowerCtx<'tcx>) -> LowerResult<Self::Output> {
        let output = match self.kind() {
            ty::TyKind::Bool => BaseTy::Bool,
            // FIXME: maybe we should care about the size and sign.
            ty::TyKind::Uint(_) | ty::TyKind::Int(_) => BaseTy::Int,
            _ => todo!(),
        };

        Ok(output)
    }
}
