use crate::lower::{Lower, LowerCtx, LowerResult};

use liquid_rust_lrir::mir::Constant;

use rustc_middle::{mir, ty::ParamEnv};

impl<'tcx> Lower<'tcx> for mir::Constant<'tcx> {
    type Output = Constant;

    fn lower(&self, lcx: LowerCtx<'tcx>) -> LowerResult<Self::Output> {
        let bits = self
            .literal
            .try_eval_bits(lcx.tcx, ParamEnv::empty(), self.literal.ty)
            .ok_or_else(|| todo!())?;

        let base_ty = self.literal.ty.lower(lcx)?;

        Ok(Constant::new(bits, base_ty))
    }
}
