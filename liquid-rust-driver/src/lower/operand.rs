use crate::lower::{Lower, LowerCtx, LowerResult};

use liquid_rust_lrir::mir::Operand;

use rustc_middle::mir;

impl<'tcx> Lower<'tcx> for mir::Operand<'tcx> {
    type Output = Operand;

    fn lower(&self, lcx: LowerCtx<'tcx>) -> LowerResult<Self::Output> {
        let output = match self {
            Self::Copy(place) => Operand::Copy(place.lower(lcx)?),
            Self::Move(place) => Operand::Move(place.lower(lcx)?),
            Self::Constant(constant) => Operand::Constant(constant.lower(lcx)?),
        };

        Ok(output)
    }
}
