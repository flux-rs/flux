use crate::lower::{Lower, LowerCtx, LowerResult};

use liquid_rust_lrir::mir::{Rvalue, UnOp};

use rustc_middle::mir;

impl<'tcx> Lower<'tcx> for mir::Rvalue<'tcx> {
    type Output = Rvalue;

    fn lower(&self, lcx: LowerCtx<'tcx>) -> LowerResult<Self::Output> {
        let output = match self {
            Self::Use(operand) => Rvalue::Use(operand.lower(lcx)?),
            Self::UnaryOp(un_op, operand) => {
                let un_op = match un_op {
                    mir::UnOp::Not => UnOp::Not,
                    mir::UnOp::Neg => UnOp::Neg,
                };
                Rvalue::UnaryOp(un_op, operand.lower(lcx)?)
            }
            Self::BinaryOp(bin_op, left_operand, right_operand) => {
                Rvalue::BinaryOp(*bin_op, left_operand.lower(lcx)?, right_operand.lower(lcx)?)
            }

            Self::Ref { .. } => todo!(),

            _ => todo!("{:#?}", self),
        };

        Ok(output)
    }
}
