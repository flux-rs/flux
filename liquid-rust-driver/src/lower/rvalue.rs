use crate::lower::{Lower, LowerCtx, LowerResult};

use liquid_rust_lrir::mir::{BinOp, Rvalue, UnOp};

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
                let un_op = match bin_op {
                    mir::BinOp::Add => BinOp::Add,
                    mir::BinOp::Sub => BinOp::Sub,
                    mir::BinOp::Mul => BinOp::Mul,
                    mir::BinOp::Div => BinOp::Div,
                    mir::BinOp::Rem => BinOp::Rem,
                    mir::BinOp::Eq => BinOp::Eq(left_operand.ty(lcx.body, lcx.tcx).lower(lcx)?),
                    mir::BinOp::Ne => BinOp::Neq(left_operand.ty(lcx.body, lcx.tcx).lower(lcx)?),
                    mir::BinOp::Lt => BinOp::Lt,
                    mir::BinOp::Le => BinOp::Lte,
                    mir::BinOp::Gt => BinOp::Gt,
                    mir::BinOp::Ge => BinOp::Gte,
                    _ => todo!(),
                };

                Rvalue::BinaryOp(un_op, left_operand.lower(lcx)?, right_operand.lower(lcx)?)
            }

            Self::Ref { .. } => todo!(),

            _ => todo!("{:#?}", self),
        };

        Ok(output)
    }
}
