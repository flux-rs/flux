mod basic_block;
mod constant;
mod context;
mod local;
mod operand;
mod place;
mod result;
mod rvalue;
mod statement;
mod terminator;
mod ty;

use result::LowerResult;

pub use context::LowerCtx;

trait Lower<'tcx> {
    type Output;

    fn lower(&self, lcx: LowerCtx<'tcx>) -> LowerResult<Self::Output>;
}
