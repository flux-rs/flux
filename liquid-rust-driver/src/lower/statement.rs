use crate::lower::{Lower, LowerCtx, LowerResult};

use liquid_rust_lrir::mir::{Statement, StatementKind};

use rustc_middle::mir;

impl<'tcx> Lower<'tcx> for mir::Statement<'tcx> {
    type Output = Statement;

    fn lower(&self, lcx: LowerCtx<'tcx>) -> LowerResult<Self::Output> {
        let kind = match &self.kind {
            mir::StatementKind::Assign(assign) => {
                let (place, rvalue) = assign.as_ref();

                StatementKind::Assign(place.lower(lcx)?, rvalue.lower(lcx)?)
            }
            mir::StatementKind::StorageLive(local) => StatementKind::StorageLive(*local),
            mir::StatementKind::StorageDead(local) => StatementKind::StorageDead(*local),
            mir::StatementKind::Nop => StatementKind::Nop,
            _ => todo!(),
        };

        Ok(Statement {
            kind,
            span: self.source_info.span,
        })
    }
}
