use crate::lower::{Lower, LowerCtx, LowerResult};

use liquid_rust_lrir::mir::{Local, LocalDecl};

use rustc_middle::mir;

impl<'tcx> Lower<'tcx> for mir::Local {
    type Output = Local;

    fn lower(&self, _lcx: LowerCtx<'tcx>) -> LowerResult<Self::Output> {
        Ok(*self)
    }
}

impl<'tcx> Lower<'tcx> for mir::LocalDecl<'tcx> {
    type Output = LocalDecl<'tcx>;

    fn lower(&self, _lcx: LowerCtx<'tcx>) -> LowerResult<Self::Output> {
        let output = LocalDecl {
            is_mutable: self.mutability == mir::Mutability::Mut,
            ty: self.ty,
            span: self.source_info.span,
        };

        Ok(output)
    }
}
