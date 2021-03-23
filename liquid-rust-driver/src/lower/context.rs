use crate::lower::{Lower, LowerResult};

use liquid_rust_common::index::IndexVec;
use liquid_rust_lrir::mir::Body;

use rustc_middle::{mir, ty::TyCtxt};

#[derive(Clone, Copy)]
pub(crate) struct LowerCtx<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub body: &'tcx mir::Body<'tcx>,
}

impl<'tcx> LowerCtx<'tcx> {
    pub fn lower_body(tcx: TyCtxt<'tcx>, body: &'tcx mir::Body<'tcx>) -> LowerResult<Body<'tcx>> {
        let lcx = Self { tcx, body };

        let basic_blocks = body
            .basic_blocks()
            .iter()
            .map(|basic_block_data| basic_block_data.lower(lcx))
            .collect::<LowerResult<IndexVec<_, _>>>()?;

        let local_decls = body
            .local_decls
            .iter()
            .map(|local_decl| local_decl.lower(lcx))
            .collect::<LowerResult<IndexVec<_, _>>>()?;

        let predecessors = body
            .predecessors()
            .iter()
            .map(|basic_blocks| basic_blocks.iter().copied().collect::<Vec<_>>())
            .collect::<IndexVec<_, _>>();

        Ok(Body {
            basic_blocks,
            local_decls,
            arg_count: body.arg_count,
            span: body.span,
            predecessors,
        })
    }
}
