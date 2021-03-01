use crate::lower::{Lower, LowerResult};

use liquid_rust_common::index::IndexMap;
use liquid_rust_lrir::mir::Body;

use rustc_middle::{mir, ty::TyCtxt};

#[derive(Clone, Copy)]
pub(super) struct LowerCtx<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub body: &'tcx mir::Body<'tcx>,
}

impl<'tcx> LowerCtx<'tcx> {
    pub fn lower_body(tcx: TyCtxt<'tcx>, body: &'tcx mir::Body<'tcx>) -> LowerResult<Body> {
        let lcx = Self { tcx, body };

        let basic_blocks = IndexMap::from_raw(
            body.basic_blocks()
                .iter()
                .map(|basic_block_data| basic_block_data.lower(lcx))
                .collect::<LowerResult<Vec<_>>>()?,
        );

        let local_decls = IndexMap::from_raw(
            body.local_decls
                .iter()
                .map(|local_decl| local_decl.lower(lcx))
                .collect::<LowerResult<Vec<_>>>()?,
        );

        let predecessors = IndexMap::from_raw(
            body.predecessors()
                .iter()
                .map(|basic_blocks| {
                    basic_blocks
                        .iter()
                        .map(|basic_block| basic_block.lower(lcx))
                        .collect::<LowerResult<Vec<_>>>()
                })
                .collect::<LowerResult<Vec<_>>>()?,
        );

        Ok(Body {
            basic_blocks,
            local_decls,
            arg_count: body.arg_count,
            span: body.span,
            predecessors,
        })
    }
}
