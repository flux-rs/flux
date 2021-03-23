use crate::lower::{Lower, LowerCtx, LowerResult};

use liquid_rust_lrir::mir::{Place, PlaceElem};

use rustc_middle::mir;

impl<'tcx> Lower<'tcx> for mir::Place<'tcx> {
    type Output = Place;

    fn lower(&self, lcx: LowerCtx<'tcx>) -> LowerResult<Self::Output> {
        Ok(Place {
            local: self.local,
            projection: self
                .projection
                .iter()
                .map(|elem| elem.lower(lcx))
                .collect::<LowerResult<Vec<_>>>()?,
        })
    }
}

impl<'tcx> Lower<'tcx> for mir::PlaceElem<'tcx> {
    type Output = PlaceElem;

    fn lower(&self, _lcx: LowerCtx<'tcx>) -> LowerResult<Self::Output> {
        let output = match self {
            Self::Deref => PlaceElem::Deref,
            // FIXME: Should we store the type too?
            Self::Field(field, _ty) => PlaceElem::Field(field.index()),
            _ => todo!(),
        };

        Ok(output)
    }
}
