use crate::lower::{Lower, LowerCtx, LowerResult};

use liquid_rust_lrir::mir::{SwitchTargets, Terminator, TerminatorKind};

use rustc_middle::mir;

impl<'tcx> Lower<'tcx> for mir::Terminator<'tcx> {
    type Output = Terminator;

    fn lower(&self, lcx: LowerCtx<'tcx>) -> LowerResult<Self::Output> {
        let kind = match &self.kind {
            mir::TerminatorKind::Return => TerminatorKind::Return,
            mir::TerminatorKind::Goto { target } => TerminatorKind::Goto {
                target: target.lower(lcx)?,
            },
            mir::TerminatorKind::SwitchInt {
                discr,
                switch_ty,
                targets,
            } => TerminatorKind::SwitchInt {
                discr: discr.lower(lcx)?,
                switch_ty: switch_ty.lower(lcx)?,
                targets: SwitchTargets::new(
                    targets.iter().map(|(value, target)| {
                        (value, target.lower(lcx).ok().expect("This never fails"))
                    }),
                    targets.otherwise().lower(lcx)?,
                ),
            },
            mir::TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } => TerminatorKind::Call {
                func: func.lower(lcx)?,
                args: args
                    .iter()
                    .map(|arg| arg.lower(lcx))
                    .collect::<LowerResult<Vec<_>>>()?,
                destination: destination
                    .ok_or_else(|| todo!())
                    .and_then(|(place, target)| Ok((place.lower(lcx)?, target.lower(lcx)?)))?,
            },
            mir::TerminatorKind::Assert {
                cond,
                expected,
                target,
                ..
            } => TerminatorKind::Assert {
                cond: cond.lower(lcx)?,
                expected: *expected,
                target: target.lower(lcx)?,
            },
            _ => todo!(),
        };

        Ok(Terminator {
            kind,
            span: self.source_info.span,
        })
    }
}
