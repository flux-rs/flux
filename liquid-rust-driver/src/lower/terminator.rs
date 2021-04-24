use crate::lower::{Lower, LowerCtx, LowerResult};

use liquid_rust_lrir::mir::{SwitchTargets, Terminator, TerminatorKind};

use rustc_middle::{mir, ty};

impl<'tcx> Lower<'tcx> for mir::Terminator<'tcx> {
    type Output = Terminator<'tcx>;

    fn lower(&self, lcx: LowerCtx<'tcx>) -> LowerResult<Self::Output> {
        let kind = match &self.kind {
            mir::TerminatorKind::Return => TerminatorKind::Return,
            mir::TerminatorKind::Goto { target } => TerminatorKind::Goto { target: *target },
            mir::TerminatorKind::SwitchInt {
                discr,
                switch_ty,
                targets,
            } => TerminatorKind::SwitchInt {
                discr: discr.lower(lcx)?,
                switch_ty: switch_ty.lower(lcx)?,
                targets: SwitchTargets::new(targets.iter(), targets.otherwise()),
            },
            mir::TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } => {
                let func = match func.ty(lcx.body, lcx.tcx).kind() {
                    ty::TyKind::FnDef(fn_def, substs) => (*fn_def, *substs),
                    _ => {
                        unreachable!("Calling non function");
                    }
                };

                TerminatorKind::Call {
                    func,
                    args: args
                        .iter()
                        .map(|arg| arg.lower(lcx))
                        .collect::<LowerResult<Vec<_>>>()?,
                    destination: destination
                        .map(|(place, target)| Ok((place.lower(lcx)?, target)))
                        .transpose()?,
                }
            }
            mir::TerminatorKind::Assert {
                cond,
                expected,
                target,
                ..
            } => TerminatorKind::Assert {
                cond: cond.lower(lcx)?,
                expected: *expected,
                target: *target,
            },
            _ => todo!(),
        };

        Ok(Terminator {
            kind,
            span: self.source_info.span,
        })
    }
}
