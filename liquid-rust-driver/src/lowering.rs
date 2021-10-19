use itertools::Itertools;
use liquid_rust_common::errors::ErrorReported;
use liquid_rust_core::{
    ir::{
        BasicBlockData, Body, Constant, Local, LocalDecl, Operand, Rvalue, Statement,
        StatementKind, Terminator, TerminatorKind,
    },
    ty::TypeLayout,
};
use rustc_const_eval::interpret::ConstValue;
use rustc_middle::{mir, ty::TyCtxt};

pub struct LoweringCtxt<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> LoweringCtxt<'tcx> {
    pub fn lower(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>) -> Result<Body, ErrorReported> {
        let lower = Self { tcx };

        let basic_blocks = body
            .basic_blocks()
            .iter()
            .map(|bb_data| lower.lower_basic_block_data(bb_data))
            .try_collect()?;

        let local_decls = body
            .local_decls
            .iter()
            .map(|local_decl| lower.lower_local_decl(local_decl))
            .try_collect()?;

        Ok(Body {
            basic_blocks,
            local_decls,
            arg_count: body.arg_count,
        })
    }

    fn lower_local_decl(
        &self,
        local_decl: &mir::LocalDecl<'tcx>,
    ) -> Result<LocalDecl, ErrorReported> {
        Ok(LocalDecl {
            layout: self.lower_ty(&local_decl.ty)?,
        })
    }

    fn lower_basic_block_data(
        &self,
        data: &mir::BasicBlockData<'tcx>,
    ) -> Result<BasicBlockData, ErrorReported> {
        let data = BasicBlockData {
            statements: data
                .statements
                .iter()
                .map(|stmt| self.lower_statement(stmt))
                .try_collect()?,
            terminator: data
                .terminator
                .as_ref()
                .map(|terminator| self.lower_terminator(terminator))
                .transpose()?,
        };
        Ok(data)
    }

    fn lower_statement(&self, stmt: &mir::Statement<'tcx>) -> Result<Statement, ErrorReported> {
        let kind = match &stmt.kind {
            mir::StatementKind::Assign(box (place, rvalue)) => {
                StatementKind::Assign(self.lower_place(place)?, self.lower_rvalue(rvalue)?)
            }
            mir::StatementKind::Nop
            | mir::StatementKind::StorageLive(_)
            | mir::StatementKind::StorageDead(_) => StatementKind::Nop,
            mir::StatementKind::FakeRead(_)
            | mir::StatementKind::SetDiscriminant { .. }
            | mir::StatementKind::LlvmInlineAsm(_)
            | mir::StatementKind::Retag(_, _)
            | mir::StatementKind::AscribeUserType(_, _)
            | mir::StatementKind::Coverage(_)
            | mir::StatementKind::CopyNonOverlapping(_) => {
                self.tcx
                    .sess
                    .span_err(stmt.source_info.span, "unsupported statement kind");
                return Err(ErrorReported);
            }
        };
        Ok(Statement { kind })
    }

    fn lower_terminator(&self, terminator: &mir::Terminator) -> Result<Terminator, ErrorReported> {
        let kind = match terminator.kind {
            mir::TerminatorKind::Return => TerminatorKind::Return,
            mir::TerminatorKind::Goto { .. }
            | mir::TerminatorKind::SwitchInt { .. }
            | mir::TerminatorKind::Resume
            | mir::TerminatorKind::Abort
            | mir::TerminatorKind::Unreachable
            | mir::TerminatorKind::Drop { .. }
            | mir::TerminatorKind::DropAndReplace { .. }
            | mir::TerminatorKind::Call { .. }
            | mir::TerminatorKind::Assert { .. }
            | mir::TerminatorKind::Yield { .. }
            | mir::TerminatorKind::GeneratorDrop
            | mir::TerminatorKind::FalseEdge { .. }
            | mir::TerminatorKind::FalseUnwind { .. }
            | mir::TerminatorKind::InlineAsm { .. } => {
                self.tcx
                    .sess
                    .span_err(terminator.source_info.span, "unsupported terminator kind");
                return Err(ErrorReported);
            }
        };
        Ok(Terminator { kind })
    }

    fn lower_rvalue(&self, rvalue: &mir::Rvalue<'tcx>) -> Result<Rvalue, ErrorReported> {
        match rvalue {
            mir::Rvalue::Use(op) => Ok(Rvalue::Use(self.lower_operand(op)?)),
            mir::Rvalue::UnaryOp(_, _)
            | mir::Rvalue::BinaryOp(_, _)
            | mir::Rvalue::Repeat(_, _)
            | mir::Rvalue::Ref(_, _, _)
            | mir::Rvalue::ThreadLocalRef(_)
            | mir::Rvalue::AddressOf(_, _)
            | mir::Rvalue::Len(_)
            | mir::Rvalue::Cast(_, _, _)
            | mir::Rvalue::CheckedBinaryOp(_, _)
            | mir::Rvalue::NullaryOp(_, _)
            | mir::Rvalue::Discriminant(_)
            | mir::Rvalue::Aggregate(_, _)
            | mir::Rvalue::ShallowInitBox(_, _) => {
                self.tcx.sess.err("unsupported rvalue kind");
                Err(ErrorReported)
            }
        }
    }

    fn lower_operand(&self, op: &mir::Operand<'tcx>) -> Result<Operand, ErrorReported> {
        match op {
            mir::Operand::Copy(place) => Ok(Operand::Copy(self.lower_place(place)?)),
            mir::Operand::Constant(c) => Ok(Operand::Constant(self.lower_constant(c)?)),
            mir::Operand::Move(_) => {
                self.tcx.sess.err("operand not supported");
                Err(ErrorReported)
            }
        }
    }

    fn lower_place(&self, place: &mir::Place<'tcx>) -> Result<Local, ErrorReported> {
        if !place.projection.is_empty() {
            self.tcx.sess.err("place not supported");
            return Err(ErrorReported);
        }
        Ok(place.local)
    }

    fn lower_constant(&self, c: &mir::Constant<'tcx>) -> Result<Constant, ErrorReported> {
        match &c.literal {
            mir::ConstantKind::Val(ConstValue::Scalar(scalar), ty) if ty.is_integral() => {
                match ty.kind() {
                    rustc_middle::ty::TyKind::Int(int_ty) => {
                        Ok(Constant::Int(scalar.to_i128().unwrap(), *int_ty))
                    }
                    rustc_middle::ty::TyKind::Uint(int_ty) => {
                        Ok(Constant::Uint(scalar.to_u128().unwrap(), *int_ty))
                    }
                    _ => unreachable!("type has to be integral at this point"),
                }
            }
            _ => {
                self.tcx.sess.span_err(c.span, "constant not supported");
                Err(ErrorReported)
            }
        }
    }

    fn lower_ty(&self, ty: &rustc_middle::ty::Ty<'tcx>) -> Result<TypeLayout, ErrorReported> {
        match ty.kind() {
            rustc_middle::ty::TyKind::Int(int_ty) => Ok(TypeLayout::Int(*int_ty)),
            rustc_middle::ty::TyKind::Uint(int_ty) => Ok(TypeLayout::Uint(*int_ty)),
            _ => {
                self.tcx.sess.err("type not supported");
                Err(ErrorReported)
            }
        }
    }
}
