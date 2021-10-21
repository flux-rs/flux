use itertools::Itertools;
use liquid_rust_common::errors::ErrorReported;
use liquid_rust_core::{
    ir::{
        BasicBlockData, BinOp, Body, Constant, Local, LocalDecl, Operand, Rvalue, Statement,
        StatementKind, Terminator, TerminatorKind,
    },
    ty::TypeLayout,
};
use rustc_const_eval::interpret::ConstValue;
use rustc_middle::{
    mir,
    ty::{ParamEnv, TyCtxt},
};

pub struct LoweringCtxt<'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'tcx mir::Body<'tcx>,
}

impl<'tcx> LoweringCtxt<'tcx> {
    pub fn lower(tcx: TyCtxt<'tcx>, body: &'tcx mir::Body<'tcx>) -> Result<Body, ErrorReported> {
        let lower = Self { tcx, body };

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

    fn lower_terminator(
        &self,
        terminator: &mir::Terminator<'tcx>,
    ) -> Result<Terminator, ErrorReported> {
        let kind = match &terminator.kind {
            mir::TerminatorKind::Return => TerminatorKind::Return,
            mir::TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } => {
                let func = match func.ty(self.body, self.tcx).kind() {
                    rustc_middle::ty::TyKind::FnDef(fn_def, substs) if substs.is_empty() => *fn_def,
                    _ => {
                        self.tcx
                            .sess
                            .span_err(terminator.source_info.span, "unsupported function call");
                        return Err(ErrorReported);
                    }
                };
                let destination = match destination {
                    Some((place, bb)) => Some((self.lower_place(place)?, *bb)),
                    None => None,
                };

                TerminatorKind::Call {
                    func,
                    destination,
                    args: args
                        .iter()
                        .map(|arg| self.lower_operand(arg))
                        .try_collect()?,
                }
            }
            mir::TerminatorKind::Goto { .. }
            | mir::TerminatorKind::SwitchInt { .. }
            | mir::TerminatorKind::Resume
            | mir::TerminatorKind::Abort
            | mir::TerminatorKind::Unreachable
            | mir::TerminatorKind::Drop { .. }
            | mir::TerminatorKind::DropAndReplace { .. }
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
            mir::Rvalue::BinaryOp(bin_op, operands) => Ok(Rvalue::BinaryOp(
                self.lower_bin_op(*bin_op)?,
                self.lower_operand(&operands.0)?,
                self.lower_operand(&operands.1)?,
            )),
            mir::Rvalue::UnaryOp(_, _)
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

    fn lower_bin_op(&self, bin_op: mir::BinOp) -> Result<BinOp, ErrorReported> {
        match bin_op {
            mir::BinOp::Add => Ok(BinOp::Add),
            mir::BinOp::Sub
            | mir::BinOp::Mul
            | mir::BinOp::Div
            | mir::BinOp::Rem
            | mir::BinOp::BitXor
            | mir::BinOp::BitAnd
            | mir::BinOp::BitOr
            | mir::BinOp::Shl
            | mir::BinOp::Shr
            | mir::BinOp::Eq
            | mir::BinOp::Lt
            | mir::BinOp::Le
            | mir::BinOp::Ne
            | mir::BinOp::Ge
            | mir::BinOp::Gt
            | mir::BinOp::Offset => {
                self.tcx
                    .sess
                    .err(&format!("unsupported binary operation: `{:?}`", bin_op));
                Err(ErrorReported)
            }
        }
    }

    fn lower_operand(&self, op: &mir::Operand<'tcx>) -> Result<Operand, ErrorReported> {
        match op {
            mir::Operand::Copy(place) => Ok(Operand::Copy(self.lower_place(place)?)),
            mir::Operand::Move(place) => Ok(Operand::Move(self.lower_place(place)?)),
            mir::Operand::Constant(c) => Ok(Operand::Constant(self.lower_constant(c)?)),
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
        use rustc_middle::ty::{Const, ConstKind};
        let tcx = self.tcx;
        match &c.literal {
            mir::ConstantKind::Ty(&Const {
                ty,
                val: ConstKind::Value(ConstValue::Scalar(scalar)),
            }) if ty.is_integral() => match (ty.kind(), scalar_to_bits(tcx, scalar, ty)) {
                (rustc_middle::ty::TyKind::Int(int_ty), Some(bits)) => {
                    Ok(Constant::Int(bits as i128, *int_ty))
                }
                _ => {
                    self.tcx.sess.span_err(
                        c.span,
                        &format!("constant not supported: `{:?}`", c.literal),
                    );
                    Err(ErrorReported)
                }
            },
            _ => {
                self.tcx.sess.span_err(
                    c.span,
                    &format!("constant not supported: `{:?}`", c.literal),
                );
                Err(ErrorReported)
            }
        }
    }

    fn lower_ty(&self, ty: &rustc_middle::ty::Ty<'tcx>) -> Result<TypeLayout, ErrorReported> {
        match ty.kind() {
            rustc_middle::ty::TyKind::Int(int_ty) => Ok(TypeLayout::Int(*int_ty)),
            _ => {
                self.tcx.sess.err("type not supported");
                Err(ErrorReported)
            }
        }
    }
}

fn scalar_to_bits<'tcx>(
    tcx: TyCtxt<'tcx>,
    scalar: mir::interpret::Scalar,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> Option<u128> {
    let size = tcx
        .layout_of(ParamEnv::empty().with_reveal_all_normalized(tcx).and(ty))
        .unwrap()
        .size;
    scalar.to_bits(size).ok()
}
