use itertools::Itertools;
use liquid_rust_core::{
    self as core,
    ir::{
        BasicBlockData, BinOp, Body, Constant, LocalDecl, Operand, Place, PlaceElem, Rvalue,
        Statement, StatementKind, Terminator, TerminatorKind,
    },
    ty::Layout,
};
use rustc_const_eval::interpret::ConstValue;
use rustc_errors::{DiagnosticId, ErrorReported};
use rustc_middle::{
    mir,
    ty::{subst::GenericArgKind, ParamEnv, TyCtxt},
};
use rustc_span::Span;

pub struct LoweringCtxt<'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'tcx mir::Body<'tcx>,
}

impl<'tcx> LoweringCtxt<'tcx> {
    pub fn lower(
        tcx: TyCtxt<'tcx>,
        body: &'tcx mir::Body<'tcx>,
    ) -> Result<Body<'tcx>, ErrorReported> {
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

        Ok(Body { basic_blocks, local_decls, arg_count: body.arg_count, mir: body })
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

    fn lower_local_decl(
        &self,
        local_decl: &mir::LocalDecl<'tcx>,
    ) -> Result<LocalDecl, ErrorReported> {
        Ok(LocalDecl {
            layout: self.lower_ty_to_layout(local_decl.ty)?,
            source_info: local_decl.source_info,
        })
    }

    fn lower_statement(&self, stmt: &mir::Statement<'tcx>) -> Result<Statement, ErrorReported> {
        let kind = match &stmt.kind {
            mir::StatementKind::Assign(box (place, rvalue)) => {
                StatementKind::Assign(
                    self.lower_place(place)?,
                    self.lower_rvalue(rvalue, stmt.source_info)?,
                )
            }
            mir::StatementKind::Nop
            | mir::StatementKind::StorageLive(_)
            | mir::StatementKind::StorageDead(_) => StatementKind::Nop,
            mir::StatementKind::FakeRead(_)
            | mir::StatementKind::SetDiscriminant { .. }
            | mir::StatementKind::Retag(_, _)
            | mir::StatementKind::AscribeUserType(_, _)
            | mir::StatementKind::Coverage(_)
            | mir::StatementKind::CopyNonOverlapping(_) => {
                return self.emit_err(
                    Some(stmt.source_info.span),
                    format!("unsupported statement: `{stmt:?}`"),
                );
            }
        };
        Ok(Statement { kind, source_info: stmt.source_info })
    }

    fn lower_terminator(
        &self,
        terminator: &mir::Terminator<'tcx>,
    ) -> Result<Terminator, ErrorReported> {
        let kind = match &terminator.kind {
            mir::TerminatorKind::Return => TerminatorKind::Return,
            mir::TerminatorKind::Call { func, args, destination, .. } => {
                let (func, substs) = match func.ty(self.body, self.tcx).kind() {
                    rustc_middle::ty::TyKind::FnDef(fn_def, substs) => {
                        let substs = substs
                            .iter()
                            .map(|arg| self.lower_generic_arg(arg))
                            .try_collect()?;

                        (*fn_def, substs)
                    }
                    _ => {
                        return self.emit_err(
                            Some(terminator.source_info.span),
                            "unsupported function call",
                        );
                    }
                };
                let destination = match destination {
                    Some((place, bb)) => Some((self.lower_place(place)?, *bb)),
                    None => None,
                };

                TerminatorKind::Call {
                    func,
                    substs,
                    destination,
                    args: args
                        .iter()
                        .map(|arg| self.lower_operand(arg))
                        .try_collect()?,
                }
            }
            mir::TerminatorKind::SwitchInt { discr, targets, .. } => {
                TerminatorKind::SwitchInt {
                    discr: self.lower_operand(discr)?,
                    targets: targets.clone(),
                }
            }
            mir::TerminatorKind::Goto { target } => TerminatorKind::Goto { target: *target },
            mir::TerminatorKind::Drop { place, target, .. } => {
                TerminatorKind::Drop { place: self.lower_place(place)?, target: *target }
            }
            mir::TerminatorKind::Assert { cond, target, expected, .. } => {
                TerminatorKind::Assert {
                    cond: self.lower_operand(cond)?,
                    expected: *expected,
                    target: *target,
                }
            }
            mir::TerminatorKind::Resume
            | mir::TerminatorKind::Abort
            | mir::TerminatorKind::Unreachable
            | mir::TerminatorKind::DropAndReplace { .. }
            | mir::TerminatorKind::Yield { .. }
            | mir::TerminatorKind::GeneratorDrop
            | mir::TerminatorKind::FalseEdge { .. }
            | mir::TerminatorKind::FalseUnwind { .. }
            | mir::TerminatorKind::InlineAsm { .. } => {
                return self.emit_err(
                    Some(terminator.source_info.span),
                    format!("unsupported terminator kind: {:?}", terminator.kind),
                );
            }
        };
        Ok(Terminator { kind, source_info: terminator.source_info })
    }

    fn lower_rvalue(
        &self,
        rvalue: &mir::Rvalue<'tcx>,
        source_info: mir::SourceInfo,
    ) -> Result<Rvalue, ErrorReported> {
        match rvalue {
            mir::Rvalue::Use(op) => Ok(Rvalue::Use(self.lower_operand(op)?)),
            mir::Rvalue::BinaryOp(bin_op, operands) => {
                Ok(Rvalue::BinaryOp(
                    self.lower_bin_op(*bin_op)?,
                    self.lower_operand(&operands.0)?,
                    self.lower_operand(&operands.1)?,
                ))
            }
            mir::Rvalue::Ref(_, mir::BorrowKind::Mut { .. }, p) => {
                Ok(Rvalue::MutRef(self.lower_place(p)?))
            }
            mir::Rvalue::Ref(_, mir::BorrowKind::Shared, p) => {
                Ok(Rvalue::ShrRef(self.lower_place(p)?))
            }
            mir::Rvalue::UnaryOp(un_op, op) => Ok(Rvalue::UnaryOp(*un_op, self.lower_operand(op)?)),
            mir::Rvalue::Repeat(_, _)
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
                self.emit_err(Some(source_info.span), format!("unsupported rvalue: `{rvalue:?}`"))
            }
        }
    }

    fn lower_bin_op(&self, bin_op: mir::BinOp) -> Result<BinOp, ErrorReported> {
        match bin_op {
            mir::BinOp::Add => Ok(BinOp::Add),
            mir::BinOp::Sub => Ok(BinOp::Sub),
            mir::BinOp::Gt => Ok(BinOp::Gt),
            mir::BinOp::Ge => Ok(BinOp::Ge),
            mir::BinOp::Lt => Ok(BinOp::Lt),
            mir::BinOp::Le => Ok(BinOp::Le),
            mir::BinOp::Eq => Ok(BinOp::Eq),
            mir::BinOp::Ne => Ok(BinOp::Ne),
            mir::BinOp::Mul => Ok(BinOp::Mul),
            mir::BinOp::Div => Ok(BinOp::Div),
            mir::BinOp::Rem => Ok(BinOp::Rem),
            mir::BinOp::BitAnd => Ok(BinOp::BitAnd),
            mir::BinOp::BitXor
            | mir::BinOp::BitOr
            | mir::BinOp::Shl
            | mir::BinOp::Shr
            | mir::BinOp::Offset => {
                self.emit_err(None, format!("unsupported binary operation: `{bin_op:?}`"))
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

    fn lower_place(&self, place: &mir::Place<'tcx>) -> Result<Place, ErrorReported> {
        let mut projection = vec![];
        for elem in place.projection {
            match elem {
                mir::PlaceElem::Deref => projection.push(PlaceElem::Deref),
                mir::PlaceElem::Field(field, _) => projection.push(PlaceElem::Field(field)),
                _ => {
                    self.tcx.sess.err("place not supported");
                    return Err(ErrorReported);
                }
            }
        }
        Ok(Place { local: place.local, projection })
    }

    fn lower_constant(&self, c: &mir::Constant<'tcx>) -> Result<Constant, ErrorReported> {
        use rustc_middle::ty::{ConstKind, TyKind};
        let tcx = self.tcx;
        let lit = &c.literal;
        let span = c.span;
        match lit {
            mir::ConstantKind::Ty(c) => {
                if let ConstKind::Value(ConstValue::Scalar(scalar)) = c.val() {
                    let ty = c.ty();
                    match ty.kind() {
                        TyKind::Int(int_ty) => {
                            Ok(Constant::Int(scalar_to_int(tcx, scalar, ty).unwrap(), *int_ty))
                        }
                        TyKind::Uint(int_ty) => {
                            Ok(Constant::Uint(scalar_to_uint(tcx, scalar, ty).unwrap(), *int_ty))
                        }
                        TyKind::Float(float_ty) => {
                            Ok(Constant::Float(scalar_to_bits(tcx, scalar, ty).unwrap(), *float_ty))
                        }
                        TyKind::Bool => {
                            Ok(Constant::Bool(scalar_to_bits(tcx, scalar, ty).unwrap() != 0))
                        }
                        _ => {
                            self.emit_err(Some(span), format!("constant not supported: `{lit:?}`"))
                        }
                    }
                } else {
                    self.emit_err(Some(span), format!("constant not supported: `{lit:?}`"))
                }
            }
            _ => self.emit_err(Some(c.span), format!("constant not supported: `{lit:?}`")),
        }
    }

    fn lower_generic_arg(
        &self,
        arg: rustc_middle::ty::subst::GenericArg,
    ) -> Result<core::ty::Ty, ErrorReported> {
        match arg.unpack() {
            GenericArgKind::Type(ty) => self.lower_ty(ty),
            GenericArgKind::Const(_) | GenericArgKind::Lifetime(_) => {
                self.emit_err(None, format!("unsupported generic argument: `{arg:?}`"))
            }
        }
    }

    fn lower_ty_to_layout(&self, ty: rustc_middle::ty::Ty) -> Result<Layout, ErrorReported> {
        match ty.kind() {
            rustc_middle::ty::TyKind::Bool => Ok(Layout::Bool),
            rustc_middle::ty::TyKind::Int(int_ty) => Ok(Layout::Int(*int_ty)),
            rustc_middle::ty::TyKind::Uint(uint_ty) => Ok(Layout::Uint(*uint_ty)),
            rustc_middle::ty::TyKind::Param(_) => Ok(Layout::Param),
            rustc_middle::ty::TyKind::Adt(adt_def, _) => Ok(Layout::Adt(adt_def.did)),
            rustc_middle::ty::TyKind::Ref(..) => Ok(Layout::Ref),
            rustc_middle::ty::TyKind::Float(float_ty) => Ok(Layout::Float(*float_ty)),
            _ => self.emit_err(None, format!("unsupported type `{ty:?}`, kind: `{:?}`", ty.kind())),
        }
    }

    fn lower_ty(&self, ty: rustc_middle::ty::Ty) -> Result<core::ty::Ty, ErrorReported> {
        use liquid_rust_core::ty as core;
        match ty.kind() {
            rustc_middle::ty::TyKind::Bool => {
                Ok(core::Ty::Exists(core::BaseTy::Bool, core::Pred::Infer))
            }
            rustc_middle::ty::TyKind::Int(int_ty) => {
                Ok(core::Ty::Exists(core::BaseTy::Int(*int_ty), core::Pred::Infer))
            }
            rustc_middle::ty::TyKind::Uint(uint_ty) => {
                Ok(core::Ty::Exists(core::BaseTy::Uint(*uint_ty), core::Pred::Infer))
            }
            rustc_middle::ty::TyKind::Float(float_ty) => Ok(core::Ty::Float(*float_ty)),
            rustc_middle::ty::TyKind::Param(param) => {
                Ok(core::Ty::Param(core::ParamTy { index: param.index, name: param.name }))
            }
            rustc_middle::ty::TyKind::Adt(adt_def, substs) => {
                let substs = substs
                    .iter()
                    .map(|arg| self.lower_generic_arg(arg))
                    .try_collect()?;
                let adt = core::BaseTy::Adt(adt_def.did, substs);
                Ok(core::Ty::Exists(adt, core::Pred::Infer))
            }
            _ => self.emit_err(None, format!("unsupported type `{ty:?}`, kind: `{:?}`", ty.kind())),
        }
    }

    fn emit_err<S: AsRef<str>, T>(&self, span: Option<Span>, msg: S) -> Result<T, ErrorReported> {
        let mut diagnostic = self
            .tcx
            .sess
            .struct_err_with_code(msg.as_ref(), DiagnosticId::Error("LIQUID".to_string()));
        if let Some(span) = span {
            diagnostic.set_span(span);
        }
        diagnostic.emit();
        Err(ErrorReported)
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

fn scalar_to_int<'tcx>(
    tcx: TyCtxt<'tcx>,
    scalar: mir::interpret::Scalar,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> Option<i128> {
    let size = tcx
        .layout_of(ParamEnv::empty().with_reveal_all_normalized(tcx).and(ty))
        .unwrap()
        .size;
    scalar.to_int(size).ok()
}

fn scalar_to_uint<'tcx>(
    tcx: TyCtxt<'tcx>,
    scalar: mir::interpret::Scalar,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> Option<u128> {
    let size = tcx
        .layout_of(ParamEnv::empty().with_reveal_all_normalized(tcx).and(ty))
        .unwrap()
        .size;
    scalar.to_uint(size).ok()
}
