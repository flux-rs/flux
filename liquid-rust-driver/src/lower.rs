use liquid_rust_common::{
    ir::{
        BBlock, BBlockId, BinOp, Func, FuncBuilder, Literal, Local, Operand, Rvalue, Statement,
        Terminator, UnOp,
    },
    ty::{BaseTy, IntSize},
};

use rustc_ast::ast::{IntTy, UintTy};
use rustc_index::vec::IndexVec;
use rustc_middle::{
    bug, mir,
    ty::{ConstKind, ParamEnv, Ty as MirTy, TyCtxt, TyKind},
};
use rustc_span::{Span, DUMMY_SP};
use std::fmt;

pub struct LowerCtx<'tcx> {
    tcx: TyCtxt<'tcx>,
    locals: IndexVec<mir::Local, Local>,
    blocks: IndexVec<mir::BasicBlock, BBlockId>,
}

impl<'tcx> LowerCtx<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            locals: IndexVec::new(),
            blocks: IndexVec::new(),
        }
    }

    pub fn lower_body(&mut self, body: &mir::Body<'tcx>) -> Result<FuncBuilder, LowerError> {
        body.lower(self)
    }
}

#[derive(Debug)]
pub struct LowerError {
    span: Span,
    kind: LowerErrorKind,
    msg: String,
}

impl LowerError {
    fn new(kind: LowerErrorKind, msg: impl Into<String>) -> Self {
        Self {
            span: DUMMY_SP,
            kind,
            msg: msg.into(),
        }
    }

    pub fn span(&self) -> Span {
        self.span
    }

    pub fn with_span(mut self, span: Span) -> Self {
        if self.span.is_dummy() {
            self.span = span;
        }
        self
    }

    pub fn msg(&self) -> &str {
        &self.msg
    }
}

impl fmt::Display for LowerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let term = match self.kind {
            LowerErrorKind::UnsupportedTy => "type",
            LowerErrorKind::UnsupportedBinOp => " binary operator",
            LowerErrorKind::UnsupportedConstant => " constant",
            LowerErrorKind::UnsupportedStatement => "statement",
            LowerErrorKind::UnsupportedTerminator => "terminator",
            LowerErrorKind::UnsupportedRvalue => "rvalue",
            LowerErrorKind::HasProjections => {
                return write!(f, "projections are not supported: found {}.", self.msg())
            }
        };

        write!(f, "unsupported {}: found {}.", term, self.msg())
    }
}

#[derive(Debug)]
enum LowerErrorKind {
    UnsupportedTy,
    UnsupportedStatement,
    HasProjections,
    UnsupportedBinOp,
    UnsupportedTerminator,
    UnsupportedConstant,
    UnsupportedRvalue,
}

trait Lower<'tcx> {
    type Output;

    fn lower(&self, lcx: &mut LowerCtx<'tcx>) -> Result<Self::Output, LowerError>;
}

impl<'tcx> Lower<'tcx> for mir::Local {
    type Output = Local;

    fn lower(&self, lcx: &mut LowerCtx<'tcx>) -> Result<Self::Output, LowerError> {
        if let Some(var) = lcx.locals.get(*self) {
            Ok(*var)
        } else {
            bug!("Undefined local `{:?}`.", self);
        }
    }
}
impl<'tcx> Lower<'tcx> for IntTy {
    type Output = IntSize;

    fn lower(&self, _lcx: &mut LowerCtx<'tcx>) -> Result<Self::Output, LowerError> {
        Ok(match self {
            IntTy::I8 => IntSize::Size8,
            IntTy::I16 => IntSize::Size16,
            IntTy::I32 => IntSize::Size32,
            IntTy::I64 => IntSize::Size64,
            IntTy::I128 => IntSize::Size128,
            IntTy::Isize => IntSize::SizePtr,
        })
    }
}

impl<'tcx> Lower<'tcx> for UintTy {
    type Output = IntSize;

    fn lower(&self, _lcx: &mut LowerCtx<'tcx>) -> Result<Self::Output, LowerError> {
        Ok(match self {
            UintTy::U8 => IntSize::Size8,
            UintTy::U16 => IntSize::Size16,
            UintTy::U32 => IntSize::Size32,
            UintTy::U64 => IntSize::Size64,
            UintTy::U128 => IntSize::Size128,
            UintTy::Usize => IntSize::SizePtr,
        })
    }
}

impl<'tcx> Lower<'tcx> for MirTy<'tcx> {
    type Output = BaseTy;

    fn lower(&self, lcx: &mut LowerCtx<'tcx>) -> Result<Self::Output, LowerError> {
        let base_ty = match self.kind() {
            TyKind::Bool => BaseTy::Bool,
            TyKind::Uint(uint_ty) => BaseTy::Uint(uint_ty.lower(lcx)?),
            TyKind::Int(int_ty) => BaseTy::Int(int_ty.lower(lcx)?),
            _ => {
                return Err(LowerError::new(
                    LowerErrorKind::UnsupportedTy,
                    self.sort_string(lcx.tcx),
                ));
            }
        };

        Ok(base_ty)
    }
}

impl<'tcx> Lower<'tcx> for mir::Statement<'tcx> {
    type Output = Statement;
    fn lower(&self, lcx: &mut LowerCtx<'tcx>) -> Result<Self::Output, LowerError> {
        let span = self.source_info.span;
        let statement = match &self.kind {
            mir::StatementKind::Assign(assign) => {
                let (place, rvalue) = assign.as_ref();
                let local = place.lower(lcx).map_err(|err| err.with_span(span))?;
                let rvalue = rvalue.lower(lcx).map_err(|err| err.with_span(span))?;
                Statement::Assign(local, rvalue)
            }
            mir::StatementKind::StorageLive(..)
            | mir::StatementKind::StorageDead(..)
            | mir::StatementKind::Nop => Statement::Noop,
            statement => {
                let msg = match statement {
                    mir::StatementKind::Assign(..)
                    | mir::StatementKind::StorageLive(..)
                    | mir::StatementKind::StorageDead(..)
                    | mir::StatementKind::Nop => unreachable!(),
                    mir::StatementKind::FakeRead(..) => "fake read",
                    mir::StatementKind::SetDiscriminant { .. } => "discriminant write",
                    mir::StatementKind::LlvmInlineAsm(..) => "inline assembly",
                    mir::StatementKind::Retag(..) => "retagging",
                    mir::StatementKind::AscribeUserType(..) => "type ascription",
                    mir::StatementKind::Coverage(..) => "coverage",
                };

                return Err(
                    LowerError::new(LowerErrorKind::UnsupportedStatement, msg).with_span(span)
                );
            }
        };

        Ok(statement)
    }
}

impl<'tcx> Lower<'tcx> for mir::Place<'tcx> {
    type Output = Local;
    fn lower(&self, lcx: &mut LowerCtx<'tcx>) -> Result<Self::Output, LowerError> {
        let mir::Place { local, projection } = self;

        if let Some(elem) = projection.iter().next() {
            let msg = match elem {
                mir::ProjectionElem::Deref => "dereference",
                mir::ProjectionElem::Field(..) => "field access",
                mir::ProjectionElem::Index(..) => "indexing operation",
                mir::ProjectionElem::ConstantIndex { .. }
                | mir::ProjectionElem::Subslice { .. } => "slice pattern",
                mir::ProjectionElem::Downcast(..) => "enum downcast",
            };

            Err(LowerError::new(LowerErrorKind::HasProjections, msg))
        } else {
            local.lower(lcx)
        }
    }
}

impl<'tcx> Lower<'tcx> for mir::Rvalue<'tcx> {
    type Output = Rvalue;
    fn lower(&self, lcx: &mut LowerCtx<'tcx>) -> Result<Self::Output, LowerError> {
        let rvalue = match self {
            mir::Rvalue::Use(operand) => Rvalue::Use(operand.lower(lcx)?),
            mir::Rvalue::BinaryOp(bin_op, op1, op2) => {
                let bin_op = match bin_op {
                    mir::BinOp::Add => BinOp::Add,
                    mir::BinOp::Sub => BinOp::Sub,
                    mir::BinOp::Mul => BinOp::Mul,
                    mir::BinOp::Eq => BinOp::Eq,
                    mir::BinOp::Ne => BinOp::Neq,
                    mir::BinOp::Lt => BinOp::Lt,
                    mir::BinOp::Gt => BinOp::Gt,
                    mir::BinOp::Le => BinOp::Lte,
                    mir::BinOp::Ge => BinOp::Gte,
                    _ => {
                        return Err(LowerError::new(
                            LowerErrorKind::UnsupportedBinOp,
                            bin_op.to_hir_binop().as_str(),
                        ))
                    }
                };
                let op1 = op1.lower(lcx)?;
                let op2 = op2.lower(lcx)?;
                Rvalue::BinApp(bin_op, op1, op2)
            }
            mir::Rvalue::UnaryOp(un_op, op) => {
                let un_op = match un_op {
                    mir::UnOp::Neg => UnOp::Neg,
                    mir::UnOp::Not => UnOp::Not,
                };
                let op = op.lower(lcx)?;
                Rvalue::UnApp(un_op, op)
            }
            rvalue => {
                let msg = match rvalue {
                    mir::Rvalue::Use(..) | mir::Rvalue::BinaryOp(..) | mir::Rvalue::UnaryOp(..) => {
                        unreachable!()
                    }
                    mir::Rvalue::Repeat(..) => "repeat",
                    mir::Rvalue::Ref(..) => "reference",
                    mir::Rvalue::ThreadLocalRef(..) => "local static access",
                    mir::Rvalue::AddressOf(..) => "raw pointer",
                    mir::Rvalue::Len(..) => "length of array or slice",
                    mir::Rvalue::Cast(..) => "cast",
                    mir::Rvalue::CheckedBinaryOp(..) => "checked binary operation",
                    mir::Rvalue::NullaryOp(..) => "nullary operation",
                    mir::Rvalue::Discriminant(..) => "discriminant read",
                    mir::Rvalue::Aggregate(..) => "value aggregation",
                };

                return Err(LowerError::new(LowerErrorKind::UnsupportedRvalue, msg));
            }
        };

        Ok(rvalue)
    }
}

impl<'tcx> Lower<'tcx> for mir::Operand<'tcx> {
    type Output = Operand;
    fn lower(&self, lcx: &mut LowerCtx<'tcx>) -> Result<Self::Output, LowerError> {
        let operand = match self {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                let place = place.lower(lcx)?;
                Operand::Local(place)
            }
            mir::Operand::Constant(constant) => {
                let literal = constant.literal;
                match literal.val {
                    ConstKind::Value(mir::interpret::ConstValue::Scalar(_)) => {
                        let literal = match literal.ty.kind() {
                            TyKind::Bool => {
                                let bits =
                                    literal.eval_bits(lcx.tcx, ParamEnv::empty(), literal.ty);
                                Literal::Bool(bits != 0)
                            }
                            TyKind::Uint(uint_ty) => {
                                let bits =
                                    literal.eval_bits(lcx.tcx, ParamEnv::empty(), literal.ty);
                                Literal::Uint(bits, uint_ty.lower(lcx)?)
                            }
                            TyKind::Int(int_ty) => {
                                let bits =
                                    literal.eval_bits(lcx.tcx, ParamEnv::empty(), literal.ty);
                                Literal::Int(bits as i128, int_ty.lower(lcx)?)
                            }
                            _ => {
                                return Err(LowerError::new(
                                    LowerErrorKind::UnsupportedConstant,
                                    constant.to_string(),
                                )
                                .with_span(constant.span))
                            }
                        };

                        Operand::Literal(literal)
                    }
                    _ => {
                        return Err(LowerError::new(
                            LowerErrorKind::UnsupportedConstant,
                            constant.to_string(),
                        )
                        .with_span(constant.span))
                    }
                }
            }
        };

        Ok(operand)
    }
}

impl<'tcx> Lower<'tcx> for mir::BasicBlock {
    type Output = BBlockId;
    fn lower(&self, lcx: &mut LowerCtx<'tcx>) -> Result<Self::Output, LowerError> {
        if let Some(block_id) = lcx.blocks.get(*self) {
            Ok(*block_id)
        } else {
            bug!("Undefined Basic Block `{:?}`.", self);
        }
    }
}

impl<'tcx> Lower<'tcx> for mir::Terminator<'tcx> {
    type Output = Terminator;
    fn lower(&self, lcx: &mut LowerCtx<'tcx>) -> Result<Self::Output, LowerError> {
        let terminator = match &self.kind {
            mir::TerminatorKind::Return => Terminator::Return,
            mir::TerminatorKind::Goto { target } => Terminator::Goto(target.lower(lcx)?),
            // mir::TerminatorKind::SwitchInt {
            //     discr,
            //     targets,
            //     switch_ty,
            //     ..
            // } => {
            //     let discr = discr.lower(lcx)?;
            //
            //     let otherwise = targets.otherwise().lower(lcx)?;
            //
            //     let targets = targets
            //         .iter()
            //         .map(|(bits, target)| {
            //             let lit = match switch_ty.kind() {
            //                 TyKind::Bool => Literal::Bool(bits != 0),
            //                 TyKind::Uint(size) => Literal::Uint(bits, size.lower(lcx)?),
            //                 TyKind::Int(size) => Literal::Int(bits as i128, size.lower(lcx)?),
            //                 TyKind::FnDef(def_id, _) => {
            //                     if let Some(func_id) = lcx.func_ids.get(def_id).copied() {
            //                         Literal::Fn(func_id)
            //                     } else {
            //                         return Err(LowerError::UndefinedDefId(*def_id));
            //                     }
            //                 }
            //
            //                 _ => return Err(LowerError::UnsupportedTy(*switch_ty)),
            //             };
            //             Ok(Branch(lit, target.lower(lcx)?))
            //         })
            //         .collect::<Result<Vec<Branch>, _>>()?;
            //
            //     Terminator::Switch(discr, targets, otherwise)
            // }
            // mir::TerminatorKind::Call {
            //     func,
            //     args,
            //     destination,
            //     ..
            // } => {
            //     let func = func.lower(lcx)?;
            //     let args = args
            //         .iter()
            //         .map(|arg| arg.lower(lcx))
            //         .collect::<Result<Vec<Operand>, _>>()?;
            //
            //     let (place, target) = destination.unwrap();
            //     let place = place.lower(lcx)?;
            //     let target = target.lower(lcx)?;
            //
            //     Terminator::Call(place, func, args, target)
            // }
            kind => {
                let msg = match kind {
                    mir::TerminatorKind::Goto { .. } | mir::TerminatorKind::Return => {
                        unreachable!()
                    }
                    mir::TerminatorKind::SwitchInt { .. } => "switch",
                    mir::TerminatorKind::Resume => "resume",
                    mir::TerminatorKind::Abort => "abort",
                    mir::TerminatorKind::Unreachable => "unreachable",
                    mir::TerminatorKind::Drop { .. }
                    | mir::TerminatorKind::DropAndReplace { .. }
                    | mir::TerminatorKind::GeneratorDrop => "drop",
                    mir::TerminatorKind::Call { .. } => "function call",
                    mir::TerminatorKind::Assert { .. } => "assertion",
                    mir::TerminatorKind::Yield { .. } => "yield",
                    mir::TerminatorKind::FalseEdge { .. } => "false edge",
                    mir::TerminatorKind::FalseUnwind { .. } => "false unwind",
                    mir::TerminatorKind::InlineAsm { .. } => "inline assembly",
                };

                return Err(LowerError::new(LowerErrorKind::UnsupportedTerminator, msg)
                    .with_span(self.source_info.span));
            }
        };

        Ok(terminator)
    }
}

impl<'tcx> Lower<'tcx> for mir::BasicBlockData<'tcx> {
    type Output = BBlock;
    fn lower(&self, lcx: &mut LowerCtx<'tcx>) -> Result<Self::Output, LowerError> {
        let mut builder = BBlock::builder();
        for statement in &self.statements {
            builder.add_statement(statement.lower(lcx)?);
        }

        builder.add_terminator(self.terminator.as_ref().unwrap().lower(lcx)?);

        Ok(builder.build().unwrap())
    }
}

impl<'tcx> Lower<'tcx> for mir::Body<'tcx> {
    type Output = FuncBuilder;

    fn lower(&self, lcx: &mut LowerCtx<'tcx>) -> Result<Self::Output, LowerError> {
        let arity = self.arg_count;

        let mut builder = Func::builder(arity, self.basic_blocks().len());

        for decl in &self.local_decls {
            let ty = decl
                .ty
                .lower(lcx)
                .map_err(|err| err.with_span(decl.source_info.span))?;
            let local = builder.add_local_decl(ty);
            lcx.locals.push(local);
        }

        for bb_id in builder.bblock_ids() {
            lcx.blocks.push(bb_id);
        }

        for (basic_block, basic_block_data) in self.basic_blocks().iter_enumerated() {
            let bb_id = lcx.blocks[basic_block];
            let bb = basic_block_data
                .lower(lcx)
                .map_err(|err| err.with_span(self.span))?;
            builder.set_bblock(bb_id, bb);
        }

        Ok(builder)
    }
}
