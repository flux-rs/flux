use liquid_rust_mir::{
    BBlock, BBlockId, Func, FuncBuilder, FuncId, Local, Operand, Rvalue, Statement, StatementKind,
    Terminator, TerminatorKind,
};
use liquid_rust_ty::{BaseTy, BinOp, IntSign, IntSize, Literal, UnOp};

use rustc_ast::ast::{IntTy, UintTy};
use rustc_hir::def_id::DefId;
use rustc_index::vec::IndexVec;
use rustc_middle::{
    bug, mir,
    ty::{ConstKind, ParamEnv, Ty as MirTy, TyCtxt, TyKind},
};
use rustc_span::{Span, DUMMY_SP};
use std::{collections::HashMap, fmt};

pub struct LowerCtx<'tcx, 'low> {
    tcx: TyCtxt<'tcx>,
    body: &'low mir::Body<'tcx>,
    locals: IndexVec<mir::Local, Local>,
    blocks: IndexVec<mir::BasicBlock, BBlockId>,
    func_ids: &'low HashMap<DefId, FuncId>,
}

impl<'tcx, 'low> LowerCtx<'tcx, 'low> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        body: &'low mir::Body<'tcx>,

        func_ids: &'low HashMap<DefId, FuncId>,
    ) -> Self {
        Self {
            tcx,
            body,
            locals: IndexVec::new(),
            blocks: IndexVec::new(),
            func_ids,
        }
    }

    pub fn lower_body(mut self) -> Result<FuncBuilder<Span>, LowerError> {
        self.body.lower(&mut self)
    }

    fn lower<T: Lower<'tcx>>(&mut self, term: &T) -> Result<T::Output, LowerError> {
        term.lower(self)
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
            LowerErrorKind::UnsupportedUnOp => " unary operator",
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
    UnsupportedUnOp,
    UnsupportedTerminator,
    UnsupportedConstant,
    UnsupportedRvalue,
}

trait Lower<'tcx> {
    type Output;

    fn lower(&self, lcx: &mut LowerCtx<'tcx, '_>) -> Result<Self::Output, LowerError>;
}

impl<'tcx> Lower<'tcx> for mir::Local {
    type Output = Local;

    fn lower(&self, lcx: &mut LowerCtx<'tcx, '_>) -> Result<Self::Output, LowerError> {
        if let Some(var) = lcx.locals.get(*self) {
            Ok(*var)
        } else {
            bug!("Undefined local `{:?}`.", self);
        }
    }
}
impl<'tcx> Lower<'tcx> for IntTy {
    type Output = IntSize;

    fn lower(&self, _lcx: &mut LowerCtx<'tcx, '_>) -> Result<Self::Output, LowerError> {
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

    fn lower(&self, _lcx: &mut LowerCtx<'tcx, '_>) -> Result<Self::Output, LowerError> {
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

    fn lower(&self, lcx: &mut LowerCtx<'tcx, '_>) -> Result<Self::Output, LowerError> {
        let base_ty = match self.kind() {
            TyKind::Bool => BaseTy::Bool,
            TyKind::Uint(uint_ty) => BaseTy::Int(IntSign::Unsigned, lcx.lower(uint_ty)?),
            TyKind::Int(int_ty) => BaseTy::Int(IntSign::Signed, lcx.lower(int_ty)?),
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
    type Output = Statement<Span>;
    fn lower(&self, lcx: &mut LowerCtx<'tcx, '_>) -> Result<Self::Output, LowerError> {
        let span = self.source_info.span;
        let kind = match &self.kind {
            mir::StatementKind::Assign(assign) => {
                let (place, rvalue) = assign.as_ref();
                let local = lcx.lower(place).map_err(|err| err.with_span(span))?;
                let rvalue = lcx.lower(rvalue).map_err(|err| err.with_span(span))?;
                StatementKind::Assign(local, rvalue)
            }
            mir::StatementKind::StorageLive(..)
            | mir::StatementKind::StorageDead(..)
            | mir::StatementKind::Nop => StatementKind::Noop,
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

        Ok(Statement { kind, span })
    }
}

impl<'tcx> Lower<'tcx> for mir::Place<'tcx> {
    type Output = Local;
    fn lower(&self, lcx: &mut LowerCtx<'tcx, '_>) -> Result<Self::Output, LowerError> {
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
            lcx.lower(local)
        }
    }
}

impl<'tcx> Lower<'tcx> for mir::Rvalue<'tcx> {
    type Output = Rvalue;
    fn lower(&self, lcx: &mut LowerCtx<'tcx, '_>) -> Result<Self::Output, LowerError> {
        let rvalue = match self {
            mir::Rvalue::Use(operand) => Rvalue::Use(lcx.lower(operand)?),
            mir::Rvalue::BinaryOp(bin_op, op1, op2) => {
                let op_ty = lcx.lower(&op1.ty(lcx.body, lcx.tcx))?;

                let bin_op = match (bin_op, op_ty) {
                    (mir::BinOp::Add, BaseTy::Int(sign, size)) => BinOp::Add(sign, size),
                    (mir::BinOp::Sub, BaseTy::Int(sign, size)) => BinOp::Sub(sign, size),
                    (mir::BinOp::Mul, BaseTy::Int(sign, size)) => BinOp::Mul(sign, size),
                    (mir::BinOp::Div, BaseTy::Int(sign, size)) => BinOp::Div(sign, size),
                    (mir::BinOp::Rem, BaseTy::Int(sign, size)) => BinOp::Rem(sign, size),
                    (mir::BinOp::Eq, base_ty) => BinOp::Eq(base_ty),
                    (mir::BinOp::Ne, base_ty) => BinOp::Neq(base_ty),
                    (mir::BinOp::Lt, BaseTy::Int(sign, size)) => BinOp::Lt(sign, size),
                    (mir::BinOp::Gt, BaseTy::Int(sign, size)) => BinOp::Gt(sign, size),
                    (mir::BinOp::Le, BaseTy::Int(sign, size)) => BinOp::Lte(sign, size),
                    (mir::BinOp::Ge, BaseTy::Int(sign, size)) => BinOp::Gte(sign, size),
                    (bin_op, base_ty) => {
                        return Err(LowerError::new(
                            LowerErrorKind::UnsupportedBinOp,
                            format!(
                                "{} with {} arguments",
                                bin_op.to_hir_binop().as_str(),
                                base_ty
                            ),
                        ))
                    }
                };

                let op1 = lcx.lower(op1)?;
                let op2 = lcx.lower(op2)?;
                Rvalue::BinApp(bin_op, op1, op2)
            }
            mir::Rvalue::UnaryOp(un_op, op) => {
                let op_ty = lcx.lower(&op.ty(lcx.body, lcx.tcx))?;

                let un_op = match (un_op, op_ty) {
                    (mir::UnOp::Neg, BaseTy::Int(sign, size)) => UnOp::Neg(sign, size),
                    (mir::UnOp::Not, BaseTy::Bool) => UnOp::Not,
                    (mir::UnOp::Neg, base_ty) => {
                        return Err(LowerError::new(
                            LowerErrorKind::UnsupportedUnOp,
                            format!("- with {} arguments", base_ty),
                        ))
                    }
                    (mir::UnOp::Not, base_ty) => {
                        return Err(LowerError::new(
                            LowerErrorKind::UnsupportedUnOp,
                            format!("! with {} arguments", base_ty),
                        ))
                    }
                };

                let op = lcx.lower(op)?;
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
    fn lower(&self, lcx: &mut LowerCtx<'tcx, '_>) -> Result<Self::Output, LowerError> {
        let operand = match self {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                let place = lcx.lower(place)?;
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
                                Literal::new(bits, BaseTy::Bool)
                            }
                            TyKind::Uint(uint_ty) => {
                                let bits =
                                    literal.eval_bits(lcx.tcx, ParamEnv::empty(), literal.ty);
                                Literal::new(
                                    bits,
                                    BaseTy::Int(IntSign::Unsigned, lcx.lower(uint_ty)?),
                                )
                            }
                            TyKind::Int(int_ty) => {
                                let bits =
                                    literal.eval_bits(lcx.tcx, ParamEnv::empty(), literal.ty);
                                Literal::new(bits, BaseTy::Int(IntSign::Signed, lcx.lower(int_ty)?))
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
    fn lower(&self, lcx: &mut LowerCtx<'tcx, '_>) -> Result<Self::Output, LowerError> {
        if let Some(block_id) = lcx.blocks.get(*self) {
            Ok(*block_id)
        } else {
            bug!("Undefined Basic Block `{:?}`.", self);
        }
    }
}

impl<'tcx> Lower<'tcx> for mir::Terminator<'tcx> {
    type Output = Terminator<Span>;
    fn lower(&self, lcx: &mut LowerCtx<'tcx, '_>) -> Result<Self::Output, LowerError> {
        let span = self.source_info.span;
        let kind = match &self.kind {
            mir::TerminatorKind::Return => TerminatorKind::Return,
            mir::TerminatorKind::Goto { target } => TerminatorKind::Goto(lcx.lower(target)?),
            mir::TerminatorKind::Assert {
                cond,
                expected,
                target,
                ..
            } => TerminatorKind::Assert(lcx.lower(cond)?, *expected, lcx.lower(target)?),
            mir::TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } => match func {
                mir::Operand::Constant(constant) => {
                    let (lhs, bb_id) = match destination {
                        Some((place, target)) => (lcx.lower(place)?, lcx.lower(target)?),
                        None => todo!(),
                    };

                    let func_id = match constant.literal.ty.kind() {
                        TyKind::FnDef(def_id, _) => *lcx.func_ids.get(def_id).unwrap(),
                        _ => todo!(),
                    };

                    let args = args
                        .iter()
                        .map(|arg| lcx.lower(arg))
                        .collect::<Result<Box<[_]>, _>>()?;

                    TerminatorKind::Call(lhs, func_id, args, bb_id)
                }
                _ => todo!(),
            },
            mir::TerminatorKind::SwitchInt {
                discr: mir::Operand::Copy(discr),
                targets,
                ..
            }
            | mir::TerminatorKind::SwitchInt {
                discr: mir::Operand::Move(discr),
                targets,
                ..
            } => {
                let discr = lcx.lower(discr)?;

                let otherwise = lcx.lower(&targets.otherwise())?;

                let targets = targets
                    .iter()
                    .map(|(bits, target)| Ok((bits, lcx.lower(&target)?)))
                    .collect::<Result<Box<[(u128, BBlockId)]>, _>>()?;

                TerminatorKind::Switch(discr, targets, otherwise)
            }
            kind => {
                let msg = match kind {
                    mir::TerminatorKind::Goto { .. }
                    | mir::TerminatorKind::Return
                    | mir::TerminatorKind::Assert { .. } => {
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
                    mir::TerminatorKind::Yield { .. } => "yield",
                    mir::TerminatorKind::FalseEdge { .. } => "false edge",
                    mir::TerminatorKind::FalseUnwind { .. } => "false unwind",
                    mir::TerminatorKind::InlineAsm { .. } => "inline assembly",
                };

                return Err(LowerError::new(LowerErrorKind::UnsupportedTerminator, msg)
                    .with_span(self.source_info.span));
            }
        };

        Ok(Terminator { kind, span })
    }
}

impl<'tcx> Lower<'tcx> for mir::BasicBlockData<'tcx> {
    type Output = BBlock<Span>;
    fn lower(&self, lcx: &mut LowerCtx<'tcx, '_>) -> Result<Self::Output, LowerError> {
        let mut builder = BBlock::builder();
        for statement in &self.statements {
            builder.add_statement(lcx.lower(statement)?);
        }

        builder.add_terminator(lcx.lower(self.terminator.as_ref().unwrap())?);

        Ok(builder.build().unwrap())
    }
}

impl<'tcx> Lower<'tcx> for mir::Body<'tcx> {
    type Output = FuncBuilder<Span>;

    fn lower(&self, lcx: &mut LowerCtx<'tcx, '_>) -> Result<Self::Output, LowerError> {
        let arity = self.arg_count;

        let mut builder = Func::builder(arity, self.basic_blocks().len());

        for decl in &self.local_decls {
            let ty = lcx
                .lower(&decl.ty)
                .map_err(|err| err.with_span(decl.source_info.span))?;
            let local = builder.add_local_decl(ty);
            lcx.locals.push(local);
        }

        for bb_id in builder.bblock_ids() {
            lcx.blocks.push(bb_id);
        }

        for (basic_block, basic_block_data) in self.basic_blocks().iter_enumerated() {
            let bb_id = lcx.blocks[basic_block];
            let bb = lcx
                .lower(basic_block_data)
                .map_err(|err| err.with_span(self.span))?;
            builder.set_bblock(bb_id, bb);
        }

        Ok(builder)
    }
}
