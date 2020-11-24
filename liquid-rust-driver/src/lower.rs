use liquid_rust_common::{
    ir::{
        BBlock, BBlockId, BinOp, Func, FuncBuilder, Literal, Local, Operand, Rvalue, Statement,
        Terminator, UnOp,
    },
    ty::{BaseTy, IntSize},
};

use rustc_ast::ast::{IntTy, UintTy};
use rustc_index::vec::IndexVec;
use rustc_middle::mir;
use rustc_middle::ty::{ConstKind, List, ParamEnv, Ty as MirTy, TyCtxt, TyKind};

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
pub enum LowerError<'tcx> {
    UndefinedLocal(mir::Local),
    UnsupportedTy(MirTy<'tcx>),
    Projection(&'tcx List<mir::PlaceElem<'tcx>>),
    UnsupportedRvalue(mir::Rvalue<'tcx>),
    UnsupportedConstKind(ConstKind<'tcx>),
    UnsupportedTerminator(mir::Terminator<'tcx>),
    UnsupportedStatement(mir::Statement<'tcx>),
    UnsupportedBinOp(mir::BinOp),
    UndefinedBasicBlock(mir::BasicBlock),
}

trait Lower<'tcx> {
    type Output;

    fn lower(&self, lcx: &mut LowerCtx<'tcx>) -> Result<Self::Output, LowerError<'tcx>>;
}

impl<'tcx> Lower<'tcx> for mir::Local {
    type Output = Local;

    fn lower(&self, lcx: &mut LowerCtx<'tcx>) -> Result<Self::Output, LowerError<'tcx>> {
        if let Some(var) = lcx.locals.get(*self) {
            Ok(*var)
        } else {
            Err(LowerError::UndefinedLocal(*self))
        }
    }
}
impl<'tcx> Lower<'tcx> for IntTy {
    type Output = IntSize;

    fn lower(&self, _lcx: &mut LowerCtx<'tcx>) -> Result<Self::Output, LowerError<'tcx>> {
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

    fn lower(&self, _lcx: &mut LowerCtx<'tcx>) -> Result<Self::Output, LowerError<'tcx>> {
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

    fn lower(&self, lcx: &mut LowerCtx<'tcx>) -> Result<Self::Output, LowerError<'tcx>> {
        let base_ty = match self.kind() {
            TyKind::Bool => BaseTy::Bool,
            TyKind::Uint(uint_ty) => BaseTy::Uint(uint_ty.lower(lcx)?),
            TyKind::Int(int_ty) => BaseTy::Int(int_ty.lower(lcx)?),
            _ => return Err(LowerError::UnsupportedTy(self)),
        };

        Ok(base_ty)
    }
}

impl<'tcx> Lower<'tcx> for mir::Statement<'tcx> {
    type Output = Statement;
    fn lower(&self, lcx: &mut LowerCtx<'tcx>) -> Result<Self::Output, LowerError<'tcx>> {
        let statement = match &self.kind {
            mir::StatementKind::Assign(assign) => {
                let (place, rvalue) = assign.as_ref();
                let local = place.lower(lcx)?;
                let rvalue = rvalue.lower(lcx)?;
                Statement::Assign(local, rvalue)
            }
            mir::StatementKind::StorageLive(_) | mir::StatementKind::StorageDead(_) => {
                Statement::Noop
            }
            _ => return Err(LowerError::UnsupportedStatement(self.clone())),
        };

        Ok(statement)
    }
}

impl<'tcx> Lower<'tcx> for mir::Place<'tcx> {
    type Output = Local;
    fn lower(&self, lcx: &mut LowerCtx<'tcx>) -> Result<Self::Output, LowerError<'tcx>> {
        let mir::Place { local, projection } = self;

        if projection.iter().count() == 0 {
            if let Some(local) = lcx.locals.get(*local) {
                Ok(*local)
            } else {
                Err(LowerError::UndefinedLocal(*local))
            }
        } else {
            Err(LowerError::Projection(projection))
        }
    }
}

impl<'tcx> Lower<'tcx> for mir::Rvalue<'tcx> {
    type Output = Rvalue;
    fn lower(&self, lcx: &mut LowerCtx<'tcx>) -> Result<Self::Output, LowerError<'tcx>> {
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
                    _ => return Err(LowerError::UnsupportedBinOp(*bin_op)),
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
            rvalue => return Err(LowerError::UnsupportedRvalue(rvalue.clone())),
        };

        Ok(rvalue)
    }
}

impl<'tcx> Lower<'tcx> for mir::Operand<'tcx> {
    type Output = Operand;
    fn lower(&self, lcx: &mut LowerCtx<'tcx>) -> Result<Self::Output, LowerError<'tcx>> {
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
                            _ => return Err(LowerError::UnsupportedTy(literal.ty)),
                        };

                        Operand::Literal(literal)
                    }
                    kind => {
                        return Err(LowerError::UnsupportedConstKind(kind));
                    }
                }
            }
        };

        Ok(operand)
    }
}

impl<'tcx> Lower<'tcx> for mir::BasicBlock {
    type Output = BBlockId;
    fn lower(&self, lcx: &mut LowerCtx<'tcx>) -> Result<Self::Output, LowerError<'tcx>> {
        if let Some(block_id) = lcx.blocks.get(*self) {
            Ok(*block_id)
        } else {
            Err(LowerError::UndefinedBasicBlock(*self))
        }
    }
}

impl<'tcx> Lower<'tcx> for mir::Terminator<'tcx> {
    type Output = Terminator;
    fn lower(&self, lcx: &mut LowerCtx<'tcx>) -> Result<Self::Output, LowerError<'tcx>> {
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
            _ => return Err(LowerError::UnsupportedTerminator(self.clone())),
        };

        Ok(terminator)
    }
}

impl<'tcx> Lower<'tcx> for mir::BasicBlockData<'tcx> {
    type Output = BBlock;
    fn lower(&self, lcx: &mut LowerCtx<'tcx>) -> Result<Self::Output, LowerError<'tcx>> {
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

    fn lower(&self, lcx: &mut LowerCtx<'tcx>) -> Result<Self::Output, LowerError<'tcx>> {
        let arity = self.arg_count;

        let mut builder = Func::builder(arity, self.basic_blocks().len());

        for decl in &self.local_decls {
            let ty = decl.ty.lower(lcx)?;
            let local = builder.add_local_decl(ty);
            lcx.locals.push(local);
        }

        for bb_id in builder.bblock_ids() {
            lcx.blocks.push(bb_id);
        }

        for (basic_block, basic_block_data) in self.basic_blocks().iter_enumerated() {
            let bb_id = lcx.blocks[basic_block];
            let bb = basic_block_data.lower(lcx)?;
            builder.set_bblock(bb_id, bb);
        }

        Ok(builder)
    }
}
