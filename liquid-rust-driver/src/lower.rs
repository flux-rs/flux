use rustc_ast::ast::{IntTy, UintTy};
use rustc_hir::def_id::DefId;
use rustc_middle::mir;
use rustc_middle::ty::{ConstKind, List, ParamEnv, Ty as MirTy, TyCtxt, TyKind};

use std::collections::HashMap;

use liquid_rust_lang::{
    ast::Annotation,
    ctx::UnifyError,
    ir::{
        BasicBlock, BinOp, BlockId, Func, FuncId, Literal, Local, Operand, Rvalue, Statement,
        Terminator, UnOp,
    },
    ty::{BaseTy, IntSize},
    Generator,
};

pub struct LowerCtx<'tcx> {
    tcx: TyCtxt<'tcx>,
    locals: HashMap<mir::Local, Local>,
    local_gen: Generator<Local>,
    basic_blocks: HashMap<mir::BasicBlock, BlockId>,
    block_id_gen: Generator<BlockId>,
    func_ids: HashMap<DefId, FuncId>,
    func_id_gen: Generator<FuncId>,
    annotations: Vec<Annotation>,
}

impl<'tcx> LowerCtx<'tcx> {
    pub fn from_tcx(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            locals: HashMap::default(),
            local_gen: Local::generator(),
            basic_blocks: HashMap::default(),
            block_id_gen: BlockId::generator(),
            func_ids: HashMap::default(),
            func_id_gen: FuncId::generator(),
            annotations: Vec::new(),
        }
    }

    pub fn lower_body(
        &mut self,
        def_id: DefId,
        body: mir::Body<'tcx>,
    ) -> Result<(FuncId, Func), LowerError> {
        let func_id = self.new_func_id();
        self.func_ids.insert(def_id, func_id);
        let mut func = body.lower(self)?;

        for ann in self.annotations.drain(..) {
            match ann {
                Annotation::Ty(ast_ty) => func.set_ty(&ast_ty).map_err(LowerError::UnifyError)?,
            }
        }
        Ok((func_id, func))
    }

    fn new_local(&mut self) -> Local {
        self.local_gen.generate()
    }

    fn new_block_id(&mut self) -> BlockId {
        self.block_id_gen.generate()
    }

    fn new_func_id(&mut self) -> FuncId {
        self.func_id_gen.generate()
    }

    pub fn set_annotations(&mut self, annotations: Vec<Annotation>) {
        self.annotations = annotations;
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
    UndefinedDefId(DefId),
    UnifyError(UnifyError),
}

trait Lower<'tcx> {
    type Output;

    fn lower(&self, lcx: &mut LowerCtx<'tcx>) -> Result<Self::Output, LowerError<'tcx>>;
}

impl<'tcx> Lower<'tcx> for mir::Local {
    type Output = Local;

    fn lower(&self, lcx: &mut LowerCtx<'tcx>) -> Result<Self::Output, LowerError<'tcx>> {
        if let Some(var) = lcx.locals.get(self) {
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
            if let Some(local) = lcx.locals.get(local) {
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
            mir::Operand::Copy(place) => {
                let place = place.lower(lcx)?;
                Operand::Copy(place)
            }
            mir::Operand::Move(place) => {
                let place = place.lower(lcx)?;
                Operand::Move(place)
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
                            TyKind::FnDef(def_id, _) => {
                                if let Some(func_id) = lcx.func_ids.get(def_id) {
                                    Literal::Fn(*func_id)
                                } else {
                                    return Err(LowerError::UndefinedDefId(*def_id));
                                }
                            }
                            _ => return Err(LowerError::UnsupportedTy(literal.ty)),
                        };

                        Operand::Lit(literal)
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
    type Output = BlockId;
    fn lower(&self, lcx: &mut LowerCtx<'tcx>) -> Result<Self::Output, LowerError<'tcx>> {
        if let Some(block_id) = lcx.basic_blocks.get(self) {
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
            mir::TerminatorKind::Goto { .. } => todo!(),
            mir::TerminatorKind::SwitchInt { .. } => todo!(),
            mir::TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } => {
                let func = func.lower(lcx)?;
                let args = args
                    .iter()
                    .map(|arg| arg.lower(lcx))
                    .collect::<Result<Vec<Operand>, _>>()?;

                let (place, target) = destination.unwrap();
                let place = place.lower(lcx)?;
                let target = target.lower(lcx)?;

                Terminator::Call(place, func, args, target)
            }
            _ => return Err(LowerError::UnsupportedTerminator(self.clone())),
        };

        Ok(terminator)
    }
}

impl<'tcx> Lower<'tcx> for mir::BasicBlockData<'tcx> {
    type Output = BasicBlock;
    fn lower(&self, lcx: &mut LowerCtx<'tcx>) -> Result<Self::Output, LowerError<'tcx>> {
        let statements = self
            .statements
            .iter()
            .map(|statement| statement.lower(lcx))
            .collect::<Result<Vec<Statement>, _>>()?;

        let terminator = self.terminator.as_ref().unwrap().lower(lcx)?;

        Ok(BasicBlock(statements, terminator))
    }
}

impl<'tcx> Lower<'tcx> for mir::Body<'tcx> {
    type Output = Func;

    fn lower(&self, lcx: &mut LowerCtx<'tcx>) -> Result<Self::Output, LowerError<'tcx>> {
        lcx.local_gen = Local::generator();
        lcx.block_id_gen = BlockId::generator();

        let arg_count = self.arg_count;

        let mut local_decls = Vec::new();
        for (mir_local, mir_local_decl) in self.local_decls.iter_enumerated() {
            let local = lcx.new_local();
            lcx.locals.insert(mir_local, local);

            let ty = mir_local_decl.ty.lower(lcx)?;
            local_decls.push((local, ty));
        }

        let mut basic_blocks = HashMap::new();
        for (bb, _) in self.basic_blocks().iter_enumerated() {
            let block_id = lcx.new_block_id();
            lcx.basic_blocks.insert(bb, block_id);
        }

        for (bb, bb_data) in self.basic_blocks().iter_enumerated() {
            let block_id = *lcx.basic_blocks.get(&bb).unwrap();
            let block = bb_data.lower(lcx)?;
            basic_blocks.insert(block_id, block);
        }

        Ok(Func {
            arg_count,
            local_decls,
            basic_blocks,
            ty: None,
        })
    }
}
