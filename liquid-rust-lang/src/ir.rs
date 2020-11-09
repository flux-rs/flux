use std::collections::HashMap;

use crate::{
    ast::Ty as AstTy,
    ctx::{FnContext, UnifyError},
    ty::{BaseTy, IntSize, Ty},
    Generator,
};

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct BlockId(usize);

impl BlockId {
    pub fn generator() -> Generator<Self> {
        Generator::new(Self)
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct FuncId(usize);

impl FuncId {
    pub fn generator() -> Generator<Self> {
        Generator::new(Self)
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct Local(usize);

impl Local {
    pub fn generator() -> Generator<Self> {
        Generator::new(Self)
    }

    pub fn args(arity: usize) -> impl Iterator<Item = Self> {
        (0..arity).map(|index| Self(index + 1))
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum Literal {
    Bool(bool),
    Int(i128, IntSize),
    Uint(u128, IntSize),
    Unit,
    Fn(FuncId),
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    And,
    Or,
    Eq,
    Neq,
    Lt,
    Gt,
    Lte,
    Gte,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum UnOp {
    Not,
    Neg,
}

#[derive(Debug)]
pub enum Operand {
    Move(Local),
    Copy(Local),
    Lit(Literal),
}

#[derive(Debug)]
pub enum Rvalue {
    Use(Operand),
    BinApp(BinOp, Operand, Operand),
    UnApp(UnOp, Operand),
}

#[derive(Debug)]
pub enum Statement {
    Assign(Local, Rvalue),
    Noop,
}

#[derive(Debug)]
pub struct Branch(pub Literal, pub BlockId);

#[derive(Debug)]
pub enum Terminator {
    Return,
    Goto(BlockId),
    Switch(Local, Vec<Branch>, BlockId),
    Call(Local, Operand, Vec<Operand>, BlockId),
}

#[derive(Debug)]
pub struct BasicBlock(pub Vec<Statement>, pub Terminator);

#[derive(Debug)]
pub struct Func {
    pub arg_count: usize,
    pub local_decls: Vec<(Local, BaseTy)>,
    pub basic_blocks: HashMap<BlockId, BasicBlock>,
    pub ty: Option<Ty>,
}

impl Func {
    pub fn set_ty(&mut self, ty: &AstTy) -> Result<(), UnifyError> {
        let mut ctx = FnContext::new(self);
        let ty = ctx.check_ty(ty)?;
        self.ty = Some(ty);

        Ok(())
    }
}

pub struct Program(pub HashMap<FuncId, Func>);
