mod literal;

pub use literal::Literal;

use std::collections::HashMap;

use crate::{
    generator::{Generable, Generator},
    ty::BaseTy,
};

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct BlockId(usize);

impl Generable for BlockId {
    fn generator() -> Generator<Self> {
        Generator::new(Self)
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct FuncId(usize);

impl Generable for FuncId {
    fn generator() -> Generator<Self> {
        Generator::new(Self)
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct Local(usize);

impl Generable for Local {
    fn generator() -> Generator<Self> {
        Generator::new(Self)
    }
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
    pub args: Vec<(Local, BaseTy)>,
    pub ret_local: Local,
    pub ret_ty: BaseTy,
    pub locals: Vec<(Local, BaseTy)>,
    pub basic_blocks: HashMap<BlockId, BasicBlock>,
}
