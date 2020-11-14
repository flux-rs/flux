mod literal;

pub use literal::Literal;

use std::{
    collections::BTreeMap,
    fmt::{Display, Formatter, Result},
};

use crate::{
    generator::{Generable, Generator},
    ty::BaseTy,
};

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct BlockId(usize);

impl Generable for BlockId {
    fn generator() -> Generator<Self> {
        Generator::new(Self)
    }
}

impl Display for BlockId {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "bb{}", self.0)
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct FuncId(usize);

impl Generable for FuncId {
    fn generator() -> Generator<Self> {
        Generator::new(Self)
    }
}
impl Display for FuncId {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "func{}", self.0)
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Local(usize);

impl Generable for Local {
    fn generator() -> Generator<Self> {
        Generator::new(Self)
    }
}

impl Display for Local {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "_{}", self.0)
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

impl Display for BinOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let s = match self {
            Self::Add => "+",
            Self::Sub => "-",
            Self::Mul => "*",
            Self::And => "&&",
            Self::Or => "||",
            Self::Eq => "==",
            Self::Neq => "!=",
            Self::Lt => "<",
            Self::Gt => ">",
            Self::Lte => "<=",
            Self::Gte => ">=",
        };

        s.fmt(f)
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum UnOp {
    Not,
    Neg,
}

impl Display for UnOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let s = match self {
            Self::Not => "!",
            Self::Neg => "-",
        };

        s.fmt(f)
    }
}

#[derive(Debug, Copy, Clone)]
pub enum Operand {
    Move(Local),
    Copy(Local),
    Lit(Literal),
}
impl Display for Operand {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Self::Move(local) | Self::Copy(local) => local.fmt(f),
            Self::Lit(lit) => lit.fmt(f),
        }
    }
}

#[derive(Debug)]
pub enum Rvalue {
    Use(Operand),
    BinApp(BinOp, Operand, Operand),
    UnApp(UnOp, Operand),
}

impl Display for Rvalue {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Self::Use(op) => op.fmt(f),
            Self::BinApp(bin_op, op1, op2) => write!(f, "{} {} {}", op1, bin_op, op2),
            Self::UnApp(un_op, op) => write!(f, "{}{}", un_op, op),
        }
    }
}

#[derive(Debug)]
pub enum Statement {
    Assign(Local, Rvalue),
    Noop,
}

impl Display for Statement {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Self::Assign(local, rvalue) => write!(f, "{} = {}", local, rvalue),
            Self::Noop => "noop".fmt(f),
        }
    }
}

#[derive(Debug)]
pub struct Branch(pub Literal, pub BlockId);

impl Display for Branch {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{} -> {}", self.0, self.1)
    }
}

#[derive(Debug)]
pub enum Terminator {
    Return,
    Goto(BlockId),
    Switch(Operand, Vec<Branch>, BlockId),
    Call(Local, Operand, Vec<Operand>, BlockId),
}

impl Display for Terminator {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Self::Return => "return".fmt(f),
            Self::Goto(bb) => write!(f, "goto {}", bb),
            Self::Switch(discr, branches, otherwise) => {
                writeln!(f, "switch {} {{", discr)?;
                for branch in branches {
                    writeln!(f, "\t\t\t{},", branch)?;
                }
                writeln!(f, "\t\t\totherwise -> {}", otherwise)?;
                write!(f, "\t\t}}")
            }
            Self::Call(local, func, args, target) => {
                let mut args = args.iter();
                if let Some(arg) = args.next() {
                    write!(f, "{} = {}({}", local, func, arg)?;
                    for arg in args {
                        write!(f, ", {}", arg)?;
                    }
                    write!(f, ") -> {}", target)
                } else {
                    write!(f, "{} = {}() -> {}", local, func, target)
                }
            }
        }
    }
}

#[derive(Debug)]
pub struct BasicBlock(pub Vec<Statement>, pub Terminator);

impl Display for BasicBlock {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        for statement in &self.0 {
            if let Statement::Noop = statement {
            } else {
                writeln!(f, "\t\t{};", statement)?;
            }
        }
        write!(f, "\t\t{};", self.1)
    }
}

pub struct Func {
    pub args: Vec<(Local, BaseTy)>,
    pub ret_local: Local,
    pub ret_ty: BaseTy,
    pub locals: Vec<(Local, BaseTy)>,
    pub basic_blocks: BTreeMap<BlockId, BasicBlock>,
    pub initial_block: BlockId,
}

impl Display for Func {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let mut args = self.args.iter();

        write!(f, "fn(")?;

        if let Some((arg, arg_ty)) = args.next() {
            write!(f, "{}: {}", arg, arg_ty)?;
            for (arg, arg_ty) in args {
                write!(f, ", {}: {}", arg, arg_ty)?;
            }
        }

        writeln!(f, ") -> {} {{", self.ret_ty)?;

        for (local, local_ty) in &self.locals {
            writeln!(f, "\t{}: {};", local, local_ty)?;
        }

        writeln!(f, "")?;

        for (bb_id, bb) in &self.basic_blocks {
            writeln!(f, "\t{}: {{", bb_id)?;
            writeln!(f, "{}", bb)?;
            writeln!(f, "\t}}")?;
        }

        writeln!(f, "}}")
    }
}
