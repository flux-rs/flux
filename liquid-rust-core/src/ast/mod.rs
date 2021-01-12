pub mod pred;
pub mod visitor;

use std::fmt;

pub use self::pred::Pred;
use crate::names::{ContId, Field, Local, Location};

pub struct FnDef<I, S = usize> {
    pub ty: FnTy<S>,
    pub params: Vec<Local<S>>,
    pub body: FnBody<I, S>,
    pub ret: ContId<S>,
}

pub enum FnBody<I, S = usize> {
    LetCont(Vec<ContDef<I, S>>, Box<FnBody<I, S>>),
    Ite {
        discr: Place<S>,
        then: Box<FnBody<I, S>>,
        else_: Box<FnBody<I, S>>,
    },
    Call {
        func: Place<S>,
        args: Vec<Local<S>>,
        ret: ContId<S>,
    },
    Jump {
        target: ContId<S>,
        args: Vec<Local<S>>,
    },
    Seq(Statement<I, S>, Box<FnBody<I, S>>),
    Abort,
}

pub struct ContDef<I, S = usize> {
    pub name: ContId<S>,
    pub params: Vec<Local<S>>,
    pub body: Box<FnBody<I, S>>,
    pub ty: ContTy<S>,
}

pub struct ContTy<S = usize> {
    pub heap: Heap<S>,
    pub locals: Vec<(Local<S>, Location<S>)>,
    pub inputs: Vec<Location<S>>,
}

pub struct Statement<I, S = usize> {
    pub source_info: I,
    pub kind: StatementKind<S>,
}

pub enum StatementKind<S = usize> {
    Let(Local<S>, TypeLayout),
    Assign(Place<S>, Rvalue<S>),
    Drop(Place<S>),
    Nop,
}

pub enum TypeLayout {
    Tuple(Vec<TypeLayout>),
    Block(usize),
}
#[derive(Debug)]
pub enum Operand<S = usize> {
    Use(Place<S>),
    Constant(Constant),
}

#[derive(Debug)]
pub enum Constant {
    Bool(bool),
    Int(u128),
    Unit,
}

impl Constant {
    pub fn base_ty(&self) -> BaseTy {
        match self {
            Constant::Bool(_) => BaseTy::Bool,
            Constant::Int(_) => BaseTy::Int,
            Constant::Unit => BaseTy::Unit,
        }
    }
}

#[derive(Debug)]
pub enum Rvalue<S = usize> {
    Use(Operand<S>),
    Ref(BorrowKind, Place<S>),
    BinaryOp(BinOp, Operand<S>, Operand<S>),
    CheckedBinaryOp(BinOp, Operand<S>, Operand<S>),
    UnaryOp(UnOp, Operand<S>),
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum BinOp {
    Add,
    Sub,
    Lt,
    Le,
    Eq,
    Ge,
    Gt,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum UnOp {
    Not,
}
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum BaseTy {
    Unit,
    Bool,
    Int,
}

impl fmt::Display for BaseTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BaseTy::Unit => write!(f, "()"),
            BaseTy::Bool => write!(f, "bool"),
            BaseTy::Int => write!(f, "int"),
        }
    }
}

#[derive(Eq, PartialEq, Copy, Clone, Debug, Hash, PartialOrd)]
pub enum BorrowKind {
    Shared,
    Mut,
}

pub enum Ty<S = usize> {
    OwnRef(Location<S>),
    Ref(BorrowKind, Region<S>, Location<S>),
    Tuple(Vec<(Field<S>, Ty<S>)>),
    Uninit(usize),
    Refine(BaseTy, Refine<S>),
}

impl<S> Ty<S> {
    pub fn unit() -> Ty<S> {
        Ty::Refine(
            BaseTy::Unit,
            Refine::Pred(pred::Pred::Constant(pred::Constant::Bool(true))),
        )
    }
}

pub struct FnTy<S = usize> {
    pub in_heap: Heap<S>,
    pub inputs: Vec<Location<S>>,
    pub out_heap: Heap<S>,
    pub output: Location<S>,
}

pub enum Refine<S = usize> {
    Infer,
    Pred(Pred<S>),
}

pub struct Heap<S = usize>(Vec<(Location<S>, Ty<S>)>);

wrap_iterable! {
    for<S> Heap<S>: Vec<(Location<S>, Ty<S>)>
}

#[derive(Eq, PartialEq, Clone, Debug)]
pub enum Region<S = usize> {
    Concrete(Vec<Place<S>>),
    Infer,
}

impl<S> From<Vec<Place<S>>> for Region<S> {
    fn from(v: Vec<Place<S>>) -> Self {
        Region::Concrete(v)
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub enum Proj {
    Field(usize),
    Deref,
}

#[derive(Eq, PartialEq, Clone, Debug, Hash)]
pub struct Place<S = usize> {
    pub base: Local<S>,
    pub projs: Vec<Proj>,
}

impl fmt::Display for Place {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = format!("$x{}", self.base.0);
        let mut need_parens = false;
        for proj in &self.projs {
            match proj {
                Proj::Field(n) => {
                    if need_parens {
                        s = format!("({}).{}", s, n);
                        need_parens = false;
                    } else {
                        s = format!("{}.{}", s, n);
                    }
                }
                Proj::Deref => {
                    s = format!("*{}", s);
                    need_parens = true;
                }
            }
        }
        write!(f, "{}", s)
    }
}

impl<S> From<Local<S>> for Place<S> {
    fn from(base: Local<S>) -> Self {
        Place {
            base,
            projs: vec![],
        }
    }
}
