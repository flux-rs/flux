pub mod pred;
pub mod visitor;

use std::fmt;

pub use self::pred::Pred;
use crate::names::{ContId, Field, Local, Location};

#[derive(Debug)]
pub struct FnDef<I, S = usize> {
    pub ty: FnTy<S>,
    pub params: Vec<Local<S>>,
    pub body: FnBody<I, S>,
    pub ret: ContId<S>,
}

#[derive(Debug)]
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

#[derive(Debug)]
pub struct ContDef<I, S = usize> {
    pub name: ContId<S>,
    pub params: Vec<Local<S>>,
    pub body: Box<FnBody<I, S>>,
    pub ty: ContTy<S>,
}

#[derive(Debug)]
pub struct ContTy<S = usize> {
    pub heap: Heap<S>,
    pub locals: LocalsMap<S>,
    pub inputs: Vec<Location<S>>,
}

#[derive(Debug)]
pub struct Statement<I, S = usize> {
    pub source_info: I,
    pub kind: StatementKind<S>,
}

#[derive(Debug)]
pub enum StatementKind<S = usize> {
    Let(Local<S>, TypeLayout),
    Assign(Place<S>, Rvalue<S>),
    Drop(Local<S>),
}

#[derive(Debug)]
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
pub enum BaseType {
    Unit,
    Bool,
    Int,
}

impl fmt::Display for BaseType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BaseType::Unit => write!(f, "()"),
            BaseType::Bool => write!(f, "bool"),
            BaseType::Int => write!(f, "int"),
        }
    }
}

#[derive(Eq, PartialEq, Copy, Clone, Debug, Hash, PartialOrd)]
pub enum BorrowKind {
    Shared,
    Mut,
}

#[derive(Debug)]
pub enum Ty<S = usize> {
    Fn(FnTy<S>),
    OwnRef(Location<S>),
    Ref(BorrowKind, Region<S>, Location<S>),
    Tuple(Vec<(Field<S>, Ty<S>)>),
    Uninit(usize),
    Refine { bty: BaseType, refine: Refine<S> },
}

#[derive(Debug)]
pub struct FnTy<S = usize> {
    pub in_heap: Heap<S>,
    pub inputs: Vec<Location<S>>,
    pub out_heap: Heap<S>,
    pub output: Location<S>,
}

#[derive(Debug)]
pub enum Refine<S = usize> {
    Infer,
    Pred(Pred<S>),
}

#[derive(Debug)]
pub struct Heap<S = usize>(Vec<(Location<S>, Ty<S>)>);

impl<S> From<Vec<(Location<S>, Ty<S>)>> for Heap<S> {
    fn from(vec: Vec<(Location<S>, Ty<S>)>) -> Self {
        Heap(vec)
    }
}

impl<S> IntoIterator for Heap<S> {
    type Item = (Location<S>, Ty<S>);

    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, S> IntoIterator for &'a Heap<S> {
    type Item = &'a (Location<S>, Ty<S>);

    type IntoIter = std::slice::Iter<'a, (Location<S>, Ty<S>)>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

#[derive(Debug, Clone)]
pub struct LocalsMap<S = usize>(Vec<(Local<S>, Location<S>)>);

impl<S> LocalsMap<S> {
    pub fn empty() -> Self {
        LocalsMap(Vec::new())
    }

    pub fn locals(&self) -> impl Iterator<Item = &Local<S>> {
        self.iter().map(|(x, _)| x)
    }

    pub fn iter(&self) -> std::slice::Iter<(Local<S>, Location<S>)> {
        self.0.iter()
    }
}

impl<S> From<Vec<(Local<S>, Location<S>)>> for LocalsMap<S> {
    fn from(vec: Vec<(Local<S>, Location<S>)>) -> Self {
        LocalsMap(vec)
    }
}

impl<'a, S> IntoIterator for &'a LocalsMap<S> {
    type Item = &'a (Local<S>, Location<S>);

    type IntoIter = std::slice::Iter<'a, (Local<S>, Location<S>)>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<S> IntoIterator for LocalsMap<S> {
    type Item = (Local<S>, Location<S>);

    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
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
