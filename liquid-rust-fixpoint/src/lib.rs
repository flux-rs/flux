use liquid_rust_lrir::ty::{UnOp, BinOp};

pub enum Constraint {
    Pred(Pred),
    Conj(Vec<Self>),
    ForAll(Sort, Pred, Box<Self>),
    Guard(Pred, Box<Self>),
}

pub enum Sort {
    Int,
    Bool,
}

pub enum Pred {
    Const(Constant),
    Var(Variable),
    BinaryOp(BinOp, Box<Self>, Box<Self>),
    UnaryOp(UnOp, Box<Self>),
}

pub enum Constant {
    Bool(bool),
    Int(u128),
    Unit,
}

pub struct Variable {
    index: usize,
}

pub struct Fixpoint {

}
