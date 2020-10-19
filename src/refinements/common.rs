#[derive(Debug)]
pub enum BaseTy {
    Uint(IntSize),
    Int(IntSize),
    Bool,
}

#[derive(Debug)]
pub enum Literal {
    Bool(bool),
    Int(i128),
}

#[derive(Debug)]
pub enum IntSize {
    Size8,
    Size16,
    Size32,
    Size64,
    Size128,
    SizePtr,
}

#[derive(Debug)]
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

#[derive(Debug)]
pub enum UnOp {
    Not,
    Neg,
}

