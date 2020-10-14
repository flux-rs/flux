#[derive(Debug)]
pub struct Variable(pub String);

#[derive(Debug)]
pub enum Expr {
    Var(Variable),
    Const(i128),
    Add(Box<Self>, Box<Self>),
    Sub(Box<Self>, Box<Self>),
    Mul(Box<Self>, Box<Self>),
    // App(Variable, Vec<Self>),
}

#[derive(Debug)]
pub enum Pred {
    Eq(Expr, Expr),
    Lt(Expr, Expr),
    And(Box<Self>, Box<Self>),
    Or(Box<Self>, Box<Self>),
    Not(Box<Self>),
}

#[derive(Debug)]
pub enum BaseTy {
    Uint(IntSize),
    Int(IntSize),
}

#[derive(Debug)]
pub enum IntSize {
    Size8,
    Size16,
    Size32,
    Size64,
    Size128,
    Unsized,
}

#[derive(Debug)]
pub enum RefinedTy {
    Base(BaseTy),
    RefBase(Variable, BaseTy, Pred),
    RefFunc(Vec<(Variable, Self)>, Box<Self>),
}
