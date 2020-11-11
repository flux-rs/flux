mod predicate;

pub use predicate::Predicate;

use crate::generator::Generator;

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct Variable(usize);

impl Variable {
    pub fn generator() -> Generator<Self> {
        Generator::new(Self)
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum BaseTy {
    Unit,
    Bool,
    Uint(IntSize),
    Int(IntSize),
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum IntSize {
    Size8,
    Size16,
    Size32,
    Size64,
    Size128,
    SizePtr,
}

#[derive(Debug, Clone)]
pub enum Ty {
    RefBase(Variable, BaseTy, Predicate),
    RefFunc(Vec<(Variable, Self)>, Box<Self>),
}
