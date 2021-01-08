use hashconsing::HConsed;

pub use crate::ast::pred::{BinOp, Constant, Place, UnOp, Var};

pub type Pred = HConsed<PredS>;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum PredS {
    Constant(Constant),
    Place(Place),
    BinaryOp(BinOp, Pred, Pred),
    UnaryOp(UnOp, Pred),
}

impl std::fmt::Display for PredS {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PredS::Constant(c) => write!(f, "{}", c)?,
            PredS::Place(place) => write!(f, "{}", place)?,
            PredS::BinaryOp(op, lhs, rhs) => {
                write!(f, "({} {} {})", lhs, op, rhs)?;
            }
            PredS::UnaryOp(op, operand) => {
                write!(f, "{}({})", op, operand)?;
            }
        }
        Ok(())
    }
}
