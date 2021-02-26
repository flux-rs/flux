use crate::mir::{Constant, Place};

pub enum Operand {
    Copy(Place),
    Move(Place),
    Constant(Constant),
}
