use crate::{bblock::BBlockId, func::FuncId, local::Local, operand::Operand};

use std::fmt;

pub enum Terminator {
    Return,
    Goto(BBlockId),
    Assert(Operand, bool, BBlockId),
    Call(Local, FuncId, Box<[Operand]>, BBlockId),
    Switch(Operand, Box<[(u128, BBlockId)]>, BBlockId),
}

impl fmt::Display for Terminator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Return => "return".fmt(f),
            Self::Goto(bb_id) => write!(f, "goto {}", bb_id),
            Self::Assert(op, true, bb_id) => write!(f, "assert({}) -> {}", op, bb_id),
            Self::Assert(op, false, bb_id) => write!(f, "assert(!{}) -> {}", op, bb_id),
            Self::Call(lhs, func, args, bb_id) => {
                write!(f, "{} = {}(", lhs, func)?;
                let mut args = args.into_iter();
                if let Some(arg) = args.next() {
                    write!(f, "{}", arg)?;
                    for arg in args {
                        write!(f, ", {}", arg)?;
                    }
                }
                write!(f, ") -> {}", bb_id)
            }
            Self::Switch(op, branches, default) => {
                write!(f, "switch {} {{", op)?;
                for (bits, bb_id) in branches.as_ref() {
                    write!(f, "{} -> {}, ", bits, bb_id)?;
                }
                write!(f, "_ -> {}}}", default)
            }
        }
    }
}
