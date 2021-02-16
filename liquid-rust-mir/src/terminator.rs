use crate::{bblock::BBlockId, func::FuncId, local::Local, operand::Operand, Span};

use std::fmt;

pub struct Terminator {
    pub kind: TerminatorKind,
    pub span: Span,
}

pub enum TerminatorKind {
    Return,
    Goto(BBlockId),
    Assert(Operand, bool, BBlockId),
    Call(Local, FuncId, Box<[Operand]>, BBlockId),
    Switch(Local, Box<[(u128, BBlockId)]>, BBlockId),
}

impl fmt::Display for Terminator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            TerminatorKind::Return => "return".fmt(f),
            TerminatorKind::Goto(bb_id) => write!(f, "goto {}", bb_id),
            TerminatorKind::Assert(op, true, bb_id) => write!(f, "assert({}) -> {}", op, bb_id),
            TerminatorKind::Assert(op, false, bb_id) => write!(f, "assert(!{}) -> {}", op, bb_id),
            TerminatorKind::Call(lhs, func, args, bb_id) => {
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
            TerminatorKind::Switch(local, branches, default) => {
                write!(f, "switch {} {{", local)?;
                for (bits, bb_id) in branches.as_ref() {
                    write!(f, "{} -> {}, ", bits, bb_id)?;
                }
                write!(f, "_ -> {}}}", default)
            }
        }
    }
}
