use crate::mir::{BasicBlock, Operand, Place, Span};
use crate::ty::BaseTy;

pub struct Terminator {
    pub kind: TerminatorKind,
    pub span: Span,
}

pub enum TerminatorKind {
    Goto {
        target: BasicBlock,
    },
    SwitchInt {
        discr: Operand,
        switch_ty: BaseTy,
        targets: SwitchTargets,
    },
    Return,
    Call {
        func: Operand,
        args: Vec<Operand>,
        destination: (Place, BasicBlock),
    },
    Assert {
        cond: Operand,
        expected: bool,
        target: BasicBlock,
    },
}

pub struct SwitchTargets {
    values: Vec<u128>,
    targets: Vec<BasicBlock>,
}
