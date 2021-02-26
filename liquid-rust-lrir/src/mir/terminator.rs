use crate::mir::{BasicBlock, Operand, Place, SourceInfo};
use crate::ty::BaseTy;

pub struct Terminator {
    pub source_info: SourceInfo,
    pub kind: TerminatorKind,
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
