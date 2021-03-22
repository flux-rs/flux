use crate::Fixpoint;

pub trait Embed {
    type Output;

    fn embed(&self, fixpoint: &Fixpoint) -> Self::Output;
}

use crate::sort::Sort;

use liquid_rust_lrir::ty;

impl Embed for ty::BaseTy {
    type Output = Sort;

    fn embed(&self, _fixpoint: &Fixpoint) -> Self::Output {
        match self {
            Self::Bool => Sort::Bool,
            Self::Int => Sort::Int,
        }
    }
}

use crate::constant::Constant;

impl Embed for ty::Constant {
    type Output = Constant;

    fn embed(&self, fixpoint: &Fixpoint) -> Self::Output {
        match self.ty().embed(fixpoint) {
            Sort::Int => Constant::Int(self.bits()),
            Sort::Bool => Constant::Bool(self.bits() != 0),
        }
    }
}

use crate::pred::Pred;

impl Embed for ty::Pred {
    type Output = Pred;

    fn embed(&self, fixpoint: &Fixpoint) -> Self::Output {
        match self.kind() {
            ty::PredKind::Path(path) => {
                assert_eq!(0, path.projection.len());
                Pred::Variable(fixpoint.get_index(&path.var))
            }
            ty::PredKind::BinaryOp(bin_op, lop, rop) => Pred::BinaryOp(
                *bin_op,
                Box::new(lop.embed(fixpoint)),
                Box::new(rop.embed(fixpoint)),
            ),
            ty::PredKind::UnaryOp(un_op, op) => Pred::UnaryOp(*un_op, Box::new(op.embed(fixpoint))),
            ty::PredKind::Const(constant) => Pred::Constant(constant.embed(fixpoint)),
        }
    }
}

impl Embed for ty::Refine {
    type Output = Pred;

    fn embed(&self, fixpoint: &Fixpoint) -> Self::Output {
        match self {
            ty::Refine::Infer(kvar) => Pred::Kvar(
                kvar.id,
                kvar.vars
                    .iter()
                    .map(|var| fixpoint.get_index(var))
                    .collect(),
            ),
            ty::Refine::Pred(pred) => pred.embed(fixpoint),
        }
    }
}
