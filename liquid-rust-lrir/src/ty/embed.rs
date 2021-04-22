use super::{BaseTy, KVid, PredKind, PredS, Refine, Var};
use liquid_rust_fixpoint as fixpoint;

#[derive(Default)]
pub struct EmbeddingCtxt {
    scope: Vec<Var>,
}

impl EmbeddingCtxt {
    pub fn push_var(&mut self, var: Var) -> usize {
        let index = self.scope.len();
        self.scope.push(var);
        index
    }

    pub fn pop_var(&mut self) -> Var {
        self.scope.pop().unwrap()
    }

    fn get_index(&self, target: &Var) -> Option<usize> {
        for (index, var) in self.scope.iter().enumerate() {
            if var == target {
                return Some(index);
            }
        }
        None
    }
}

impl BaseTy {
    pub fn embed(&self) -> fixpoint::Sort {
        match self {
            Self::Bool => fixpoint::Sort::Bool,
            Self::Int => fixpoint::Sort::Int,
        }
    }
}

impl KVid {
    pub fn embed(&self) -> fixpoint::KVid {
        fixpoint::KVid::from_usize(self.as_usize())
    }
}

impl Refine {
    pub fn embed(&self, cx: &EmbeddingCtxt) -> fixpoint::Pred {
        match self {
            Refine::Infer(kvar) => fixpoint::Pred::KVar(
                kvar.id.embed(),
                kvar.vars
                    .iter()
                    .filter_map(|var| cx.get_index(var))
                    .collect(),
            ),
            Refine::Pred(pred) => fixpoint::Pred::Expr(pred.embed(cx)),
        }
    }
}

impl PredS {
    pub fn embed(&self, cx: &EmbeddingCtxt) -> fixpoint::Expr {
        match self.kind() {
            PredKind::Path(path) => {
                assert_eq!(0, path.projection.len());
                fixpoint::Expr::Variable(cx.get_index(&path.var).unwrap())
            }
            PredKind::BinaryOp(bin_op, op1, op2) => {
                fixpoint::Expr::BinaryOp(*bin_op, Box::new(op1.embed(cx)), Box::new(op2.embed(cx)))
            }
            PredKind::UnaryOp(un_op, op) => fixpoint::Expr::UnaryOp(*un_op, Box::new(op.embed(cx))),
            PredKind::Const(constant) => fixpoint::Expr::Constant(*constant),
        }
    }
}
