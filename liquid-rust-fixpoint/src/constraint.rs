use crate::{
    emit,
    emit::{Ctx, Emit},
};
use liquid_rust_lrir::{
    mir::{BinOp, UnOp},
    ty::KVid,
};

use std::{collections::HashMap, fmt};

pub enum Constraint {
    Pred(Pred),
    Conj(Vec<Self>),
    Guard(Pred, Box<Self>),
    ForAll(Sort, Pred, Box<Self>),
}

impl Constraint {
    pub const TRUE: Self = Self::Pred(Pred::Expr(Expr::Constant(Constant::Bool(true))));

    pub fn join(mut constraints: Vec<Self>) -> Option<Self> {
        match constraints.len() {
            0 => None,
            1 => Some(constraints.remove(0)),
            _ => Some(Constraint::Conj(constraints)),
        }
    }
}

impl Emit for Constraint {
    fn emit<W: fmt::Write>(&self, w: &mut W, ctx: &Ctx) -> fmt::Result {
        match self {
            Self::Pred(pred) => emit!(w, ctx, "({})", pred),
            Self::Conj(preds) => {
                emit!(w, ctx, "(and")?;
                for pred in preds {
                    emit!(w, ctx, " {}", pred)?;
                }
                emit!(w, ctx, ")")
            }
            Self::ForAll(sort, premise, conclusion) => {
                emit!(
                    w,
                    &(*ctx + 1),
                    "(forall ((v{} {}) {}) {})",
                    ctx,
                    sort,
                    premise,
                    conclusion
                )
            }
            Self::Guard(premise, conclusion) => {
                emit!(w, ctx, "(forall ((_ int) {}) {})", premise, conclusion)
            }
        }
    }
}

#[derive(Clone, Copy)]
pub enum Sort {
    Int,
    Bool,
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool => "bool".fmt(f),
            Self::Int => "int".fmt(f),
        }
    }
}

crate::impl_emit_by_display!(Sort);

pub enum Pred {
    And(Vec<Self>),
    KVar(KVid, Vec<usize>),
    Expr(Expr),
}

impl Emit for Pred {
    fn emit<W: fmt::Write>(&self, w: &mut W, ctx: &Ctx) -> fmt::Result {
        match self {
            Self::KVar(kvid, args) => {
                let vars = args
                    .iter()
                    .map(|v| format!("v{}", v))
                    .collect::<Vec<_>>()
                    .join(" ");

                write!(w, "({} {})", kvid, vars)
            }
            Self::And(preds) => {
                emit!(w, ctx, "(and")?;
                for pred in preds {
                    emit!(w, ctx, " {}", pred)?;
                }
                emit!(w, ctx, ")")
            }
            Self::Expr(expr) => emit!(w, ctx, "({})", expr),
        }
    }
}

pub enum Expr {
    Variable(usize),
    Constant(Constant),
    BinaryOp(BinOp, Box<Self>, Box<Self>),
    UnaryOp(UnOp, Box<Self>),
}

impl Emit for Expr {
    fn emit<W: fmt::Write>(&self, w: &mut W, ctx: &Ctx) -> fmt::Result {
        fn should_parenthesize(bin_op: BinOp, child: &Expr) -> bool {
            if let Expr::BinaryOp(child_op, ..) = child {
                child_op.precedence() < bin_op.precedence()
                    || (child_op.precedence() == bin_op.precedence()
                        && !BinOp::associative(bin_op.precedence()))
            } else {
                false
            }
        }
        match self {
            Self::Variable(index) => write!(w, "v{}", index),
            Self::Constant(constant) => write!(w, "{}", constant),
            Self::BinaryOp(bin_op, op1, op2) => {
                if should_parenthesize(*bin_op, op1) {
                    emit!(w, ctx, "({})", op1)?;
                } else {
                    emit!(w, ctx, "{}", op1)?;
                }
                emit!(w, ctx, " {} ", bin_op)?;
                if should_parenthesize(*bin_op, op2) {
                    emit!(w, ctx, "({})", op2)?;
                } else {
                    emit!(w, ctx, "{}", op2)?;
                }
                Ok(())
            }
            Self::UnaryOp(un_op, op) => {
                if matches!(op.as_ref(), Expr::Variable(..) | Expr::Constant(..)) {
                    emit!(w, ctx, "{}{}", un_op, op)
                } else {
                    emit!(w, ctx, "{}({})", un_op, op)
                }
            }
        }
    }
}

impl Emit for UnOp {
    fn emit<W: fmt::Write>(&self, w: &mut W, _ctx: &Ctx) -> fmt::Result {
        match self {
            UnOp::Not => write!(w, "~"),
            UnOp::Neg => write!(w, "-"),
        }
    }
}

impl Emit for BinOp {
    fn emit<W: fmt::Write>(&self, w: &mut W, _ctx: &Ctx) -> fmt::Result {
        match self {
            BinOp::Eq(_) => write!(w, "="),
            _ => write!(w, "{}", self),
        }
    }
}

pub enum Constant {
    Bool(bool),
    Int(u128),
}

impl fmt::Display for Constant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool(bool) => bool.fmt(f),
            Self::Int(int) => int.fmt(f),
        }
    }
}

pub struct Qualifier {
    pub name: String,
    pub vars: Vec<Sort>,
    pub pred: Expr,
}

impl Emit for Qualifier {
    fn emit<W: fmt::Write>(&self, w: &mut W, ctx: &Ctx) -> fmt::Result {
        write!(w, "(qualif {} (", self.name)?;
        let vars = self
            .vars
            .iter()
            .enumerate()
            .map(|(v, sort)| format!("(v{} {})", v, sort))
            .collect::<Vec<_>>()
            .join(" ");
        write!(w, "{})", vars)?;
        emit!(w, ctx, "({}))", &self.pred)
    }
}

pub struct KVar {
    id: KVid,
    sorts: Vec<Sort>,
}

impl Emit for KVar {
    fn emit<W: fmt::Write>(&self, w: &mut W, _ctx: &Ctx) -> fmt::Result {
        write!(w, "(var {} (", self.id)?;
        let sorts = self
            .sorts
            .iter()
            .map(|v| format!("({})", v))
            .collect::<Vec<_>>()
            .join(" ");
        write!(w, "{}))", sorts)
    }
}

pub(crate) struct KVarGatherCtx {
    scope: Vec<Sort>,
    kvars: HashMap<KVid, Vec<Sort>>,
}

impl KVarGatherCtx {
    pub(crate) fn gather_kvars(constraint: &Constraint) -> Vec<KVar> {
        let mut cx = KVarGatherCtx {
            scope: vec![],
            kvars: HashMap::new(),
        };
        constraint.gather_kvars(&mut cx);
        cx.kvars
            .into_iter()
            .map(|(id, sorts)| KVar { id, sorts })
            .collect()
    }
}

impl Constraint {
    fn gather_kvars(&self, cx: &mut KVarGatherCtx) {
        match self {
            Constraint::Pred(pred) => pred.gather_kvars(cx),
            Constraint::Conj(constraints) => {
                for c in constraints {
                    c.gather_kvars(cx);
                }
            }
            Constraint::Guard(premise, conclusion) => {
                premise.gather_kvars(cx);
                conclusion.gather_kvars(cx);
            }
            Constraint::ForAll(sort, premise, conclusion) => {
                cx.scope.push(*sort);
                premise.gather_kvars(cx);
                conclusion.gather_kvars(cx);
                cx.scope.pop();
            }
        }
    }
}

impl Pred {
    fn gather_kvars(&self, cx: &mut KVarGatherCtx) {
        match self {
            Pred::And(preds) => {
                for pred in preds {
                    pred.gather_kvars(cx);
                }
            }
            Pred::KVar(kvid, vars) => {
                if cx.kvars.contains_key(kvid) {
                    return;
                }
                let sorts = vars.iter().map(|&var| cx.scope[var]).collect();
                cx.kvars.insert(*kvid, sorts);
            }
            Pred::Expr(_) => {}
        }
    }
}
