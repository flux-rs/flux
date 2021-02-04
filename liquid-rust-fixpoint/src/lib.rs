pub mod solver;

use std::{collections::HashMap, fmt, io};

use liquid_rust_core::ty::{pred::Constant, BinOp, UnOp};
use quickscope::ScopeMap;
pub use solver::solve;
use solver::LiquidResult;

#[derive(Debug)]
pub enum Constraint {
    True,
    Pred(Pred),
    Conj(Vec<Constraint>),
    Forall(String, Sort, Pred, Box<Constraint>),
    Guard(Pred, Box<Constraint>),
}

impl Constraint {
    pub fn solve(&self) -> io::Result<LiquidResult> {
        solve(self)
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Sort {
    Int,
    Bool,
    Unit,
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sort::Int => write!(f, "int"),
            Sort::Bool => write!(f, "bool"),
            Sort::Unit => write!(f, "Unit"),
        }
    }
}

#[derive(Debug)]
pub enum Pred {
    Kvar(Kvar),
    Conj(Vec<Pred>),
    Expr(Expr),
    True,
}

#[derive(Debug)]
pub enum Expr {
    Var(String),
    Constant(Constant),
    BinaryOp(BinOp, Box<Expr>, Box<Expr>),
    UnaryOp(UnOp, Box<Expr>),
}

#[derive(Debug)]
pub struct Kvar(pub usize, pub Vec<String>);

struct KvarInferer {
    sorts: ScopeMap<String, Sort>,
    kvars: HashMap<usize, Vec<Sort>>,
}

impl KvarInferer {
    fn new() -> Self {
        Self {
            sorts: ScopeMap::new(),
            kvars: HashMap::new(),
        }
    }

    fn infer(mut self, c: &Constraint) -> HashMap<usize, Vec<Sort>> {
        self.infer_constraint(c);
        self.kvars
    }

    fn infer_constraint(&mut self, c: &Constraint) {
        match c {
            Constraint::True => {}
            Constraint::Pred(pred) => self.infer_pred(pred),
            Constraint::Conj(constraints) => {
                for c in constraints {
                    self.infer_constraint(c);
                }
            }
            Constraint::Forall(var, sort, pred, body) => {
                self.sorts.push_layer();
                self.sorts.define(var.clone(), *sort);
                self.infer_pred(pred);
                self.infer_constraint(body);
                self.sorts.pop_layer();
            }
            Constraint::Guard(guard, body) => {
                self.infer_pred(guard);
                self.infer_constraint(body);
            }
        }
    }

    fn infer_pred(&mut self, pred: &Pred) {
        match pred {
            Pred::Kvar(kvar) => {
                self.infer_kvar(kvar);
            }
            Pred::Conj(preds) => {
                for pred in preds {
                    self.infer_pred(pred);
                }
            }
            Pred::Expr(..) | Pred::True => {}
        }
    }

    fn infer_kvar(&mut self, kvar: &Kvar) {
        if self.kvars.contains_key(&kvar.0) {
            return;
        }
        let sorts = kvar
            .1
            .iter()
            .map(|var| {
                *self
                    .sorts
                    .get(var)
                    .unwrap_or_else(|| panic!("{} {:?}", var, kvar))
            })
            .collect();
        self.kvars.insert(kvar.0, sorts);
    }
}
