use std::fmt::{self, Write};

use crate::ty::{self, Pred, Sort, Var};
use itertools::Itertools;
use liquid_rust_common::format::PadAdapter;
use liquid_rust_fixpoint as fixpoint;

pub struct ConstraintBuilder {
    root: Cursor,
}

pub struct Cursor(Node);

enum Node {
    Conj(Vec<Cursor>),
    ForAll(Var, Sort, Pred, Vec<Cursor>),
    Head(Pred),
}

impl ConstraintBuilder {
    pub fn new() -> Self {
        ConstraintBuilder {
            root: Cursor(Node::Conj(vec![])),
        }
    }

    pub fn as_cursor(&mut self) -> &mut Cursor {
        &mut self.root
    }

    pub fn finalize(self) -> fixpoint::Constraint {
        self.root.finalize().unwrap_or(fixpoint::Constraint::TRUE)
    }
}

impl Cursor {
    #[must_use]
    pub fn push_forall(&mut self, var: Var, sort: Sort, pred: impl Into<Pred>) -> &mut Cursor {
        self.push_child(Node::ForAll(var, sort, pred.into(), Vec::new()))
    }

    pub fn push_head(&mut self, pred: impl Into<Pred>) {
        let _ = self.push_child(Node::Head(pred.into()));
    }

    #[must_use]
    fn push_child(&mut self, node: Node) -> &mut Cursor {
        let children = match &mut self.0 {
            Node::Conj(children) => children,
            Node::ForAll(_, _, _, children) => children,
            Node::Head(_) => unreachable!("trying to push a child into a head node."),
        };
        children.push(Cursor(node));
        children.last_mut().unwrap()
    }

    fn finalize(self) -> Option<fixpoint::Constraint> {
        match self.0 {
            Node::Conj(children) => finalize_children(children),
            Node::ForAll(var, sort, pred, children) => {
                let children = finalize_children(children)?;
                Some(fixpoint::Constraint::ForAll(
                    var,
                    sort,
                    finalize_pred(pred),
                    Box::new(children),
                ))
            }
            Node::Head(pred) => Some(fixpoint::Constraint::Pred(finalize_pred(pred))),
        }
    }
}

fn finalize_children(children: Vec<Cursor>) -> Option<fixpoint::Constraint> {
    let mut children = children
        .into_iter()
        .filter_map(|node| node.finalize())
        .collect_vec();
    match children.len() {
        0 => None,
        1 => children.pop(),
        _ => Some(fixpoint::Constraint::Conj(children)),
    }
}

fn finalize_pred(refine: Pred) -> fixpoint::Pred {
    match refine {
        Pred::Expr(expr) => fixpoint::Pred::Expr(finalize_expr(expr)),
    }
}

fn finalize_expr(expr: ty::Expr) -> fixpoint::Expr {
    match expr.kind() {
        ty::ExprKind::Var(x) => fixpoint::Expr::Var(*x),
        ty::ExprKind::Constant(c) => fixpoint::Expr::Constant(*c),
        ty::ExprKind::BinaryOp(op, e1, e2) => fixpoint::Expr::BinaryOp(
            *op,
            Box::new(finalize_expr(e1.clone())),
            Box::new(finalize_expr(e2.clone())),
        ),
    }
}

impl fmt::Debug for ConstraintBuilder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.root)
    }
}

impl fmt::Debug for Cursor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            Node::Conj(children) => {
                write!(f, "Conj {{")?;
                debug_children(children, f)?;
                write!(f, "}}")
            }
            Node::ForAll(var, sort, pred, children) => {
                write!(f, "Forall({:?}: {{{:?} | {:?}}}) {{", var, sort, pred)?;
                debug_children(children, f)?;
                write!(f, "}}")
            }
            Node::Head(pred) => {
                write!(f, "({:?})", pred)
            }
        }
    }
}

fn debug_children(children: &[Cursor], f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let mut w = PadAdapter::wrap_fmt(f);
    for child in children {
        write!(w, "\n{:?}", child)?;
    }
    if children.len() > 0 {
        write!(f, "\n")
    } else {
        write!(f, " ")
    }
}
