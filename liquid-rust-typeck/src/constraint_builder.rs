use std::{
    fmt::{self, Write},
    marker::PhantomData,
    ptr::NonNull,
};

use crate::ty::{self, Expr, Pred, Sort, Var};
use fixpoint::{KVar, KVid};
use itertools::Itertools;
use liquid_rust_common::{format::PadAdapter, index::IndexGen};
use liquid_rust_fixpoint as fixpoint;

pub struct ConstraintBuilder {
    root: Node,
    kvars: Vec<KVar>,
    kvid_gen: IndexGen<KVid>,
}

pub struct Cursor<'a>(NonNull<Node>, &'a mut ConstraintBuilder);

enum Node {
    Conj(Vec<Node>),
    ForAll(Var, Sort, Pred, Vec<Node>),
    Guard(Expr, Vec<Node>),
    Head(Pred),
}

impl ConstraintBuilder {
    pub fn new() -> Self {
        ConstraintBuilder {
            root: Node::Conj(vec![]),
            kvars: vec![],
            kvid_gen: IndexGen::new(),
        }
    }

    pub fn as_cursor(&mut self) -> Cursor {
        unsafe { Cursor::new_unchecked(&mut self.root as *mut Node, self) }
    }

    pub fn finalize(self) -> fixpoint::Constraint {
        self.root.finalize().unwrap_or(fixpoint::Constraint::TRUE)
    }
}

impl Cursor<'_> {
    unsafe fn new_unchecked(node: *mut Node, builder: &mut ConstraintBuilder) -> Cursor {
        Cursor(NonNull::new_unchecked(node), builder)
    }

    pub fn snapshot(&mut self) -> Cursor {
        Cursor(self.0, &mut self.1)
    }

    pub fn push_forall(&mut self, var: Var, sort: Sort, pred: impl Into<Pred>) {
        self.push_node(Node::ForAll(var, sort, pred.into(), vec![]));
    }

    pub fn push_guard(&mut self, expr: Expr) {
        self.push_node(Node::Guard(expr, vec![]));
    }

    pub fn push_head(&mut self, pred: impl Into<Pred>) {
        self.push_node(Node::Head(pred.into()));
    }

    pub fn fresh_kvar(&mut self, nu: Var, sort: Sort) -> Pred {
        let kvid = self.1.kvid_gen.fresh();
        self.1.kvars.push(KVar(kvid, vec![sort]));
        Pred::kvar(kvid, vec![Expr::from(nu)])
    }

    fn push_node(&mut self, node: Node) {
        unsafe {
            let children = match self.0.as_mut() {
                Node::Conj(children)
                | Node::ForAll(_, _, _, children)
                | Node::Guard(_, children) => children,
                Node::Head(_) => unreachable!("trying to push into a head node."),
            };
            children.push(node);
            let node = children.last_mut().unwrap();
            if !node.is_head() {
                self.0 = NonNull::new_unchecked(node as *mut Node);
            }
        }
    }
}

impl Node {
    fn finalize(self) -> Option<fixpoint::Constraint> {
        match self {
            Node::Conj(children) => finalize_children(children),
            Node::ForAll(var, sort, pred, children) => Some(fixpoint::Constraint::ForAll(
                var,
                sort,
                finalize_pred(pred),
                Box::new(finalize_children(children)?),
            )),
            Node::Guard(expr, children) => Some(fixpoint::Constraint::Guard(
                finalize_expr(expr),
                Box::new(finalize_children(children)?),
            )),
            Node::Head(pred) => Some(fixpoint::Constraint::Pred(finalize_pred(pred))),
        }
    }

    /// Returns `true` if the node is [`Head`].
    ///
    /// [`Head`]: Node::Head
    fn is_head(&self) -> bool {
        matches!(self, Self::Head(..))
    }
}

fn finalize_children(children: Vec<Node>) -> Option<fixpoint::Constraint> {
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
        Pred::KVar(kvid, args) => {
            fixpoint::Pred::KVar(kvid, args.iter().cloned().map(finalize_expr).collect())
        }
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
        ty::ExprKind::UnaryOp(op, e) => {
            fixpoint::Expr::UnaryOp(*op, Box::new(finalize_expr(e.clone())))
        }
    }
}

impl fmt::Debug for ConstraintBuilder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Constraint {{")?;
        writeln!(f, "    kvars: {:?}", self.kvars)?;
        writeln!(f, "    root: {:?}", PadAdapter::wrap(&self.root))?;
        writeln!(f, "}}")
    }
}

impl fmt::Debug for Node {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
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
            Node::Guard(expr, children) => {
                write!(f, "Guard({:?}) {{", expr)?;
                debug_children(children, f)?;
                write!(f, "}}")
            }
            Node::Head(pred) => {
                write!(f, "{:?}", pred)
            }
        }
    }
}

fn debug_children(children: &[Node], f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let mut w = PadAdapter::wrap_fmt(f);
    for child in children {
        write!(w, "\n{:?}", child)?;
    }
    if children.is_empty() {
        write!(f, " ")
    } else {
        writeln!(f)
    }
}
