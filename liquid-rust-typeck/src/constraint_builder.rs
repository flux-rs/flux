use std::{
    fmt::{self, Write},
    marker::PhantomData,
    ptr::NonNull,
};

use crate::ty::{self, Expr, ExprKind, Pred, Sort, Var};
use fixpoint::{BinOp, KVar, KVid};
use itertools::Itertools;
use liquid_rust_common::{
    format::PadAdapter,
    index::{IndexGen, IndexVec},
};
use liquid_rust_fixpoint as fixpoint;

pub struct ConstraintBuilder {
    root: Node,
    kvars: IndexVec<KVid, Vec<Sort>>,
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
            kvars: IndexVec::new(),
        }
    }

    pub fn as_cursor(&mut self) -> Cursor {
        unsafe { Cursor::new_unchecked(&mut self.root as *mut Node, self) }
    }

    pub fn to_fixpoint(self, name_gen: &IndexGen<Var>) -> fixpoint::Fixpoint {
        let constraint = self
            .root
            .to_fixpoint(name_gen, &self.kvars)
            .unwrap_or(fixpoint::Constraint::TRUE);
        let kvars = self
            .kvars
            .into_iter_enumerated()
            .map(|(kvid, sorts)| KVar(kvid, sorts))
            .collect();
        fixpoint::Fixpoint::new(kvars, constraint)
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
        let kvid = self.1.kvars.push(vec![sort]);
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
    fn to_fixpoint(
        self,
        name_gen: &IndexGen<Var>,
        kvars: &IndexVec<KVid, Vec<Sort>>,
    ) -> Option<fixpoint::Constraint> {
        match self {
            Node::Conj(children) => finalize_children(name_gen, kvars, children),
            Node::ForAll(var, sort, pred, children) => {
                let (bindings, pred) = finalize_pred(name_gen, kvars, pred);
                Some(stitch(
                    bindings,
                    fixpoint::Constraint::ForAll(
                        var,
                        sort,
                        pred,
                        Box::new(finalize_children(name_gen, kvars, children)?),
                    ),
                ))
            }
            Node::Guard(expr, children) => Some(fixpoint::Constraint::Guard(
                finalize_expr(expr),
                Box::new(finalize_children(name_gen, kvars, children)?),
            )),
            Node::Head(pred) => {
                let (bindings, pred) = finalize_pred(name_gen, kvars, pred);
                Some(stitch(bindings, fixpoint::Constraint::Pred(pred)))
            }
        }
    }

    /// Returns `true` if the node is [`Head`].
    ///
    /// [`Head`]: Node::Head
    fn is_head(&self) -> bool {
        matches!(self, Self::Head(..))
    }
}

fn finalize_children(
    name_gen: &IndexGen<Var>,
    kvars: &IndexVec<KVid, Vec<Sort>>,
    children: Vec<Node>,
) -> Option<fixpoint::Constraint> {
    let mut children = children
        .into_iter()
        .filter_map(|node| node.to_fixpoint(name_gen, kvars))
        .collect_vec();
    match children.len() {
        0 => None,
        1 => children.pop(),
        _ => Some(fixpoint::Constraint::Conj(children)),
    }
}

fn finalize_pred(
    name_gen: &IndexGen<Var>,
    kvars: &IndexVec<KVid, Vec<Sort>>,
    refine: Pred,
) -> (Vec<(Var, Sort, fixpoint::Expr)>, fixpoint::Pred) {
    let mut bindings = vec![];
    let pred = match refine {
        Pred::Expr(expr) => fixpoint::Pred::Expr(finalize_expr(expr)),
        Pred::KVar(kvid, args) => {
            let args = args.iter().zip(&kvars[kvid]).map(|(arg, sort)| {
                if let ExprKind::Var(var) = arg.kind() {
                    *var
                } else {
                    let fresh = name_gen.fresh();
                    let pred = fixpoint::Expr::BinaryOp(
                        BinOp::Eq,
                        Box::new(fixpoint::Expr::Var(fresh)),
                        Box::new(finalize_expr(arg.clone())),
                    );
                    bindings.push((fresh, *sort, pred));
                    fresh
                }
            });
            fixpoint::Pred::KVar(kvid, args.collect())
        }
    };
    (bindings, pred)
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
        writeln!(
            f,
            "    kvars: [{}]",
            self.kvars
                .iter_enumerated()
                .map(|(kvid, sorts)| { format!("KVar({:?}, {:?})", kvid, sorts) })
                .format(",")
        )?;

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

fn stitch(
    bindings: Vec<(Var, Sort, fixpoint::Expr)>,
    c: fixpoint::Constraint,
) -> fixpoint::Constraint {
    bindings.into_iter().rev().fold(c, |c, (var, sort, e)| {
        fixpoint::Constraint::ForAll(var, sort, fixpoint::Pred::Expr(e), Box::new(c))
    })
}
