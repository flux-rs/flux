use std::fmt::{self, Write};

use crate::{
    ty::{self, ExprKind, Pred, Sort, Var},
    unification::UnificationCtxt,
};
use liquid_rust_common::{
    format::PadAdapter,
    index::{newtype_index, IndexVec},
};
use liquid_rust_fixpoint::{self as fixpoint, Constraint};

pub struct ConstraintBuilder {
    nodes: IndexVec<NodeId, Node>,
    curr_path: Vec<NodeId>,
}

enum Node {
    Conj(Vec<NodeId>),
    ForAll(Var, Sort, Pred, Vec<NodeId>),
    // Guard(ty::Expr, Vec<NodeId>),
    Head(Pred),
}

newtype_index! {
    struct NodeId {
        DEBUG_FORMAT = "n{}",
        const ROOT = 0
    }
}

impl ConstraintBuilder {
    pub fn new() -> ConstraintBuilder {
        let mut nodes = IndexVec::new();

        let curr_node = nodes.push(Node::Conj(vec![]));
        ConstraintBuilder {
            nodes,
            curr_path: vec![curr_node],
        }
    }

    pub fn finalize(self, unification_cx: &UnificationCtxt) -> Constraint {
        self.finalize_inner(ROOT, unification_cx)
            .unwrap_or(Constraint::TRUE)
    }

    pub fn push_forall(&mut self, x: Var, sort: Sort, refine: Pred) {
        self.push_node(Node::ForAll(x, sort, refine, vec![]));
    }

    // pub fn push_guard(&mut self, guard: ty::Expr) {
    //     self.push_node(Node::Guard(guard, vec![]));
    // }

    pub fn push_head(&mut self, refine: impl Into<Pred>) {
        self.push_node(Node::Head(refine.into()));
        self.curr_path.pop();
    }

    fn push_node(&mut self, node: Node) {
        let curr_node_id = self.curr_node_id();
        let new_node_id = self.nodes.push(node);
        self.nodes[curr_node_id].push_child(new_node_id);
        self.curr_path.push(new_node_id);
    }

    fn curr_node_id(&self) -> NodeId {
        self.curr_path.last().copied().unwrap()
    }

    fn finalize_inner(
        &self,
        node_id: NodeId,
        unification_cx: &UnificationCtxt,
    ) -> Option<Constraint> {
        let node = &self.nodes[node_id];
        match node {
            Node::Conj(children) => self.finalize_children(children, unification_cx),
            Node::ForAll(var, sort, pred, children) => {
                let children = self.finalize_children(children, unification_cx)?;
                Some(Constraint::ForAll(
                    *var,
                    *sort,
                    finalize_pred(pred, unification_cx),
                    Box::new(children),
                ))
            }
            // Node::Guard(pred, children) => {
            //     let children = self.finalize_children(children)?;
            //     Some(Constraint::Guard(
            //         fixpoint::Pred::Expr(finalize_expr(pred)),
            //         Box::new(children),
            //     ))
            // }
            Node::Head(pred) => Some(Constraint::Pred(finalize_pred(pred, unification_cx))),
        }
    }

    fn finalize_children(
        &self,
        children: &[NodeId],
        unification_cx: &UnificationCtxt,
    ) -> Option<Constraint> {
        let mut children: Vec<Constraint> = children
            .iter()
            .filter_map(|&node_id| self.finalize_inner(node_id, unification_cx))
            .collect();
        match children.len() {
            0 => None,
            1 => children.pop(),
            _ => Some(Constraint::Conj(children)),
        }
    }
}

impl Node {
    fn push_child(&mut self, child: NodeId) {
        let children = match self {
            Node::Conj(children) => children,
            Node::ForAll(_, _, _, children) => children,
            // Node::Guard(_, children) => children,
            Node::Head(_) => unreachable!("trying to push a child into a leaf node."),
        };
        children.push(child);
    }
}

impl fmt::Debug for ConstraintBuilder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", NodeDebug(ROOT, self))
    }
}

struct NodeDebug<'a>(NodeId, &'a ConstraintBuilder);

impl fmt::Debug for NodeDebug<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn debug_children(
            node: &NodeDebug,
            children: &[NodeId],
            f: &mut fmt::Formatter<'_>,
        ) -> fmt::Result {
            let mut w = PadAdapter::wrap_fmt(f);
            for child in children {
                write!(w, "\n{:?}", NodeDebug(*child, node.1))?;
            }
            if Some(&node.0) == node.1.curr_path.last() {
                write!(w, "\n☐")?;
            }
            Ok(())
        }
        match &self.1.nodes[self.0] {
            Node::Conj(children) => {
                write!(f, "Conj {{")?;
                debug_children(self, children, f)?;
                write!(f, "\n}}")
            }
            Node::ForAll(var, sort, refine, children) => {
                write!(f, "Forall({:?}: {{{:?} | {:?}}}) {{", var, sort, refine)?;
                debug_children(self, children, f)?;
                write!(f, "\n}}")
            }
            // Node::Guard(guard, children) => {
            //     write!(f, "Guard({:?}) {{", guard)?;
            //     debug_children(self, children, f)?;
            //     write!(f, "\n}}")
            // }
            Node::Head(pred) => write!(f, "({:?})", pred),
        }
    }
}

fn finalize_pred(refine: &Pred, unification_cx: &UnificationCtxt) -> fixpoint::Pred {
    match refine {
        Pred::Expr(expr) => fixpoint::Pred::Expr(finalize_expr(expr, unification_cx)),
    }
}

fn finalize_expr(expr: &ty::Expr, unification_cx: &UnificationCtxt) -> fixpoint::Expr {
    match expr.kind() {
        ExprKind::Var(x) => fixpoint::Expr::Var(*x),
        ExprKind::Constant(c) => fixpoint::Expr::Constant(*c),
        ExprKind::BinaryOp(op, e1, e2) => fixpoint::Expr::BinaryOp(
            *op,
            Box::new(finalize_expr(e1, unification_cx)),
            Box::new(finalize_expr(e2, unification_cx)),
        ),
        ExprKind::EVar(evar) => match unification_cx.lookup(*evar) {
            Some(expr) => finalize_expr(&expr, unification_cx),
            None => {
                unreachable!("trying to finalize constraint with uninstantiated evar.")
            }
        },
    }
}
