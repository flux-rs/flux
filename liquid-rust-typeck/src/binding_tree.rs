use std::fmt;

use liquid_rust_common::{
    index::{newtype_index, IndexVec},
    ordered_map::OrderedMap,
};
use liquid_rust_fixpoint::Constraint;
use liquid_rust_lrir::ty::{embed::EmbeddingCtxt, Refine, Ty, Var};

newtype_index! {
    struct NodeId {
        DEBUG_FORMAT = "node{}",
        const ROOT = 0
    }
}

pub struct BindingTree {
    nodes: IndexVec<NodeId, Node>,
    curr_path: Vec<NodeId>,
    curr_bindings: OrderedMap<Var, Ty>,
}

impl BindingTree {
    pub fn new() -> Self {
        let mut nodes = IndexVec::new();

        let curr_node = nodes.push(Node::Blank(vec![]));
        Self {
            nodes,
            curr_path: vec![curr_node],
            curr_bindings: OrderedMap::new(),
        }
    }

    pub fn curr_depth(&self) -> usize {
        self.curr_path.len()
    }

    pub fn pop_to(&mut self, depth: usize) {
        let bindings_count = self
            .curr_path
            .iter()
            .skip(depth)
            .filter(|node_id| self.nodes[**node_id].is_binding())
            .count();
        self.curr_bindings
            .truncate(self.curr_bindings.len() - bindings_count);
        self.curr_path.truncate(depth);
    }

    pub fn lookup<V: Into<Var>>(&self, var: V) -> &Ty {
        let var = var.into();
        &self.curr_bindings[&var]
    }

    pub fn push_binding<V: Into<Var>>(&mut self, var: V, ty: Ty) {
        let var = var.into();
        self.push_node(Node::Binding(var, ty.clone(), vec![]));
        self.curr_bindings.insert(var, ty);
    }

    pub fn push_guard(&mut self, refine: Refine) {
        self.push_node(Node::Guard(refine, vec![]));
    }

    pub fn push_pred(&mut self, refine: Refine) {
        self.push_node(Node::Leaf(refine));
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

    pub fn gen_constraint(&self) -> Constraint {
        let mut cx = EmbeddingCtxt::default();
        self.gen_constraint_rec(ROOT, &mut cx)
            .unwrap_or(Constraint::TRUE)
    }

    fn gen_constraint_rec(&self, node_id: NodeId, cx: &mut EmbeddingCtxt) -> Option<Constraint> {
        let node = &self.nodes[node_id];

        match node {
            Node::Leaf(refine) => Some(Constraint::Pred(refine.embed(cx))),
            Node::Blank(children) => {
                let conj = children
                    .iter()
                    .filter_map(|&node_id| self.gen_constraint_rec(node_id, cx))
                    .collect();

                Constraint::join(conj)
            }
            Node::Binding(var, ty, children) => match ty.kind() {
                liquid_rust_lrir::ty::TyKind::Refined(base_ty, refinement) => {
                    cx.push_var(Var::Nu);
                    let refinement = refinement.embed(cx);
                    cx.pop_var();

                    let sort = base_ty.embed();

                    cx.push_var(*var);

                    let conj = children
                        .iter()
                        .filter_map(|&node_id| self.gen_constraint_rec(node_id, cx))
                        .collect();

                    cx.pop_var();

                    Some(Constraint::ForAll(
                        sort,
                        refinement,
                        Box::new(Constraint::join(conj)?),
                    ))
                }

                liquid_rust_lrir::ty::TyKind::Tuple(_) => todo!(),
                liquid_rust_lrir::ty::TyKind::Ref(_, _, _) => todo!(),
                liquid_rust_lrir::ty::TyKind::Uninit(_size) => {
                    let conj = children
                        .iter()
                        .filter_map(|&node_id| self.gen_constraint_rec(node_id, cx))
                        .collect();

                    Constraint::join(conj)
                }
            },
            Node::Guard(refine, children) => {
                let conj = children
                    .iter()
                    .filter_map(|&node_id| self.gen_constraint_rec(node_id, cx))
                    .collect();

                Some(Constraint::Guard(
                    refine.embed(cx),
                    Box::new(Constraint::join(conj)?),
                ))
            }
        }
    }

    pub fn dot<W: std::io::Write>(&self, mut buf: W) -> std::io::Result<()> {
        writeln!(buf, "digraph g {{")?;

        for (id, node) in self.nodes.iter_enumerated() {
            writeln!(buf, "  \"{:?}\"[", id)?;

            match &node {
                Node::Blank(..) => writeln!(buf, "    label = \"blank\"")?,
                Node::Binding(var, ty, ..) => writeln!(buf, "    label = \"{}: {}\"", var, ty)?,
                Node::Guard(refine, ..) => writeln!(buf, "    label = \"{}\"", refine)?,
                Node::Leaf(refine) => writeln!(buf, "    label = \"{}\"", refine)?,
            }

            writeln!(buf, "  ];")?;

            for child in node.children() {
                writeln!(buf, "  \"{:?}\" -> \"{:?}\"", id, child)?;
            }
        }

        writeln!(buf, "}}")?;

        Ok(())
    }
}

impl Default for BindingTree {
    fn default() -> Self {
        Self::new()
    }
}

enum Node {
    Blank(Vec<NodeId>),
    Binding(Var, Ty, Vec<NodeId>),
    Guard(Refine, Vec<NodeId>),
    Leaf(Refine),
}

impl Node {
    fn children(&self) -> impl Iterator<Item = NodeId> + '_ {
        let iter = match self {
            Node::Blank(children) => children.iter(),
            Node::Binding(_, _, children) => children.iter(),
            Node::Guard(_, children) => children.iter(),
            Node::Leaf(_) => [].iter(),
        };
        iter.copied()
    }

    fn push_child(&mut self, child: NodeId) {
        let children = match self {
            Node::Blank(children) => children,
            Node::Binding(_, _, children) => children,
            Node::Guard(_, children) => children,
            Node::Leaf(_) => panic!("Trying to push a child into a leaf node."),
        };
        children.push(child);
    }
}

impl Node {
    /// Returns `true` if the node is [`Binding`].
    fn is_binding(&self) -> bool {
        matches!(self, Self::Binding(..))
    }
}

impl fmt::Display for BindingTree {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let env = self
            .curr_path
            .iter()
            .filter_map(|node_id| match &self.nodes[*node_id] {
                Node::Binding(v, ty, ..) => Some(format!("{}: {}", v, ty)),
                Node::Guard(pred, ..) => Some(format!("{}", pred)),
                _ => None,
            })
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "[{}]", env)
    }
}
