use std::{collections::HashMap, fmt};

use liquid_rust_common::{index::IndexMap, new_index, ordered_hash_map::OrderedHashMap};
use liquid_rust_lrir::ty::{Pred, Refine, Ty, Var};

new_index! {
    NodeId
}

pub struct BindingTree {
    nodes: IndexMap<NodeId, Node>,
    constraints: HashMap<NodeId, Vec<(Refine, Refine)>>,
    curr_path: Vec<NodeId>,
    curr_bindings: OrderedHashMap<Var, Ty>,
}

impl BindingTree {
    pub fn new() -> Self {
        let mut nodes = IndexMap::new();
        let curr_node = nodes.insert(Node {
            kind: NodeKind::Blank,
            children: vec![],
        });
        Self {
            nodes,
            constraints: HashMap::new(),
            curr_path: vec![curr_node],
            curr_bindings: OrderedHashMap::new(),
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
        self.push_node(Node {
            kind: NodeKind::Binding(var, ty.clone()),
            children: vec![],
        });
        self.curr_bindings.insert(var, ty);
    }

    pub fn push_guard(&mut self, pred: Pred) {
        self.push_node(Node {
            kind: NodeKind::Guard(pred),
            children: vec![],
        });
    }

    pub fn push_constraint(&mut self, refine1: Refine, refine2: Refine) {
        self.constraints
            .entry(self.curr_node_id())
            .or_default()
            .push((refine1, refine2));
    }

    fn push_node(&mut self, node: Node) {
        let curr_node_id = self.curr_node_id();
        let new_node_id = self.nodes.insert(node);
        self.nodes[curr_node_id].children.push(new_node_id);
        self.curr_path.push(new_node_id);
    }

    fn curr_node_id(&self) -> NodeId {
        self.curr_path.last().copied().unwrap()
    }
}

struct Node {
    kind: NodeKind,
    children: Vec<NodeId>,
}

impl Node {
    /// Returns `true` if the node is a [`Binding`].
    fn is_binding(&self) -> bool {
        matches!(self.kind, NodeKind::Binding(..))
    }
}

enum NodeKind {
    Blank,
    Binding(Var, Ty),
    Guard(Pred),
}

impl fmt::Display for BindingTree {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let env = self
            .curr_path
            .iter()
            .filter_map(|node_id| match &self.nodes[*node_id].kind {
                NodeKind::Blank => None,
                NodeKind::Binding(v, ty) => Some(format!("{}: {}", v, ty)),
                NodeKind::Guard(pred) => Some(format!("{}", pred)),
            })
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "[{}]", env)
    }
}
