use std::fmt;

use liquid_rust_common::{
    index::{newtype_index, IndexVec},
    ordered_map::OrderedMap,
};
use liquid_rust_fixpoint::{Constraint, Fixpoint};
use liquid_rust_lrir::ty::{Refine, Ty, Var};

newtype_index! {
    struct NodeId {
        DEBUG_FORMAT = "node{}",
        const FIRST_NODE = 0
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
        let curr_node = nodes.push(Node {
            kind: NodeKind::Blank,
            children: vec![],
        });
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
        self.curr_bindings.truncate(bindings_count);
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

    pub fn push_guard(&mut self, refine: Refine) {
        self.push_node(Node {
            kind: NodeKind::Guard(refine),
            children: vec![],
        });
    }

    pub fn push_constraint(&mut self, ty: Ty, refine: Refine) {
        self.push_binding(Var::Nu, ty);
        self.push_guard(refine);
        self.pop_to(self.curr_depth() - 2);
    }

    fn push_node(&mut self, node: Node) {
        let curr_node_id = self.curr_node_id();
        let new_node_id = self.nodes.push(node);
        self.nodes[curr_node_id].children.push(new_node_id);
        self.curr_path.push(new_node_id);
    }

    fn curr_node_id(&self) -> NodeId {
        self.curr_path.last().copied().unwrap()
    }

    fn check_aux(&self, node_id: NodeId, fixpoint: &mut Fixpoint) -> Constraint {
        let node = &self.nodes[node_id];

        match &node.kind {
            NodeKind::Blank => {
                let mut conj = vec![];

                for &node_id in node.children.iter() {
                    conj.push(self.check_aux(node_id, fixpoint));
                }

                bar(conj)
            }
            NodeKind::Binding(var, ty) => match ty.kind() {
                liquid_rust_lrir::ty::TyKind::Refined(base_ty, refinement) => {
                    fixpoint.push_var(Var::Nu);
                    let refinement = fixpoint.embed(refinement);
                    fixpoint.pop_var();

                    let sort = fixpoint.embed(base_ty);

                    let mut conj = vec![];

                    fixpoint.push_var(var.clone());

                    for &node_id in node.children.iter() {
                        conj.push(self.check_aux(node_id, fixpoint));
                    }

                    fixpoint.pop_var();

                    Constraint::ForAll(sort, refinement, Box::new(bar(conj)))
                }

                liquid_rust_lrir::ty::TyKind::Tuple(_) => todo!(),
                liquid_rust_lrir::ty::TyKind::Ref(_, _, _) => todo!(),
                liquid_rust_lrir::ty::TyKind::Uninit(_size) => {
                    let mut conj = vec![];

                    for &node_id in node.children.iter() {
                        conj.push(self.check_aux(node_id, fixpoint));
                    }

                    bar(conj)
                }
            },
            NodeKind::Guard(refine) => {
                let mut conj = vec![Constraint::Pred(fixpoint.embed(refine))];

                for &node_id in node.children.iter() {
                    conj.push(self.check_aux(node_id, fixpoint));
                }

                bar(conj)
            }
        }
    }

    pub fn check(&self, fixpoint: &mut Fixpoint) {
        let constraint = self.check_aux(FIRST_NODE, fixpoint);
        fixpoint.check(constraint);
    }

    pub fn dot<W: std::io::Write>(&self, mut buf: W) -> std::io::Result<()> {
        writeln!(buf, "graph g {{")?;

        for (id, node) in self.nodes.iter_enumerated() {
            writeln!(buf, "  \"{:?}\"[", id)?;

            match &node.kind {
                NodeKind::Blank => writeln!(buf, "    label = \"blank\"")?,
                NodeKind::Binding(var, ty) => writeln!(buf, "    label = \"{}: {}\"", var, ty)?,
                NodeKind::Guard(refine) => writeln!(buf, "    label = \"{}\"", refine)?,
            }

            writeln!(buf, "  ];")?;

            for child in node.children.iter() {
                writeln!(buf, "  \"{:?}\" -> \"{:?}\"", id, child)?;
            }
        }

        writeln!(buf, "}}")?;

        Ok(())
    }
}

fn bar(mut conj: Vec<Constraint>) -> Constraint {
    match conj.len() {
        0 => Constraint::tru(),
        1 => conj.remove(0),
        _ => Constraint::Conj(conj),
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
    Guard(Refine),
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
