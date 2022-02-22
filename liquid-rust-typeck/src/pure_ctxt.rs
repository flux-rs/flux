use std::{
    cell::RefCell,
    rc::{Rc, Weak},
};

use itertools::{repeat_n, Itertools};
use liquid_rust_common::index::{Idx, IndexGen, IndexVec};
use liquid_rust_fixpoint as fixpoint;

use crate::{
    constraint_gen::Tag,
    ty::{BinOp, Expr, ExprKind, ExprS, KVid, Loc, Name, Pred, Sort, SortKind, Var},
    FixpointCtxt, TagIdx,
};

pub struct ConstraintBuilder {
    root: NodePtr,
}

pub struct PureCtxt<'a> {
    cx: &'a mut ConstraintBuilder,
    ptr: NodePtr,
}

pub struct Snapshot {
    node: WeakNodePtr,
}

#[derive(Default)]
pub struct KVarStore {
    kvars: IndexVec<KVid, Vec<fixpoint::Sort>>,
}

pub struct Scope {
    bindings: IndexVec<Name, Sort>,
}

struct Node {
    kind: NodeKind,
    /// Number of binding nodes between the root and this node's parent
    nbindings: usize,
    parent: Option<WeakNodePtr>,
    children: Vec<NodePtr>,
}

type NodePtr = Rc<RefCell<Node>>;
type WeakNodePtr = Weak<RefCell<Node>>;

enum NodeKind {
    Conj,
    Binding(Name, Sort, Pred),
    Pred(Expr),
    Head(Pred, Tag),
}

impl ConstraintBuilder {
    pub fn new() -> ConstraintBuilder {
        let root = Node { kind: NodeKind::Conj, nbindings: 0, parent: None, children: vec![] };
        let root = Rc::new(RefCell::new(root));
        ConstraintBuilder { root }
    }

    pub fn pure_context_at_root(&mut self) -> PureCtxt {
        PureCtxt { ptr: Rc::clone(&self.root), cx: self }
    }

    pub fn pure_context_at(&mut self, snapshot: &Snapshot) -> Option<PureCtxt> {
        Some(PureCtxt { ptr: snapshot.node.upgrade()?, cx: self })
    }

    pub fn into_fixpoint(self, cx: &mut FixpointCtxt) -> fixpoint::Constraint<TagIdx> {
        self.root
            .borrow()
            .to_fixpoint(cx)
            .unwrap_or(fixpoint::Constraint::TRUE)
    }
}

impl KVarStore {
    pub fn new() -> Self {
        Self { kvars: IndexVec::new() }
    }

    pub fn fresh<S>(&mut self, var: Var, sort: Sort, scope: S) -> Pred
    where
        S: IntoIterator<Item = (Name, Sort)>,
    {
        let scope = scope.into_iter();

        let mut sorts = Vec::with_capacity(scope.size_hint().0 + 1);
        let mut args = Vec::with_capacity(scope.size_hint().0);

        sorts.push(sort_to_fixpoint(&sort));
        args.push(Expr::from(var));
        scope
            .filter(|(_, s)| !matches!(s.kind(), SortKind::Loc))
            .map(|(var, sort)| (var, sort_to_fixpoint(&sort)))
            .for_each(|(var, sort)| {
                sorts.push(sort);
                args.push(Var::Free(var).into());
            });

        let kvid = self.kvars.push(sorts);
        Pred::kvar(kvid, args)
    }

    pub fn into_fixpoint(self) -> Vec<fixpoint::KVar> {
        self.kvars
            .into_iter_enumerated()
            .map(|(kvid, sorts)| fixpoint::KVar(kvid, sorts))
            .collect()
    }
}

impl std::ops::Index<KVid> for KVarStore {
    type Output = Vec<fixpoint::Sort>;

    fn index(&self, index: KVid) -> &Self::Output {
        &self.kvars[index]
    }
}

impl PureCtxt<'_> {
    pub fn name_gen(&self) -> IndexGen<Name> {
        let gen = IndexGen::new();
        gen.skip(self.next_name_idx());
        gen
    }

    pub fn breadcrumb(&mut self) -> PureCtxt {
        PureCtxt { cx: self.cx, ptr: Rc::clone(&self.ptr) }
    }

    pub fn snapshot(&self) -> Snapshot {
        Snapshot { node: Rc::downgrade(&self.ptr) }
    }

    pub fn clear(&mut self) {
        self.ptr.borrow_mut().children.clear();
    }

    pub fn scope(&self) -> Scope {
        self.snapshot().scope().unwrap()
    }

    pub fn push_binding<F, P>(&mut self, sort: Sort, f: F) -> Name
    where
        F: FnOnce(Name) -> P,
        P: Into<Pred>,
    {
        let fresh = Name::new(self.next_name_idx());
        self.ptr = self.push_node(NodeKind::Binding(fresh, sort, f(fresh).into()));
        fresh
    }

    pub fn push_pred(&mut self, expr: impl Into<Expr>) {
        self.ptr = self.push_node(NodeKind::Pred(expr.into()));
    }

    pub fn push_loc(&mut self) -> Loc {
        let fresh = Name::new(self.next_name_idx());
        self.ptr = self.push_node(NodeKind::Binding(fresh, Sort::loc(), Pred::tt()));
        Loc::Abstract(fresh)
    }

    pub fn push_head(&mut self, pred: impl Into<Pred>, tag: Tag) {
        let pred = pred.into();
        if !pred.is_true() {
            self.push_node(NodeKind::Head(pred, tag));
        }
    }

    fn next_name_idx(&self) -> usize {
        self.ptr.borrow().nbindings + usize::from(self.ptr.borrow().is_binding())
    }

    fn push_node(&mut self, kind: NodeKind) -> NodePtr {
        debug_assert!(!matches!(self.ptr.borrow().kind, NodeKind::Head(..)));
        let node = Node {
            kind,
            nbindings: self.next_name_idx(),
            parent: Some(Rc::downgrade(&self.ptr)),
            children: vec![],
        };
        let node = Rc::new(RefCell::new(node));
        self.ptr.borrow_mut().children.push(Rc::clone(&node));
        node
    }
}

impl Snapshot {
    pub fn scope(&self) -> Option<Scope> {
        let parents = ParentsIter::new(self.node.upgrade()?);
        let bindings = parents
            .filter_map(|node| {
                let node = node.borrow();
                if let NodeKind::Binding(_, sort, _) = &node.kind {
                    Some(sort.clone())
                } else {
                    None
                }
            })
            .collect_vec()
            .into_iter()
            .rev()
            .collect();
        Some(Scope { bindings })
    }
}

impl Scope {
    pub fn iter(&self) -> impl Iterator<Item = (Name, Sort)> + '_ {
        self.bindings
            .iter_enumerated()
            .map(|(name, sort)| (name, sort.clone()))
    }

    pub fn contains(&self, name: Name) -> bool {
        name.index() < self.bindings.len()
    }
}

impl std::ops::Index<Name> for Scope {
    type Output = Sort;

    fn index(&self, name: Name) -> &Self::Output {
        &self.bindings[name]
    }
}

impl Node {
    fn to_fixpoint(&self, cx: &mut FixpointCtxt) -> Option<fixpoint::Constraint<TagIdx>> {
        match &self.kind {
            NodeKind::Conj => children_to_fixpoint(cx, &self.children),
            NodeKind::Binding(_, sort, _) if matches!(sort.kind(), SortKind::Loc) => {
                children_to_fixpoint(cx, &self.children)
            }
            NodeKind::Binding(name, sort, pred) => {
                let fresh = cx.fresh_name();
                // The name is no longer in scope after we return from `pred_to_fixpoint`
                // but there's no harm in keeping it around as it will just get overwritten if
                // it's used in a different branch of the tree.
                cx.name_map.insert(*name, fresh);
                let (bindings, pred) = pred_to_fixpoint(cx, pred);
                Some(stitch(
                    bindings,
                    fixpoint::Constraint::ForAll(
                        fresh,
                        sort_to_fixpoint(sort),
                        pred,
                        Box::new(children_to_fixpoint(cx, &self.children)?),
                    ),
                ))
            }
            NodeKind::Pred(expr) => {
                Some(fixpoint::Constraint::Guard(
                    expr_to_fixpoint(cx, expr),
                    Box::new(children_to_fixpoint(cx, &self.children)?),
                ))
            }
            NodeKind::Head(pred, tag) => {
                let (bindings, pred) = pred_to_fixpoint(cx, pred);
                Some(stitch(bindings, fixpoint::Constraint::Pred(pred, Some(cx.tag_idx(*tag)))))
            }
        }
    }

    /// Returns `true` if the node kind is [`Binding`].
    ///
    /// [`Binding`]: NodeKind::Binding
    fn is_binding(&self) -> bool {
        matches!(self.kind, NodeKind::Binding(..))
    }

    /// Returns `true` if the node kind is [`Head`].
    ///
    /// [`Head`]: NodeKind::Head
    fn is_head(&self) -> bool {
        matches!(self.kind, NodeKind::Head(..))
    }
}

fn children_to_fixpoint(
    cx: &mut FixpointCtxt,
    children: &[NodePtr],
) -> Option<fixpoint::Constraint<TagIdx>> {
    let mut children = children
        .iter()
        .filter_map(|node| node.borrow().to_fixpoint(cx))
        .collect_vec();
    match children.len() {
        0 => None,
        1 => children.pop(),
        _ => Some(fixpoint::Constraint::Conj(children)),
    }
}

fn pred_to_fixpoint(
    cx: &mut FixpointCtxt,
    refine: &Pred,
) -> (Vec<(fixpoint::Name, fixpoint::Sort, fixpoint::Expr)>, fixpoint::Pred) {
    let mut bindings = vec![];
    let pred = match refine {
        Pred::Expr(expr) => fixpoint::Pred::Expr(expr_to_fixpoint(cx, expr)),
        Pred::KVar(kvid, args) => {
            let args = args.iter().zip(&cx.kvars[*kvid]).map(|(arg, sort)| {
                if let ExprKind::Var(Var::Free(name)) = arg.kind() {
                    cx.name_map[name]
                } else {
                    let fresh = cx.fresh_name();
                    let pred = fixpoint::Expr::BinaryOp(
                        BinOp::Eq,
                        Box::new(fixpoint::Expr::Var(fresh)),
                        Box::new(expr_to_fixpoint(cx, arg)),
                    );
                    bindings.push((fresh, sort.clone(), pred));
                    fresh
                }
            });
            fixpoint::Pred::KVar(*kvid, args.collect())
        }
    };
    (bindings, pred)
}

fn sort_to_fixpoint(sort: &Sort) -> fixpoint::Sort {
    match sort.kind() {
        SortKind::Int | SortKind::Loc => fixpoint::Sort::Int,
        SortKind::Bool => fixpoint::Sort::Bool,
        SortKind::Tuple(sorts) => {
            match &sorts[..] {
                [] => fixpoint::Sort::Unit,
                [_] => unreachable!("1-tuple"),
                [sorts @ .., s1, s2] => {
                    let s1 = Box::new(sort_to_fixpoint(s1));
                    let s2 = Box::new(sort_to_fixpoint(s2));
                    sorts
                        .iter()
                        .map(sort_to_fixpoint)
                        .map(Box::new)
                        .fold(fixpoint::Sort::Pair(s1, s2), |s1, s2| {
                            fixpoint::Sort::Pair(Box::new(s1), s2)
                        })
                }
            }
        }
    }
}

fn expr_to_fixpoint(cx: &FixpointCtxt, expr: &ExprS) -> fixpoint::Expr {
    match expr.kind() {
        ExprKind::Var(Var::Free(name)) => fixpoint::Expr::Var(cx.name_map[name]),
        ExprKind::Constant(c) => fixpoint::Expr::Constant(*c),
        ExprKind::BinaryOp(op, e1, e2) => {
            fixpoint::Expr::BinaryOp(
                *op,
                Box::new(expr_to_fixpoint(cx, e1)),
                Box::new(expr_to_fixpoint(cx, e2)),
            )
        }
        ExprKind::UnaryOp(op, e) => fixpoint::Expr::UnaryOp(*op, Box::new(expr_to_fixpoint(cx, e))),
        ExprKind::Var(Var::Bound) => {
            unreachable!("unexpected bound variable")
        }
        ExprKind::Proj(e, field) => {
            repeat_n(fixpoint::Proj::Snd, *field as usize)
                .chain([fixpoint::Proj::Fst])
                .fold(expr_to_fixpoint(cx, e), |e, proj| fixpoint::Expr::Proj(Box::new(e), proj))
        }
        ExprKind::Tuple(exprs) => tuple_to_fixpoint(cx, exprs),
    }
}

fn tuple_to_fixpoint(cx: &FixpointCtxt, exprs: &[Expr]) -> fixpoint::Expr {
    match exprs {
        [] => fixpoint::Expr::Unit,
        [_] => unreachable!("1-tuple"),
        [e1, e2] => {
            fixpoint::Expr::Pair(
                Box::new(expr_to_fixpoint(cx, e1)),
                Box::new(expr_to_fixpoint(cx, e2)),
            )
        }
        [e, exprs @ ..] => {
            fixpoint::Expr::Pair(
                Box::new(expr_to_fixpoint(cx, e)),
                Box::new(tuple_to_fixpoint(cx, exprs)),
            )
        }
    }
}

fn stitch(
    bindings: Vec<(fixpoint::Name, fixpoint::Sort, fixpoint::Expr)>,
    c: fixpoint::Constraint<TagIdx>,
) -> fixpoint::Constraint<TagIdx> {
    bindings.into_iter().rev().fold(c, |c, (name, sort, e)| {
        fixpoint::Constraint::ForAll(name, sort, fixpoint::Pred::Expr(e), Box::new(c))
    })
}

struct ParentsIter {
    ptr: Option<NodePtr>,
}

impl ParentsIter {
    fn new(ptr: NodePtr) -> Self {
        Self { ptr: Some(ptr) }
    }
}

impl Iterator for ParentsIter {
    type Item = NodePtr;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(ptr) = self.ptr.take() {
            self.ptr = ptr.borrow().parent.as_ref().and_then(WeakNodePtr::upgrade);
            Some(ptr)
        } else {
            None
        }
    }
}

mod pretty {
    use std::fmt::{self, Write};

    use itertools::Itertools;
    use liquid_rust_common::format::PadAdapter;
    use rustc_middle::ty::TyCtxt;

    use super::*;
    use crate::pretty::*;

    fn bindings_chain(ptr: &NodePtr) -> (Vec<(Name, Sort, Pred)>, Vec<NodePtr>) {
        fn go(
            ptr: &NodePtr,
            mut bindings: Vec<(Name, Sort, Pred)>,
        ) -> (Vec<(Name, Sort, Pred)>, Vec<NodePtr>) {
            let node = ptr.borrow();
            if let NodeKind::Binding(name, sort, pred) = &node.kind {
                bindings.push((*name, sort.clone(), pred.clone()));
                if let [child] = &node.children[..] {
                    go(child, bindings)
                } else {
                    (bindings, node.children.clone())
                }
            } else {
                (bindings, vec![Rc::clone(ptr)])
            }
        }
        go(ptr, vec![])
    }

    fn preds_chain(ptr: &NodePtr) -> (Vec<Expr>, Vec<NodePtr>) {
        fn go(ptr: &NodePtr, mut preds: Vec<Expr>) -> (Vec<Expr>, Vec<NodePtr>) {
            let node = ptr.borrow();
            if let NodeKind::Pred(e) = &node.kind {
                preds.push(e.clone());
                if let [child] = &node.children[..] {
                    go(child, preds)
                } else {
                    (preds, node.children.clone())
                }
            } else {
                (preds, vec![Rc::clone(ptr)])
            }
        }
        go(ptr, vec![])
    }

    impl Pretty for ConstraintBuilder {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!("{:?}", &self.root)
        }

        fn default_cx(tcx: TyCtxt) -> PPrintCx {
            PPrintCx::default(tcx).kvar_args(Visibility::Truncate(1))
        }
    }

    impl Pretty for NodePtr {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            let node = self.borrow();
            match &node.kind {
                NodeKind::Conj => {
                    w!("{:?}", join!("\n", &node.children))
                }
                NodeKind::Binding(name, sort, pred) => {
                    let (bindings, children) = if cx.bindings_chain {
                        bindings_chain(self)
                    } else {
                        (vec![(*name, sort.clone(), pred.clone())], node.children.clone())
                    };

                    w!(
                        "∀ {}.{:?}",
                        ^bindings
                            .into_iter()
                            .format_with(", ", |(name, sort, pred), f| {
                                if pred.is_true() {
                                    f(&format_args_cx!("{:?}: {:?}", ^name, sort))
                                } else {
                                    f(&format_args_cx!("{:?}: {:?}{{{:?}}}", ^name, sort, pred))
                                }
                            }),
                        children
                    )
                }
                NodeKind::Pred(expr) => {
                    let (exprs, children) = if cx.preds_chain {
                        preds_chain(self)
                    } else {
                        (vec![expr.clone()], node.children.clone())
                    };
                    w!(
                        "{} ⇒{:?}",
                        ^exprs
                            .into_iter()
                            .filter(|e| !e.is_true())
                            .format_with(" ∧ ", |e, f| {
                                let e = if cx.simplify_exprs { e.simplify() } else { e.clone() };
                                if e.is_atom() {
                                    f(&format_args_cx!("{:?}", ^e))
                                } else {
                                    f(&format_args_cx!("({:?})", ^e))
                                }
                            }),
                        children
                    )
                }
                NodeKind::Head(pred, tag) => {
                    if pred.is_atom() {
                        w!("{:?}", pred)?;
                    } else {
                        w!("({:?})", pred)?;
                    }
                    if cx.tags {
                        w!(" [{:?}]", tag)?;
                    }
                    Ok(())
                }
            }
        }
    }

    impl Pretty for Vec<NodePtr> {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let mut f = PadAdapter::wrap_fmt(f);
            define_scoped!(cx, f);
            match &self[..] {
                [] => w!(" true"),
                [n] => {
                    if n.borrow().is_head() {
                        w!(" ")?;
                    } else {
                        w!("\n")?;
                    }
                    w!("{:?}", Rc::clone(n))
                }
                _ => w!("\n{:?}", join!("\n", self.iter().map(Rc::clone))),
            }
        }
    }

    impl Pretty for PureCtxt<'_> {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            let parents = ParentsIter::new(Rc::clone(&self.ptr)).collect_vec();
            write!(
                f,
                "{{{}}}",
                parents
                    .into_iter()
                    .rev()
                    .filter(|n| {
                        matches!(n.borrow().kind, NodeKind::Binding(..) | NodeKind::Pred(..))
                    })
                    .format_with(", ", |n, f| {
                        let n = n.borrow();
                        match &n.kind {
                            NodeKind::Binding(name, sort, pred) => {
                                f(&format_args_cx!("{:?}: {:?}", ^name, sort))?;
                                if !pred.is_true() {
                                    f(&format_args_cx!(", {:?}", pred))?;
                                }
                                Ok(())
                            }
                            NodeKind::Pred(e) => f(&format_args!("{:?}", e)),
                            NodeKind::Conj | NodeKind::Head(..) => unreachable!(),
                        }
                    })
            )
        }

        fn default_cx(tcx: TyCtxt) -> PPrintCx {
            PPrintCx::default(tcx).kvar_args(Visibility::Truncate(1))
            // PPrintCx::default(tcx).kvar_args(Visibility::Show)
        }
    }

    impl Pretty for Scope {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            write!(
                f,
                "[{}]",
                self.bindings
                    .iter_enumerated()
                    .format_with(", ", |(name, sort), f| {
                        f(&format_args_cx!("{:?}: {:?}", ^name, sort))
                    })
            )
        }
    }

    impl_debug_with_default_cx!(ConstraintBuilder => "constraint_builder", PureCtxt<'_>, Scope);
}
