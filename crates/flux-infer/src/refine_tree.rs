use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    ops::ControlFlow,
    rc::{Rc, Weak},
};

use flux_common::{index::IndexVec, iter::IterExt, tracked_span_bug};
use flux_config::OverflowMode;
use flux_macros::DebugAsJson;
use flux_middle::{
    global_env::GlobalEnv,
    pretty::{PrettyCx, PrettyNested, format_cx},
    queries::QueryResult,
    rty::{
        BaseTy, EVid, Expr, ExprKind, KVid, Name, Sort, Ty, TyKind, Var,
        fold::{TypeFoldable, TypeSuperVisitable, TypeVisitable, TypeVisitor},
    },
};
use itertools::Itertools;
use rustc_data_structures::snapshot_map::SnapshotMap;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_index::newtype_index;
use rustc_middle::ty::TyCtxt;
use rustc_span::{Span, Symbol};
use serde::Serialize;

use crate::{
    evars::EVarStore,
    fixpoint_encoding::{FixpointCtxt, fixpoint},
    infer::{ConstrReason, Tag, TypeTrace},
};

/// A *refine*ment *tree* tracks the "tree-like structure" of refinement variables and predicates
/// generated during refinement type-checking. This tree can be encoded as a fixpoint constraint
/// whose satisfiability implies the safety of a function.
///
/// We try to hide the representation of the tree as much as possible and only a couple of operations
/// can be used to manipulate the structure of the tree explicitly. Instead, the tree is mostly
/// constructed implicitly via a restricted api provided by [`Cursor`]. Some methods operate on *nodes*
/// of the tree which we try to keep abstract, but it is important to remember that there's an
/// underlying tree.
///
/// The current implementation uses [`Rc`] and [`RefCell`] to represent the tree, but we ensure
/// statically that the [`RefineTree`] is the single owner of the data and require a mutable reference
/// to it for all mutations, i.e., we could in theory replace the [`RefCell`] with an [`UnsafeCell`]
/// (or a [`GhostCell`]).
///
/// [`UnsafeCell`]: std::cell::UnsafeCell
/// [`GhostCell`]: https://docs.rs/ghost-cell/0.2.3/ghost_cell/ghost_cell/struct.GhostCell.html
pub struct RefineTree {
    root: NodePtr,
}

impl RefineTree {
    pub(crate) fn new(params: Vec<(Var, Sort)>) -> RefineTree {
        let root =
            Node { kind: NodeKind::Root(params), nbindings: 0, parent: None, children: vec![] };
        let root = NodePtr(Rc::new(RefCell::new(root)));
        RefineTree { root }
    }

    pub(crate) fn simplify(&mut self, genv: GlobalEnv) {
        self.root
            .borrow_mut()
            .simplify(SimplifyPhase::Full(genv), &mut SnapshotMap::default());
        self.root.borrow_mut().simplify_bot();
        self.root.borrow_mut().simplify_top();
    }

    pub(crate) fn into_fixpoint(
        self,
        cx: &mut FixpointCtxt<Tag>,
    ) -> QueryResult<fixpoint::Constraint> {
        Ok(self
            .root
            .borrow()
            .to_fixpoint(cx, HashMap::new(), 0)?
            .unwrap_or(fixpoint::Constraint::TRUE))
    }

    pub(crate) fn cursor_at_root(&mut self) -> Cursor<'_> {
        Cursor { ptr: NodePtr(Rc::clone(&self.root)), tree: self }
    }

    pub(crate) fn replace_evars(&mut self, evars: &EVarStore) -> Result<(), EVid> {
        self.root.borrow_mut().replace_evars(evars)
    }
}

/// A cursor into the [refinement tree]. More specifically, a [`Cursor`] represents a path from the
/// root to some internal node in a [refinement tree].
///
/// [refinement tree]: RefineTree
pub struct Cursor<'a> {
    tree: &'a mut RefineTree,
    ptr: NodePtr,
}

impl Cursor<'_> {
    /// Moves the cursor to the specified [marker]. If `clear_children` is `true`, all children of
    /// the node are removed after moving the cursor, invalidating any markers pointing to a node
    /// within those children.
    ///
    /// [marker]: Marker
    pub(crate) fn move_to(&mut self, marker: &Marker, clear_children: bool) -> Option<Cursor<'_>> {
        let ptr = marker.ptr.upgrade()?;
        if clear_children {
            ptr.borrow_mut().children.clear();
        }
        Some(Cursor { ptr, tree: self.tree })
    }

    /// Returns a marker to the current node
    #[must_use]
    pub(crate) fn marker(&self) -> Marker {
        Marker { ptr: NodePtr::downgrade(&self.ptr) }
    }

    #[must_use]
    pub(crate) fn branch(&mut self) -> Cursor<'_> {
        Cursor { tree: self.tree, ptr: NodePtr::clone(&self.ptr) }
    }

    pub(crate) fn vars(&self) -> impl Iterator<Item = (Var, Sort)> {
        // TODO(nilehmann) we could incrementally cache the scope
        self.ptr.scope().into_iter()
    }

    #[expect(dead_code, reason = "used for debugging")]
    pub(crate) fn push_trace(&mut self, trace: TypeTrace) {
        self.ptr = self.ptr.push_node(NodeKind::Trace(trace));
    }

    /// Defines a fresh refinement variable with the given `sort` and advance the cursor to the new
    /// node. It returns the freshly generated name for the variable.
    pub(crate) fn define_var(
        &mut self,
        sort: &Sort,
        binder_provenance: Option<BinderProvenance>,
    ) -> Name {
        let fresh = Name::from_usize(self.ptr.next_name_idx());
        self.ptr = self
            .ptr
            .push_node(NodeKind::ForAll(fresh, sort.clone(), binder_provenance));
        fresh
    }

    /// Pushes an [assumption] and moves the cursor into the new node.
    ///
    /// [assumption]: NodeKind::Assumption
    pub(crate) fn assume_pred(&mut self, pred: impl Into<Expr>) {
        let pred = pred.into();
        if !pred.is_trivially_true() {
            self.ptr = self.ptr.push_node(NodeKind::Assumption(pred));
        }
    }

    /// Pushes a predicate that must be true assuming variables and predicates in the current branch
    /// of the tree (i.e., it pushes a [`NodeKind::Head`]). This methods does not advance the cursor.
    pub(crate) fn check_pred(&mut self, pred: impl Into<Expr>, tag: Tag) {
        let pred = pred.into();
        if !pred.is_trivially_true() {
            self.ptr.push_node(NodeKind::Head(pred, tag));
        }
    }

    /// Convenience method to push an assumption followed by a predicate that needs to be checked.
    /// This method does not advance the cursor.
    pub(crate) fn check_impl(&mut self, pred1: impl Into<Expr>, pred2: impl Into<Expr>, tag: Tag) {
        self.ptr
            .push_node(NodeKind::Assumption(pred1.into()))
            .push_node(NodeKind::Head(pred2.into(), tag));
    }

    pub(crate) fn assume_invariants(
        &mut self,
        tcx: TyCtxt,
        ty: &Ty,
        overflow_checking: OverflowMode,
    ) {
        struct Visitor<'a, 'b, 'tcx> {
            tcx: TyCtxt<'tcx>,
            cursor: &'a mut Cursor<'b>,
            overflow_mode: OverflowMode,
        }
        impl TypeVisitor for Visitor<'_, '_, '_> {
            fn visit_bty(&mut self, bty: &BaseTy) -> ControlFlow<!> {
                match bty {
                    BaseTy::Adt(adt_def, substs) if adt_def.is_box() => substs.visit_with(self),
                    BaseTy::Ref(_, ty, _) => ty.visit_with(self),
                    BaseTy::Tuple(tys) => tys.visit_with(self),
                    _ => ControlFlow::Continue(()),
                }
            }

            fn visit_ty(&mut self, ty: &Ty) -> ControlFlow<!> {
                if let TyKind::Indexed(bty, idx) = ty.kind()
                    && !idx.has_escaping_bvars()
                {
                    for invariant in bty.invariants(self.tcx, self.overflow_mode) {
                        let invariant = invariant.apply(idx);
                        self.cursor.assume_pred(&invariant);
                    }
                }
                ty.super_visit_with(self)
            }
        }
        let _ = ty.visit_with(&mut Visitor { tcx, cursor: self, overflow_mode: overflow_checking });
    }
}

/// A marker is a pointer to a node in the [refinement tree] that can be used to query information
/// about that node or to move the cursor. A marker may become invalid if the underlying node is
/// [cleared].
///
/// [cleared]: Cursor::move_to
/// [refinement tree]: RefineTree
pub struct Marker {
    ptr: WeakNodePtr,
}

impl Marker {
    /// Returns the [`scope`] at the marker if it is still valid or [`None`] otherwise.
    ///
    /// [`scope`]: Scope
    pub fn scope(&self) -> Option<Scope> {
        Some(self.ptr.upgrade()?.scope())
    }

    pub fn has_free_vars<T: TypeVisitable>(&self, t: &T) -> bool {
        let ptr = self
            .ptr
            .upgrade()
            .unwrap_or_else(|| tracked_span_bug!("`has_free_vars` called on invalid `Marker`"));

        let nbindings = ptr.next_name_idx();

        !t.fvars().into_iter().all(|name| name.index() < nbindings)
    }
}

/// A list of refinement variables and their sorts.
#[derive(PartialEq, Eq)]
pub struct Scope {
    params: Vec<(Var, Sort)>,
    bindings: IndexVec<Name, Sort>,
}

impl Scope {
    pub(crate) fn iter(&self) -> impl Iterator<Item = (Var, Sort)> + '_ {
        itertools::chain(
            self.params.iter().cloned(),
            self.bindings
                .iter_enumerated()
                .map(|(name, sort)| (Var::Free(name), sort.clone())),
        )
    }

    fn into_iter(self) -> impl Iterator<Item = (Var, Sort)> {
        itertools::chain(
            self.params,
            self.bindings
                .into_iter_enumerated()
                .map(|(name, sort)| (Var::Free(name), sort.clone())),
        )
    }

    /// Whether `t` has any free variables not in this scope
    pub fn has_free_vars<T: TypeFoldable>(&self, t: &T) -> bool {
        !self.contains_all(t.fvars())
    }

    fn contains_all(&self, iter: impl IntoIterator<Item = Name>) -> bool {
        iter.into_iter().all(|name| self.contains(name))
    }

    fn contains(&self, name: Name) -> bool {
        name.index() < self.bindings.len()
    }
}

struct Node {
    kind: NodeKind,
    /// Number of bindings between the root and this node's parent, i.e., we have
    /// as an invariant that `nbindings` equals the number of [`NodeKind::ForAll`]
    /// nodes from the parent of this node to the root.
    nbindings: usize,
    parent: Option<WeakNodePtr>,
    children: Vec<NodePtr>,
}

#[derive(Clone)]
struct NodePtr(Rc<RefCell<Node>>);

impl NodePtr {
    fn downgrade(this: &Self) -> WeakNodePtr {
        WeakNodePtr(Rc::downgrade(&this.0))
    }

    fn push_node(&mut self, kind: NodeKind) -> NodePtr {
        debug_assert!(!matches!(self.borrow().kind, NodeKind::Head(..)));
        let node = Node {
            kind,
            nbindings: self.next_name_idx(),
            parent: Some(NodePtr::downgrade(self)),
            children: vec![],
        };
        let node = NodePtr(Rc::new(RefCell::new(node)));
        self.borrow_mut().children.push(NodePtr::clone(&node));
        node
    }

    fn next_name_idx(&self) -> usize {
        self.borrow().nbindings + usize::from(self.borrow().is_forall())
    }

    fn scope(&self) -> Scope {
        let mut params = None;
        let parents = ParentsIter::new(self.clone());
        let bindings = parents
            .filter_map(|node| {
                let node = node.borrow();
                match &node.kind {
                    NodeKind::Root(p) => {
                        params = Some(p.clone());
                        None
                    }
                    NodeKind::ForAll(_, sort, _) => Some(sort.clone()),
                    _ => None,
                }
            })
            .collect_vec()
            .into_iter()
            .rev()
            .collect();
        Scope { bindings, params: params.unwrap_or_default() }
    }
}

struct WeakNodePtr(Weak<RefCell<Node>>);

impl WeakNodePtr {
    fn upgrade(&self) -> Option<NodePtr> {
        Some(NodePtr(self.0.upgrade()?))
    }
}

enum NodeKind {
    /// List of const and refinement generics
    Root(Vec<(Var, Sort)>),
    ForAll(Name, Sort, Option<BinderProvenance>),
    Assumption(Expr),
    Head(Expr, Tag),
    True,
    /// Used for debugging. See [`TypeTrace`]
    Trace(TypeTrace),
}

impl std::ops::Index<Name> for Scope {
    type Output = Sort;

    fn index(&self, name: Name) -> &Self::Output {
        &self.bindings[name]
    }
}

impl std::ops::Deref for NodePtr {
    type Target = Rc<RefCell<Node>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Clone, Copy)]
enum SimplifyPhase<'genv, 'tcx> {
    /// Normalize and simplify inner `Expr`
    Full(GlobalEnv<'genv, 'tcx>),
    /// Only propagate `true` (TOP) and `false` (BOT)
    Partial,
}
type BinderDepth = usize;
pub type BinderDeps = HashMap<Name, (Option<BinderProvenance>, BinderDepth, HashSet<Name>)>;

impl Node {
    fn simplify(&mut self, phase: SimplifyPhase, assumed_preds: &mut SnapshotMap<Expr, ()>) {
        // First, simplify the node itself
        match &mut self.kind {
            NodeKind::Head(pred, tag) => {
                let pred = match phase {
                    SimplifyPhase::Full(genv) => pred.normalize(genv).simplify(assumed_preds),
                    SimplifyPhase::Partial => pred.clone(),
                };
                if pred.is_trivially_true() {
                    self.kind = NodeKind::True;
                } else {
                    self.kind = NodeKind::Head(pred, *tag);
                }
            }
            NodeKind::Assumption(pred) => {
                if let SimplifyPhase::Full(genv) = phase {
                    *pred = pred.normalize(genv).simplify(assumed_preds);
                }
                pred.visit_conj(|conjunct| {
                    assumed_preds.insert(conjunct.erase_spans(), ());
                });
            }
            _ => {}
        }
        let is_false_asm =
            matches!(&self.kind, NodeKind::Assumption(pred) if pred.is_trivially_false());

        // Then simplify the children
        // (the order matters here because we need to collect assumed preds first)
        for child in &self.children {
            let current_version = assumed_preds.snapshot();
            child.borrow_mut().simplify(phase, assumed_preds);
            assumed_preds.rollback_to(current_version);
        }

        // Then remove any unnecessary children
        match &mut self.kind {
            NodeKind::Head(..) | NodeKind::True => {}
            NodeKind::Assumption(_)
            | NodeKind::Trace(_)
            | NodeKind::Root(_)
            | NodeKind::ForAll(..) => {
                self.children
                    .extract_if(.., |child| {
                        is_false_asm || matches!(&child.borrow().kind, NodeKind::True)
                    })
                    .for_each(drop);
            }
        }
        if !self.is_leaf() && self.children.is_empty() {
            self.kind = NodeKind::True;
        }
    }

    fn is_leaf(&self) -> bool {
        matches!(self.kind, NodeKind::Head(..) | NodeKind::True)
    }

    fn replace_evars(&mut self, evars: &EVarStore) -> Result<(), EVid> {
        for child in &self.children {
            child.borrow_mut().replace_evars(evars)?;
        }
        match &mut self.kind {
            NodeKind::Assumption(pred) => *pred = evars.replace_evars(pred)?,
            NodeKind::Head(pred, _) => {
                *pred = evars.replace_evars(pred)?;
            }
            NodeKind::Trace(trace) => {
                evars.replace_evars(trace)?;
            }
            NodeKind::Root(_) | NodeKind::ForAll(..) | NodeKind::True => {}
        }
        Ok(())
    }

    fn to_fixpoint(
        &self,
        cx: &mut FixpointCtxt<Tag>,
        mut binder_deps: BinderDeps,
        binder_depth: BinderDepth,
    ) -> QueryResult<Option<fixpoint::Constraint>> {
        let cstr = match &self.kind {
            NodeKind::Trace(_) | NodeKind::ForAll(_, Sort::Loc, _) => {
                children_to_fixpoint(cx, &self.children, binder_deps, binder_depth)?
            }

            NodeKind::Root(params) => {
                let Some(children) = children_to_fixpoint(cx, &self.children, binder_deps, binder_depth)? else {
                    return Ok(None);
                };
                let mut constr = children;
                for (var, sort) in params.iter().rev() {
                    if sort.is_loc() {
                        continue;
                    }
                    constr = fixpoint::Constraint::ForAll(
                        fixpoint::Bind {
                            name: cx.var_to_fixpoint(var),
                            sort: cx.sort_to_fixpoint(sort),
                            pred: fixpoint::Pred::TRUE,
                        },
                        Box::new(constr),
                    );
                }
                Some(constr)
            }
            NodeKind::ForAll(name, sort, bp) => {
                binder_deps.insert(*name, (bp.clone(), binder_depth, HashSet::new()));
                cx.with_name_map(*name, |cx, fresh| -> QueryResult<_> {
                    let Some(children) = children_to_fixpoint(cx, &self.children, binder_deps, binder_depth + 1)?
                    else {
                        return Ok(None);
                    };
                    Ok(Some(fixpoint::Constraint::ForAll(
                        fixpoint::Bind {
                            name: fixpoint::Var::Local(fresh),
                            sort: cx.sort_to_fixpoint(sort),
                            pred: fixpoint::Pred::TRUE,
                        },
                        Box::new(children),
                    )))
                })?
            }
            NodeKind::Assumption(pred) => {
                // TODO: do we need to track relations between variables whenever
                // cx.assumption_to_fixpoint is called (i.e. do we also need to track
                // for assumptions inside of NodeKind::Head expressions) or is doing it
                // only for NodeKind::Assumption sufficient?
                let (mut bindings, pred) = cx.assumption_to_fixpoint(pred, &mut binder_deps)?;
                let Some(cstr) = children_to_fixpoint(cx, &self.children, binder_deps, binder_depth)? else {
                    return Ok(None);
                };
                bindings.push(fixpoint::Bind {
                    name: fixpoint::Var::Underscore,
                    sort: fixpoint::Sort::Int,
                    pred,
                });
                Some(fixpoint::Constraint::foralls(bindings, cstr))
            }
            NodeKind::Head(pred, tag) => {
                Some(cx.head_to_fixpoint(pred, |span| tag.with_dst(span), binder_deps)?)
            }
            NodeKind::True => None,
        };
        Ok(cstr)
    }

    /// Returns `true` if the node kind is [`ForAll`].
    ///
    /// [`ForAll`]: NodeKind::ForAll
    fn is_forall(&self) -> bool {
        matches!(self.kind, NodeKind::ForAll(..))
    }

    /// Returns `true` if the node kind is [`Head`].
    ///
    /// [`Head`]: NodeKind::Head
    fn is_head(&self) -> bool {
        matches!(self.kind, NodeKind::Head(..))
    }
}

fn children_to_fixpoint(
    cx: &mut FixpointCtxt<Tag>,
    children: &[NodePtr],
    binder_deps: BinderDeps,
    binder_depth: BinderDepth,
) -> QueryResult<Option<fixpoint::Constraint>> {
    let mut children = children
        .iter()
        .filter_map(|node| {
            node.borrow()
                .to_fixpoint(cx, binder_deps.clone(), binder_depth)
                .transpose()
        })
        .try_collect_vec()?;
    let cstr = match children.len() {
        0 => None,
        1 => children.pop(),
        _ => Some(fixpoint::Constraint::Conj(children)),
    };
    Ok(cstr)
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

    use flux_middle::pretty::*;
    use pad_adapter::PadAdapter;

    use super::*;

    type Binding = (Name, Sort, Option<BinderProvenance>);

    fn bindings_chain(ptr: &NodePtr) -> (Vec<Binding>, Vec<NodePtr>) {
        fn go(ptr: &NodePtr, mut bindings: Vec<Binding>) -> (Vec<Binding>, Vec<NodePtr>) {
            let node = ptr.borrow();
            if let NodeKind::ForAll(name, sort, bp) = &node.kind {
                bindings.push((*name, sort.clone(), bp.clone()));
                if let [child] = &node.children[..] {
                    go(child, bindings)
                } else {
                    (bindings, node.children.clone())
                }
            } else {
                (bindings, vec![NodePtr::clone(ptr)])
            }
        }
        go(ptr, vec![])
    }

    fn preds_chain(ptr: &NodePtr) -> (Vec<Expr>, Vec<NodePtr>) {
        fn go(ptr: &NodePtr, mut preds: Vec<Expr>) -> (Vec<Expr>, Vec<NodePtr>) {
            let node = ptr.borrow();
            if let NodeKind::Assumption(pred) = &node.kind {
                preds.push(pred.clone());
                if let [child] = &node.children[..] {
                    go(child, preds)
                } else {
                    (preds, node.children.clone())
                }
            } else {
                (preds, vec![NodePtr::clone(ptr)])
            }
        }
        go(ptr, vec![])
    }

    impl Pretty for RefineTree {
        fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            w!(cx, f, "{:?}", &self.root)
        }
    }

    impl Pretty for NodePtr {
        fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let node = self.borrow();
            match &node.kind {
                NodeKind::Trace(trace) => {
                    w!(cx, f, "@ {:?}", ^trace)?;
                    w!(cx, with_padding(f), "\n{:?}", join!("\n", &node.children))
                }
                NodeKind::Root(bindings) => {
                    w!(cx, f,
                        "∀ {}.",
                        ^bindings
                            .iter()
                            .format_with(", ", |(name, sort), f| {
                                f(&format_args_cx!(cx, "{:?}: {:?}", ^name, sort))
                            })
                    )?;
                    fmt_children(&node.children, cx, f)
                }
                NodeKind::ForAll(name, sort, bp) => {
                    let (bindings, children) = if cx.bindings_chain {
                        bindings_chain(self)
                    } else {
                        (vec![(*name, sort.clone(), bp.clone())], node.children.clone())
                    };

                    w!(cx, f,
                        "∀ {}.",
                        ^bindings
                            .into_iter()
                            .format_with(", ", |(name, sort, bp), f| {
                                if cx.tags && let Some(bp) = bp {
                                    f(&format_args_cx!(cx, "{:?}: {:?} ~ {:?}", ^name, sort, bp))
                                } else {
                                    f(&format_args_cx!(cx, "{:?}: {:?}", ^name, sort))
                                }
                            })
                    )?;
                    fmt_children(&children, cx, f)
                }
                NodeKind::Assumption(pred) => {
                    let (preds, children) = if cx.preds_chain {
                        preds_chain(self)
                    } else {
                        (vec![pred.clone()], node.children.clone())
                    };
                    let guard = Expr::and_from_iter(preds).simplify(&SnapshotMap::default());
                    w!(cx, f, "{:?} =>", parens!(guard, !guard.is_atom()))?;
                    fmt_children(&children, cx, f)
                }
                NodeKind::Head(pred, tag) => {
                    let pred = if cx.simplify_exprs {
                        pred.simplify(&SnapshotMap::default())
                    } else {
                        pred.clone()
                    };
                    w!(cx, f, "{:?}", parens!(pred, !pred.is_atom()))?;
                    if cx.tags {
                        w!(cx, f, " ~ {:?}", tag)?;
                    }
                    Ok(())
                }
                NodeKind::True => {
                    w!(cx, f, "true")
                }
            }
        }
    }

    fn fmt_children(
        children: &[NodePtr],
        cx: &PrettyCx,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        match children {
            [] => w!(cx, f, " true"),
            [n] => {
                if n.borrow().is_head() {
                    w!(cx, f, " {:?}", n)
                } else {
                    w!(cx, with_padding(f), "\n{:?}", n)
                }
            }
            _ => w!(cx, with_padding(f), "\n{:?}", join!("\n", children)),
        }
    }

    impl Pretty for BinderProvenance {
        fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self.span {
                Some(s) => {
                    w!(cx, f, "{:?} at {:?}", &self.originator, &s)
                }
                None => {
                    w!(cx, f, "{:?} (span unknown)", &self.originator)
                }
            }
        }
    }

    impl Pretty for BinderOriginator {
        fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            w!(cx, f, "{:?}", ^self)
        }
    }

    impl Pretty for Cursor<'_> {
        fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let mut elements = vec![];
            for node in ParentsIter::new(NodePtr::clone(&self.ptr)) {
                let n = node.borrow();
                match &n.kind {
                    NodeKind::Root(bindings) => {
                        // We reverse here because is reversed again at the end
                        for (name, sort) in bindings.iter().rev() {
                            elements.push(format_cx!(cx, "{:?}: {:?}", ^name, sort));
                        }
                    }
                    NodeKind::ForAll(name, sort, _) => {
                        elements.push(format_cx!(cx, "{:?}: {:?}", ^name, sort));
                    }
                    NodeKind::Assumption(pred) => {
                        elements.push(format_cx!(cx, "{:?}", pred));
                    }
                    _ => {}
                }
            }
            write!(f, "{{{}}}", elements.into_iter().rev().format(", "))
        }
    }

    impl Pretty for Scope {
        fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(
                f,
                "[bindings = {}, reftgenerics = {}]",
                self.bindings
                    .iter_enumerated()
                    .format_with(", ", |(name, sort), f| {
                        f(&format_args_cx!(cx, "{:?}: {:?}", ^name, sort))
                    }),
                self.params
                    .iter()
                    .format_with(", ", |(param_const, sort), f| {
                        f(&format_args_cx!(cx, "{:?}: {:?}", ^param_const, sort))
                    }),
            )
        }
    }

    fn with_padding<'a, 'b>(f: &'a mut fmt::Formatter<'b>) -> PadAdapter<'a, 'b, 'static> {
        PadAdapter::with_padding(f, "  ")
    }

    impl_debug_with_default_cx!(
        RefineTree => "refine_tree",
        Cursor<'_> => "cursor",
        Scope,
    );
}

/// An explicit representation of a path in the [`RefineTree`] used for debugging/tracing/serialization ONLY.
#[derive(Serialize, DebugAsJson)]
pub struct RefineCtxtTrace {
    bindings: Vec<RcxBind>,
    exprs: Vec<String>,
}

#[derive(Serialize)]
struct RcxBind {
    name: String,
    sort: String,
}

impl RefineCtxtTrace {
    pub fn new(genv: GlobalEnv, cursor: &Cursor) -> Self {
        let parents = ParentsIter::new(NodePtr::clone(&cursor.ptr)).collect_vec();
        let mut bindings = vec![];
        let mut exprs = vec![];
        let cx = &PrettyCx::default(genv).show_kvar_args();

        parents.into_iter().rev().for_each(|ptr| {
            let node = ptr.borrow();
            match &node.kind {
                NodeKind::ForAll(name, sort, _) => {
                    let bind = RcxBind {
                        name: format_cx!(cx, "{:?}", ^name),
                        sort: format_cx!(cx, "{:?}", sort),
                    };
                    bindings.push(bind);
                }
                NodeKind::Assumption(e)
                    if !e.simplify(&SnapshotMap::default()).is_trivially_true() =>
                {
                    e.visit_conj(|e| {
                        exprs.push(e.nested_string(cx));
                    });
                }
                NodeKind::Root(binds) => {
                    for (name, sort) in binds {
                        let bind = RcxBind {
                            name: format_cx!(cx, "{:?}", name),
                            sort: format_cx!(cx, "{:?}", sort),
                        };
                        bindings.push(bind);
                    }
                }
                _ => (),
            }
        });
        Self { bindings, exprs }
    }
}

impl Node {
    /// replace bot-kvars with false
    fn simplify_bot(&mut self) {
        let graph = ConstraintDeps::new(self);
        let bots = graph.bot_kvars();
        self.simplify_with_assignment(&bots);
        self.simplify(SimplifyPhase::Partial, &mut SnapshotMap::default());
    }

    /// replace top-kvars with true
    fn simplify_top(&mut self) {
        let graph = ConstraintDeps::new(self);
        let tops = graph.top_kvars();
        self.simplify_with_assignment(&tops);
        self.simplify(SimplifyPhase::Partial, &mut SnapshotMap::default());
    }

    /// simplifies assumptions and heads using the TOP/BOT kvar assignment; follow
    /// with a call to `simplify` to delete constraints with FALSE assm.
    fn simplify_with_assignment(&mut self, assignment: &Assignment) {
        match &mut self.kind {
            NodeKind::Head(pred, tag) => {
                let pred = assignment.simplify(pred);
                self.kind = NodeKind::Head(pred, *tag);
            }
            NodeKind::Assumption(pred) => {
                let pred = assignment.simplify(pred);
                self.kind = NodeKind::Assumption(pred);
            }
            _ => {}
        }
        for child in &self.children {
            child.borrow_mut().simplify_with_assignment(assignment);
        }
    }
}

#[derive(Debug)]
struct ConstraintDeps {
    /// assumptions for each clause
    assumptions: IndexVec<ClauseId, FxHashSet<KVid>>,
    /// head of each clause
    heads: IndexVec<ClauseId, Head>,
}

impl ConstraintDeps {
    fn new(node: &Node) -> Self {
        let mut graph = Self { assumptions: IndexVec::default(), heads: IndexVec::default() };
        graph.build(node, &mut vec![]);
        graph
    }

    fn insert_clause(&mut self, assumptions: &[KVid], head: Head) {
        self.assumptions.push(assumptions.iter().copied().collect());
        self.heads.push(head);
    }

    fn build(&mut self, node: &Node, assumptions: &mut Vec<KVid>) {
        let n = assumptions.len();
        match &node.kind {
            NodeKind::Head(expr, _) => {
                expr.visit_conj(|e| {
                    if let ExprKind::KVar(kvar) = e.kind() {
                        self.insert_clause(assumptions, Head::KVar(kvar.kvid));
                    } else {
                        self.insert_clause(assumptions, Head::Conc);
                    }
                });
            }
            NodeKind::Assumption(expr) => {
                expr.visit_conj(|e| {
                    if let ExprKind::KVar(kvar) = e.kind() {
                        assumptions.push(kvar.kvid);
                    }
                });
            }
            _ => {}
        };

        for child in &node.children {
            self.build(&child.borrow(), assumptions);
        }

        assumptions.truncate(n); // restore ctx
    }

    /// set of edges where kvid appears as ASSM
    fn kv_lhs(&self) -> FxHashMap<KVid, Vec<ClauseId>> {
        let mut res: FxHashMap<KVid, Vec<ClauseId>> = FxHashMap::default();
        for (clause_id, kvids) in self.assumptions.iter_enumerated() {
            for kvid in kvids {
                res.entry(*kvid).or_default().push(clause_id);
            }
        }
        res
    }

    /// set of edges where kvid appears as HEAD
    fn kv_rhs(&self) -> FxHashMap<KVid, Vec<ClauseId>> {
        let mut res: FxHashMap<KVid, Vec<ClauseId>> = FxHashMap::default();
        for (clause_id, head) in self.heads.iter_enumerated() {
            if let Head::KVar(kvid) = head {
                res.entry(*kvid).or_default().push(clause_id);
            }
        }
        res
    }

    /// Computes the set of all kvars that can be assigned to Bot (False),
    /// because they are not (transitively) reachable from any concrete ASSUMPTION.
    fn bot_kvars(self) -> Assignment {
        // set of BOT kvars (initially, all)
        let mut assignment = Assignment::new(Label::Bot);

        let kv_lhs = self.kv_lhs();

        // set of BOT kvars in LHS of each constraint with KVar HEAD
        let mut bot_assms: IndexVec<ClauseId, FxHashSet<KVid>> = self.assumptions;

        // set of constraints `cid` whose bot-assms is empty
        let mut candidates: Vec<ClauseId> = bot_assms
            .iter_enumerated()
            .filter_map(|(cid, lhs)| if lhs.is_empty() { Some(cid) } else { None })
            .collect();

        // while there is a candidate constraint, that has NO BOT kvars in lhs
        while let Some(cid) = candidates.pop() {
            if let Head::KVar(kvid) = self.heads[cid] {
                // un-BOT the head kvar
                assignment.remove(kvid);
                // remove the head kvar from all (bot) assumptions where it currently occurs
                for cid in kv_lhs.get(&kvid).unwrap_or(&vec![]) {
                    // if cid HEAD is a kvar
                    if let Head::KVar(rhs_kvid) = self.heads[*cid] {
                        let assms = &mut bot_assms[*cid];
                        assms.remove(&kvid);
                        if assignment.has_label(rhs_kvid) && assms.is_empty() {
                            candidates.push(*cid);
                        }
                    };
                }
            }
        }

        assignment
    }

    /// Computes the set of all kvars that can be assigned to Top (True),
    /// because they do not (transitively) reach any concrete HEAD.
    fn top_kvars(self) -> Assignment {
        // initialize
        let mut assignment = Assignment::new(Label::Top);

        let kv_rhs = self.kv_rhs();

        // set of kvar {k | cid in graph.edges, c.rhs is concrete, k in c.lhs }
        let mut candidates = vec![];
        for (cid, head) in self.heads.iter_enumerated() {
            if matches!(head, Head::Conc) {
                for kvid in &self.assumptions[cid] {
                    candidates.push(*kvid);
                }
            }
        }

        // set each kvar that transitively reaches a concrete HEAD to NON-BOT
        while let Some(kvid) = candidates.pop() {
            // set that kvar to non-top
            assignment.remove(kvid);

            // for each constraint where kvid appears as head
            for cid in kv_rhs.get(&kvid).unwrap_or(&vec![]) {
                // add kvars in lhs to candidates (if they have not already been solved to non-BOT)
                for lhs_kvid in &self.assumptions[*cid] {
                    if assignment.has_label(*lhs_kvid) {
                        candidates.push(*lhs_kvid);
                    }
                }
            }
        }

        assignment
    }
}

newtype_index! {
    struct ClauseId {}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Head {
    /// KVar
    KVar(KVid),
    /// A *conc*rete predicate, i.e., an [`Expr`] that's not a kvar. We don't need to know
    /// the exact expression, only that it's concrete.
    Conc,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Label {
    /// Kvar can be solved to false
    Bot,
    /// Kvar can be solved to true
    Top,
}

struct Assignment {
    /// These vars are NOT assigned `label`,
    /// all other `KVid` implicitly have assignment `label`
    vars: FxHashSet<KVid>,
    label: Label,
}

impl Assignment {
    fn new(label: Label) -> Self {
        let vars = FxHashSet::default();
        Self { vars, label }
    }

    fn has_label(&self, kvid: KVid) -> bool {
        !self.vars.contains(&kvid)
    }

    fn remove(&mut self, kvid: KVid) {
        self.vars.insert(kvid);
    }

    /// simplifies the given predicate expression by replacing
    /// kvid assigned to TOP with True, BOT with false.
    fn simplify(&self, pred: &Expr) -> Expr {
        let mut preds = vec![];
        for p in pred.flatten_conjs() {
            if let ExprKind::KVar(kvar) = p.kind()
                && self.has_label(kvar.kvid)
            {
                if self.label == Label::Bot {
                    return Expr::ff();
                } // else, skip pushing `p` into `preds`
            } else {
                preds.push(p.clone());
            }
        }
        Expr::and_from_iter(preds)
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct BinderProvenance {
    /// Whence?
    pub span: Option<Span>,
    /// Why?
    pub originator: BinderOriginator,
}

impl BinderProvenance {
    pub fn new(originator: BinderOriginator) -> Self {
        BinderProvenance { span: None, originator }
    }

    pub fn with_span(self, span: Span) -> Self {
        BinderProvenance { span: Some(span), originator: self.originator }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum BinderOriginator {
    /// Subtyping check
    Sub(ConstrReason),
    /// Function subtyping check
    FnSub,
    /// Function call
    Call,
    /// The return of a function call
    CallReturn,
    /// Argument from the definition of a function
    FnArg(Option<Symbol>),
    /// Unfold a local pointer
    UnfoldPtr,
    /// Unfold a strong ref
    UnfoldStrgRef,
    /// Assume an ensures
    AssumeEnsures,
    /// Check an invariant
    CheckInvariant,
    /// For use applying the mut ref hack
    MutRefHack,
    /// Subtyping projection types
    /// (NOTE: not differentiating between generic arg tys)
    SubProjTy,
}
