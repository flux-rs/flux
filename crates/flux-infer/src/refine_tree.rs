use std::{
    cell::RefCell,
    ops::ControlFlow,
    rc::{Rc, Weak},
};

use flux_common::{index::IndexVec, iter::IterExt, tracked_span_bug};
use flux_config::OverflowMode;
use flux_macros::DebugAsJson;
use flux_middle::{
    def_id_to_string,
    global_env::GlobalEnv,
    pretty::{PrettyCx, PrettyNested, format_cx},
    queries::QueryResult,
    rty::{
        BaseTy, EVid, Expr, ExprKind, KVid, Name, NameProvenance, PrettyVar, Sort, Ty, TyKind, Var,
        WKVid,
        fold::{TypeFoldable, TypeSuperVisitable, TypeVisitable, TypeVisitor},
    },
};
use itertools::Itertools;
use rustc_data_structures::{
    fx::FxIndexMap,
    snapshot_map::SnapshotMap,
    unord::{UnordMap, UnordSet},
};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_index::newtype_index;
use rustc_middle::ty::TyCtxt;
use serde::Serialize;

use crate::{
    evars::EVarStore,
    fixpoint_encoding::{FixpointCtxt, fixpoint},
    infer::{Tag, TypeTrace},
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

    pub(crate) fn to_fixpoint(
        &self,
        cx: &mut FixpointCtxt<Tag>,
    ) -> QueryResult<fixpoint::Constraint> {
        Ok(self
            .root
            .borrow()
            .to_fixpoint(cx)?
            .unwrap_or(fixpoint::Constraint::TRUE))
    }

    #[allow(dead_code, reason = "used by dormant multi-query encoding")]
    pub(crate) fn root_params(&self) -> Vec<(Var, Sort)> {
        match &self.root.borrow().kind {
            NodeKind::Root(params) => params.clone(),
            // Simplification can turn an unconstrained tree into `true`; it has no variables to
            // install in the encoder scope.
            NodeKind::True => vec![],
            _ => unreachable!("refinement tree root is not a root node"),
        }
    }

    pub(crate) fn wkvars_in_positions(
        &self,
    ) -> (FxHashSet<WKVid>, FxHashSet<WKVid>, FxIndexMap<WKVid, usize>) {
        struct WKVars {
            heads: FxHashSet<WKVid>,
            assumptions: FxHashSet<WKVid>,
            self_args: FxIndexMap<WKVid, usize>,
        }

        fn visit_expr(
            expr: &Expr,
            vars: &mut FxHashSet<WKVid>,
            self_args: &mut FxIndexMap<WKVid, usize>,
        ) {
            struct Visitor<'a> {
                vars: &'a mut FxHashSet<WKVid>,
            }

            impl TypeVisitor for Visitor<'_> {
                fn visit_expr(&mut self, expr: &Expr) -> ControlFlow<!> {
                    if let ExprKind::WKVar(wkvar) = expr.kind() {
                        self.vars.insert(wkvar.wkvid.clone());
                    }
                    expr.super_visit_with(self)
                }
            }

            struct ArgsVisitor<'a> {
                self_args: &'a mut FxIndexMap<WKVid, usize>,
            }
            impl TypeVisitor for ArgsVisitor<'_> {
                fn visit_expr(&mut self, expr: &Expr) -> ControlFlow<!> {
                    if let ExprKind::WKVar(wkvar) = expr.kind()
                        && let Some(previous) =
                            self.self_args.insert(wkvar.wkvid.clone(), wkvar.self_args)
                        && previous != wkvar.self_args
                    {
                        panic!("inconsistent self_args for weak KVar {:?}", wkvar.wkvid);
                    }
                    expr.super_visit_with(self)
                }
            }

            let _ = expr.visit_with(&mut Visitor { vars });
            let _ = expr.visit_with(&mut ArgsVisitor { self_args });
        }

        fn visit(node: &Node, vars: &mut WKVars) {
            match &node.kind {
                NodeKind::Head(expr, _) => visit_expr(expr, &mut vars.heads, &mut vars.self_args),
                NodeKind::Assumption(expr) => {
                    visit_expr(expr, &mut vars.assumptions, &mut vars.self_args);
                }
                _ => {}
            }
            for child in &node.children {
                visit(&child.borrow(), vars);
            }
        }

        let mut vars = WKVars {
            heads: Default::default(),
            assumptions: Default::default(),
            self_args: Default::default(),
        };
        visit(&self.root.borrow(), &mut vars);
        (vars.heads, vars.assumptions, vars.self_args)
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
    pub(crate) fn define_var(&mut self, sort: &Sort, provenance: NameProvenance) -> Name {
        let fresh = Name::from_usize(self.ptr.next_name_idx());
        self.ptr = self
            .ptr
            .push_node(NodeKind::ForAll(fresh, sort.clone(), provenance));
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
    ForAll(Name, Sort, NameProvenance),
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

    fn to_fixpoint(&self, cx: &mut FixpointCtxt<Tag>) -> QueryResult<Option<fixpoint::Constraint>> {
        let cstr = match &self.kind {
            NodeKind::Trace(_) | NodeKind::ForAll(_, Sort::Loc, _) => {
                children_to_fixpoint(cx, &self.children)?
            }

            NodeKind::Root(params) => {
                // declare pretty-vars for params
                for (var, sort) in params {
                    if let Var::EarlyParam(param) = var
                        && !sort.is_loc()
                    {
                        cx.with_early_param(param);
                    }
                }

                let Some(children) = children_to_fixpoint(cx, &self.children)? else {
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
                            preds: vec![],
                        },
                        Box::new(constr),
                    );
                }
                Some(constr)
            }
            NodeKind::ForAll(name, sort, provenance) => {
                cx.with_name_map(*name, *provenance, |cx, fresh| -> QueryResult<_> {
                    let Some(children) = children_to_fixpoint(cx, &self.children)? else {
                        return Ok(None);
                    };
                    Ok(Some(fixpoint::Constraint::ForAll(
                        fixpoint::Bind {
                            name: fixpoint::Var::Local(fresh),
                            sort: cx.sort_to_fixpoint(sort),
                            preds: vec![],
                        },
                        Box::new(children),
                    )))
                })?
            }
            NodeKind::Assumption(pred) => {
                let (mut bindings, preds) = cx.assumption_to_fixpoint(pred)?;
                let Some(cstr) = children_to_fixpoint(cx, &self.children)? else {
                    return Ok(None);
                };
                bindings.push(fixpoint::Bind {
                    name: fixpoint::Var::Underscore,
                    sort: fixpoint::Sort::Int,
                    preds,
                });
                Some(fixpoint::Constraint::foralls(bindings, cstr))
            }
            NodeKind::Head(pred, tag) => {
                Some(cx.head_to_fixpoint(pred, |span| tag.with_dst(span))?)
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
) -> QueryResult<Option<fixpoint::Constraint>> {
    let mut children = children
        .iter()
        .filter_map(|node| node.borrow().to_fixpoint(cx).transpose())
        .try_collect_vec()?;
    let cstr = match children.len() {
        0 => None,
        1 => children.pop(),
        _ => Some(fixpoint::Constraint::conj(children)),
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

    fn bindings_chain(ptr: &NodePtr) -> (Vec<(Name, Sort)>, Vec<NodePtr>) {
        fn go(ptr: &NodePtr, mut bindings: Vec<(Name, Sort)>) -> (Vec<(Name, Sort)>, Vec<NodePtr>) {
            let node = ptr.borrow();
            if let NodeKind::ForAll(name, sort, _) = &node.kind {
                bindings.push((*name, sort.clone()));
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
                NodeKind::ForAll(name, sort, _) => {
                    let (bindings, children) = if cx.bindings_chain {
                        bindings_chain(self)
                    } else {
                        (vec![(*name, sort.clone())], node.children.clone())
                    };

                    w!(cx, f,
                        "∀ {}.",
                        ^bindings
                            .into_iter()
                            .format_with(", ", |(name, sort), f| {
                                f(&format_args_cx!(cx, "{:?}: {:?}", ^name, sort))
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
    pub fn new(cx: &mut PrettyCx, cursor: &Cursor) -> Self {
        let parents = ParentsIter::new(NodePtr::clone(&cursor.ptr)).collect_vec();
        let mut bindings = vec![];
        let mut exprs = vec![];

        parents.into_iter().rev().for_each(|ptr| {
            let node = ptr.borrow();
            match &node.kind {
                NodeKind::ForAll(name, sort, provenance) => {
                    let name = cx
                        .pretty_var_env
                        .set(PrettyVar::Local(*name), provenance.opt_symbol());
                    let sort = format_cx!(cx, "{:?}", sort);
                    let bind = RcxBind { name, sort };
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
                        let name = if let Var::EarlyParam(param) = name {
                            cx.pretty_var_env
                                .set(PrettyVar::Param(*param), Some(param.name))
                        } else {
                            format_cx!(cx, "{:?}", name)
                        };
                        let sort = format_cx!(cx, "{:?}", sort);
                        let bind = RcxBind { name, sort };
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
    fn kv_lhs(&self) -> UnordMap<KVid, Vec<ClauseId>> {
        let mut res: UnordMap<KVid, Vec<ClauseId>> = UnordMap::default();
        for (clause_id, kvids) in self.assumptions.iter_enumerated() {
            for kvid in kvids {
                res.entry(*kvid).or_default().push(clause_id);
            }
        }
        res
    }

    /// set of edges where kvid appears as HEAD
    fn kv_rhs(&self) -> UnordMap<KVid, Vec<ClauseId>> {
        let mut res: UnordMap<KVid, Vec<ClauseId>> = UnordMap::default();
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
    vars: UnordSet<KVid>,
    label: Label,
}

impl Assignment {
    fn new(label: Label) -> Self {
        let vars = UnordSet::new();
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

// ---------------------------------------------------------------------------
// WKVar bot analysis: determines which WKVids would trivially solve to false
// if promoted to KVars. This mirrors the KVar bot_kvars analysis but operates
// on WKVids independently.
// ---------------------------------------------------------------------------

newtype_index! {
    struct WClauseId {}
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum WHead {
    WKVar(WKVid),
    Conc,
}

#[derive(Debug)]
struct WKVarConstraintDeps {
    assumptions: IndexVec<WClauseId, FxHashSet<WKVid>>,
    heads: IndexVec<WClauseId, WHead>,
}

impl WKVarConstraintDeps {
    #[allow(dead_code)]
    fn new(node: &Node) -> Self {
        let mut graph = Self { assumptions: IndexVec::default(), heads: IndexVec::default() };
        graph.build(node, &mut vec![]);
        graph
    }

    fn from_trees(trees: &[&RefineTree]) -> Self {
        let mut graph = Self { assumptions: IndexVec::default(), heads: IndexVec::default() };
        for tree in trees {
            graph.build(&tree.root.borrow(), &mut vec![]);
        }
        graph
    }

    fn insert_clause(&mut self, assumptions: &[WKVid], head: WHead) {
        self.assumptions.push(assumptions.iter().cloned().collect());
        self.heads.push(head);
    }

    fn build(&mut self, node: &Node, assumptions: &mut Vec<WKVid>) {
        let n = assumptions.len();
        match &node.kind {
            NodeKind::Head(expr, _) => {
                expr.visit_conj(|e| {
                    if let ExprKind::WKVar(wkvar) = e.kind() {
                        self.insert_clause(assumptions, WHead::WKVar(wkvar.wkvid.clone()));
                    } else {
                        self.insert_clause(assumptions, WHead::Conc);
                    }
                });
            }
            NodeKind::Assumption(expr) => {
                expr.visit_conj(|e| {
                    if let ExprKind::WKVar(wkvar) = e.kind() {
                        assumptions.push(wkvar.wkvid.clone());
                    }
                });
            }
            _ => {}
        };

        for child in &node.children {
            self.build(&child.borrow(), assumptions);
        }

        assumptions.truncate(n);
    }

    fn wkv_lhs(&self) -> UnordMap<WKVid, Vec<WClauseId>> {
        let mut res: UnordMap<WKVid, Vec<WClauseId>> = UnordMap::default();
        for (clause_id, wkvids) in self.assumptions.iter_enumerated() {
            for wkvid in wkvids {
                res.entry(wkvid.clone()).or_default().push(clause_id);
            }
        }
        res
    }

    /// Computes the set of WKVids that would trivially solve to false (bot) if promoted.
    /// Returns the set of WKVids that are NOT bot (i.e., safe to promote).
    fn promotable_wkvids(self, candidates: &FxHashSet<WKVid>) -> FxHashSet<WKVid> {
        let wkv_lhs = self.wkv_lhs();

        // bot_assms: for each clause, the set of WKVids in its assumptions that are still "bot"
        let mut bot_assms: IndexVec<WClauseId, FxHashSet<WKVid>> = self
            .assumptions
            .iter()
            .map(|assms| {
                assms
                    .iter()
                    .filter(|wkvid| candidates.contains(*wkvid))
                    .cloned()
                    .collect()
            })
            .collect();

        // Track which wkvids are still considered bot (start: all candidates)
        let mut is_bot: FxHashSet<WKVid> = candidates.clone();

        // Seed: clauses with no bot wkvars in assumptions
        let mut worklist: Vec<WClauseId> = bot_assms
            .iter_enumerated()
            .filter_map(|(cid, lhs)| if lhs.is_empty() { Some(cid) } else { None })
            .collect();

        while let Some(cid) = worklist.pop() {
            if let WHead::WKVar(ref wkvid) = self.heads[cid] {
                if !is_bot.remove(wkvid) {
                    continue;
                }
                // Remove this wkvid from all assumption sets where it appears
                for dep_cid in wkv_lhs.get(wkvid).unwrap_or(&vec![]) {
                    if let WHead::WKVar(ref rhs_wkvid) = self.heads[*dep_cid] {
                        let assms = &mut bot_assms[*dep_cid];
                        assms.remove(wkvid);
                        if is_bot.contains(rhs_wkvid) && assms.is_empty() {
                            worklist.push(*dep_cid);
                        }
                    }
                }
            }
        }

        // Return the wkvids that are NOT bot
        candidates.difference(&is_bot).cloned().collect()
    }
}

impl RefineTree {
    /// Given a set of candidate WKVids (those that appear in both head and assumption positions),
    /// returns the subset that are safe to promote to KVars (i.e., would NOT trivially solve to
    /// false).
    pub(crate) fn promotable_wkvids(
        trees: &[&RefineTree],
        candidates: &FxHashSet<WKVid>,
    ) -> FxHashSet<WKVid> {
        let graph = WKVarConstraintDeps::from_trees(trees);
        // graph.print_graph();
        graph.promotable_wkvids(candidates)
    }
}

impl WKVarConstraintDeps {
    /// Debug-prints the WKVar dependency graph as ASCII-art trees, one per
    /// connected component, rooted at nodes with no incoming edges (or, if a
    /// component is a pure cycle with no such root, at an arbitrary node).
    ///
    /// An edge `a -> b` means `a` appears in the assumptions of some clause
    /// whose head is `b` (i.e. `a` flows into `b`). Clauses whose head is a
    /// concrete assertion (`WHead::Conc`) are rendered as edges into a
    /// `(conc)` leaf.
    ///
    /// Cycles are broken for display: if a path revisits a node already on
    /// the current root-to-node path, that node is printed again (so you can
    /// see the edge) but is NOT expanded further from there.
    ///
    /// Toggle this on/off by commenting out the call site.
    #[allow(dead_code)]
    fn print_graph(&self) {
        let wkvid_name = |wkvid: &WKVid| {
            format!("$wk_{}_{}", def_id_to_string(wkvid.parent_fn), wkvid.id.as_u32())
        };

        // Build successors/predecessors over rendered node names.
        // Each `(conc)` sink is tagged with its source so distinct wkvars
        // that both reach a concrete head don't get merged into one node.
        let mut succs: FxHashMap<String, Vec<String>> = FxHashMap::default();
        let mut preds: FxHashMap<String, FxHashSet<String>> = FxHashMap::default();
        let mut all_nodes: FxHashSet<String> = FxHashSet::default();

        for (clause_id, assms) in self.assumptions.iter_enumerated() {
            let head_str = match &self.heads[clause_id] {
                WHead::WKVar(wkvid) => Some(wkvid_name(wkvid)),
                WHead::Conc => None,
            };
            for wkvid in assms {
                let src = wkvid_name(wkvid);
                all_nodes.insert(src.clone());
                let dst = match &head_str {
                    Some(h) => {
                        all_nodes.insert(h.clone());
                        h.clone()
                    }
                    None => format!("(conc) [{src}]"),
                };
                succs.entry(src.clone()).or_default().push(dst.clone());
                preds.entry(dst.clone()).or_default().insert(src.clone());
            }
        }

        // Ensure every node has entries so lookups don't panic.
        let mut universe: FxHashSet<String> = all_nodes.clone();
        for k in succs.keys().chain(preds.keys()) {
            universe.insert(k.clone());
        }
        for n in &universe {
            succs.entry(n.clone()).or_default();
            preds.entry(n.clone()).or_default();
        }
        for edges in succs.values_mut() {
            edges.sort();
            edges.dedup();
        }

        // --- Weakly connected components (undirected BFS) ---
        let mut adj: FxHashMap<String, FxHashSet<String>> = FxHashMap::default();
        for n in &universe {
            adj.entry(n.clone()).or_default();
        }
        for (a, bs) in &succs {
            for b in bs {
                adj.entry(a.clone()).or_default().insert(b.clone());
                adj.entry(b.clone()).or_default().insert(a.clone());
            }
        }

        let mut visited_global: FxHashSet<String> = FxHashSet::default();
        let mut components: Vec<Vec<String>> = vec![];
        let mut sorted_universe: Vec<&String> = universe.iter().collect();
        sorted_universe.sort();

        for start in sorted_universe {
            if visited_global.contains(start) {
                continue;
            }
            let mut comp = vec![];
            let mut stack = vec![start.clone()];
            visited_global.insert(start.clone());
            while let Some(n) = stack.pop() {
                comp.push(n.clone());
                if let Some(neighbors) = adj.get(&n) {
                    for nb in neighbors {
                        if visited_global.insert(nb.clone()) {
                            stack.push(nb.clone());
                        }
                    }
                }
            }
            components.push(comp);
        }

        println!("=== WKVar dependency graph ({} component(s)) ===", components.len());

        for (i, comp) in components.iter().enumerate() {
            let comp_set: FxHashSet<String> = comp.iter().cloned().collect();

            // Roots: nodes with no incoming edges from within this component.
            let mut roots: Vec<String> = comp
                .iter()
                .filter(|n| {
                    preds
                        .get(*n)
                        .map(|p| p.iter().all(|x| !comp_set.contains(x)))
                        .unwrap_or(true)
                })
                .cloned()
                .collect();
            roots.sort();

            // Pure cycle with no root: just pick the smallest node as an
            // arbitrary starting point so we still render something.
            if roots.is_empty()
                && let Some(n) = comp.iter().min().cloned()
            {
                roots.push(n);
            }

            println!(
                "-- component {} ({} node(s)), root(s): {} --",
                i + 1,
                comp.len(),
                roots.join(", ")
            );

            let mut printed_roots: FxHashSet<String> = FxHashSet::default();
            for root in &roots {
                if !printed_roots.insert(root.clone()) {
                    continue;
                }
                let mut path: Vec<String> = vec![];
                Self::render_tree(
                    root,
                    &succs,
                    &comp_set,
                    &mut path,
                    &mut Default::default(),
                    "",
                    true,
                );
            }
        }
        println!("===============================");
    }

    /// Recursively renders `node` and its successors (restricted to `comp_set`)
    /// as an ASCII-art tree, using `prefix`/`is_last` for indentation in the
    /// style of the `tree` command.
    ///
    /// - `path` tracks the current root-to-node path, for cycle detection: if
    ///   `node` is already on `path`, recursion stops (cycle).
    /// - `rendered` tracks every node whose children have already been fully
    ///   expanded anywhere earlier in this root's tree: if `node` was already
    ///   rendered, we print it again (so the edge is visible) but don't
    ///   re-expand its children, to avoid duplicating large shared subtrees.
    fn render_tree(
        node: &str,
        succs: &FxHashMap<String, Vec<String>>,
        comp_set: &FxHashSet<String>,
        path: &mut Vec<String>,
        rendered: &mut FxHashSet<String>,
        prefix: &str,
        is_root: bool,
    ) {
        if is_root {
            println!("{node}");
            rendered.insert(node.to_string());
        }

        if path.iter().any(|p| p == node) {
            return;
        }

        path.push(node.to_string());

        let children: Vec<&String> = succs
            .get(node)
            .map(|v| {
                v.iter()
                    .filter(|c| comp_set.contains(*c) || c.starts_with("(conc)"))
                    .collect()
            })
            .unwrap_or_default();

        for (idx, child) in children.iter().enumerate() {
            let is_last = idx == children.len() - 1;
            let connector = if is_last { "└──▶ " } else { "├──▶ " };

            let is_cycle = path.contains(child);
            let already_rendered = !is_cycle && rendered.contains(*child);

            let child_marker = if is_cycle {
                format!("{child} (↺ cycle)")
            } else if already_rendered {
                format!("{child} (see above)")
            } else {
                (*child).clone()
            };
            println!("{prefix}{connector}{child_marker}");

            if !is_cycle && !already_rendered {
                rendered.insert((*child).clone());
                let child_prefix = format!("{prefix}{}", if is_last { "     " } else { "│    " });
                Self::render_tree(child, succs, comp_set, path, rendered, &child_prefix, false);
            }
        }

        path.pop();
    }
}
