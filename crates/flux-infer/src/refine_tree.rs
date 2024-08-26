use std::{
    cell::RefCell,
    ops::ControlFlow,
    rc::{Rc, Weak},
};

use flux_common::{index::IndexVec, iter::IterExt};
use flux_middle::{
    intern::List,
    queries::QueryResult,
    rty::{
        evars::EVarSol,
        fold::{
            TypeFoldable, TypeFolder, TypeSuperFoldable, TypeSuperVisitable, TypeVisitable,
            TypeVisitor,
        },
        BaseTy, Expr, GenericArg, Mutability, Name, Sort, Ty, TyKind, Var,
    },
};
use itertools::Itertools;
use rustc_middle::ty::ParamConst;

use crate::{
    fixpoint_encoding::{fixpoint, FixpointCtxt},
    infer::{Tag, TypeTrace},
};

/// A *refine*ment *tree* tracks the "tree-like structure" of refinement variables and predicates
/// generated during refinement type-checking. This tree can be encoded as a fixpoint constraint
/// whose satisfiability implies the safety of a function.
///
/// We try to hide the representation of the tree as much as possible and only a couple of operations
/// can be used to manipulate the structure of the tree explicitly. Instead, the tree is mostly constructed
/// implicitly via a restricted api provided by [`RefineCtxt`]. Some methods operate on *nodes* of
/// the tree which we try to keep abstract, but it is important to remember that there's an underlying
/// tree.
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

/// A *refine*ment *c*on*t*e*xt* tracks all the refinement parameters and predicates
/// available in a particular path during type-checking. For example, consider the following
/// program:
///
/// ```ignore
/// #[flux::sig(fn(i32[@a0], i32{v : v > a0})) -> i32]
/// fn add(x: i32, y: i32) -> i32 {
///     x + y
/// }
/// ```
///
/// At the beginning of the function, the refinement context will be `{a0: int, a1: int, a1 > a0}`,
/// where `a1` is a freshly generated name for the existential variable in the refinement of `y`.
///
/// More specifically, a [`RefineCtxt`] represents a path from the root to some internal node in a
/// [refinement tree].
///
/// [refinement tree]: RefineTree
pub struct RefineCtxt<'a> {
    tree: &'a mut RefineTree,
    ptr: NodePtr,
}

/// A snapshot of a [`RefineCtxt`] at a particular point during type-checking. Alternatively, a
/// snapshot correponds to a reference to a node in a [refinement tree]. Snapshots may become invalid
/// if the underlying node is [`cleared`].
///
/// [`cleared`]: RefineCtxt::clear_children
/// [refinement tree]: RefineTree
pub struct Snapshot {
    ptr: WeakNodePtr,
}

impl Snapshot {
    /// Returns the [`scope`] at the snapshot if it is still valid or [`None`] otherwise.
    ///
    /// [`scope`]: Scope
    pub fn scope(&self) -> Option<Scope> {
        let parents = ParentsIter::new(self.ptr.upgrade()?);
        let bindings = parents
            .filter_map(|node| {
                let node = node.borrow();
                if let NodeKind::ForAll(_, sort) = &node.kind {
                    Some(sort.clone())
                } else {
                    None
                }
            })
            .collect_vec()
            .into_iter()
            .rev()
            .collect();
        let mut reftgenerics = vec![];
        let parents = ParentsIter::new(self.ptr.upgrade()?);
        for node in parents {
            if let NodeKind::Root(consts) = &node.borrow().kind {
                for (param_const, sort) in consts {
                    reftgenerics.push((*param_const, sort.clone()));
                }
            }
        }
        Some(Scope { bindings, reftgenerics: List::from_vec(reftgenerics) })
    }
}

/// A list of refinement variables and their sorts.
#[derive(PartialEq, Eq)]
pub struct Scope {
    bindings: IndexVec<Name, Sort>,
    reftgenerics: List<(ParamConst, Sort)>,
}

impl Scope {
    pub fn iter(&self) -> impl Iterator<Item = (Var, Sort)> + '_ {
        let iter_param_consts = self
            .reftgenerics
            .iter()
            .map(|(param_const, sort)| (Var::ConstGeneric(*param_const), sort.clone()));
        let iter_bindings = self
            .bindings
            .iter_enumerated()
            .map(|(name, sort)| (Var::Free(name), sort.clone()));
        iter_param_consts.chain(iter_bindings)
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
}

struct WeakNodePtr(Weak<RefCell<Node>>);

impl WeakNodePtr {
    fn upgrade(&self) -> Option<NodePtr> {
        Some(NodePtr(self.0.upgrade()?))
    }
}

enum NodeKind {
    Root(List<(ParamConst, Sort)>),
    /// Used for debugging. See [`TypeTrace`]
    Trace(TypeTrace),
    ForAll(Name, Sort),
    Assumption(Expr),
    Head(Expr, Tag),
    True,
}

impl RefineTree {
    pub fn new(const_params: List<(ParamConst, Sort)>) -> RefineTree {
        let root = Node {
            kind: NodeKind::Root(const_params),
            nbindings: 0,
            parent: None,
            children: vec![],
        };
        let root = NodePtr(Rc::new(RefCell::new(root)));
        RefineTree { root }
    }

    pub fn simplify(&mut self) {
        self.root.borrow_mut().simplify();
    }

    pub fn into_fixpoint(self, cx: &mut FixpointCtxt<Tag>) -> QueryResult<fixpoint::Constraint> {
        Ok(self
            .root
            .borrow()
            .to_fixpoint(cx)?
            .unwrap_or(fixpoint::Constraint::TRUE))
    }

    pub fn refine_ctxt_at_root(&mut self) -> RefineCtxt {
        RefineCtxt { ptr: NodePtr(Rc::clone(&self.root)), tree: self }
    }

    pub(crate) fn refine_ctxt_at(&mut self, snapshot: &Snapshot) -> Option<RefineCtxt> {
        Some(RefineCtxt { ptr: snapshot.ptr.upgrade()?, tree: self })
    }
}

impl<'rcx> RefineCtxt<'rcx> {
    #[allow(clippy::unused_self)]
    // We take a mutable reference to the subtree to prove statically that there's only one writer.
    pub(crate) fn clear_children(&mut self, snapshot: &Snapshot) {
        if let Some(ptr) = snapshot.ptr.upgrade() {
            ptr.borrow_mut().children.clear();
        }
    }

    pub(crate) fn change_root(&mut self, snapshot: &Snapshot) -> Option<RefineCtxt> {
        Some(RefineCtxt { ptr: snapshot.ptr.upgrade()?, tree: self.tree })
    }

    pub fn snapshot(&self) -> Snapshot {
        Snapshot { ptr: NodePtr::downgrade(&self.ptr) }
    }

    #[must_use]
    pub fn branch(&mut self) -> RefineCtxt {
        RefineCtxt { tree: self.tree, ptr: NodePtr::clone(&self.ptr) }
    }

    pub fn scope(&self) -> Scope {
        self.snapshot().scope().unwrap()
    }

    #[allow(dead_code)]
    pub(crate) fn push_trace(&mut self, trace: TypeTrace) {
        self.ptr = self.ptr.push_node(NodeKind::Trace(trace));
    }

    /// Defines a fresh refinement variable with the given `sort`. It returns the freshly generated
    /// name for the variable.
    pub fn define_var(&mut self, sort: &Sort) -> Name {
        let fresh = Name::from_usize(self.ptr.next_name_idx());
        self.ptr = self.ptr.push_node(NodeKind::ForAll(fresh, sort.clone()));
        fresh
    }

    /// Given a [`sort`] that may contain aggregate sorts ([tuple] or [adt]), it destructs the sort
    /// recursively, generating multiple fresh variables and returning an "eta-expanded" expression
    /// of fresh variables. This is in contrast to generating a single fresh variable of aggregate
    /// sort.
    ///
    /// For example, given the sort `(int, (bool, int))` it returns `(a0, (a1, a2))` for fresh variables
    /// `a0: int`, `a1: bool`, and `a2: int`.
    ///
    /// [`sort`]: Sort
    /// [tuple]: Sort::Tuple
    /// [adt]: flux_middle::rty::SortCtor::Adt
    pub fn define_vars(&mut self, sort: &Sort) -> Expr {
        Expr::fold_sort(sort, |sort| Expr::fvar(self.define_var(sort)))
    }

    pub fn assume_pred(&mut self, pred: impl Into<Expr>) {
        let pred = pred.into();
        if !pred.is_trivially_true() {
            self.ptr = self.ptr.push_node(NodeKind::Assumption(pred));
        }
    }

    pub fn check_pred(&mut self, pred: impl Into<Expr>, tag: Tag) {
        let pred = pred.into();
        if !pred.is_trivially_true() {
            self.ptr.push_node(NodeKind::Head(pred, tag));
        }
    }

    pub(crate) fn check_impl(&mut self, pred1: impl Into<Expr>, pred2: impl Into<Expr>, tag: Tag) {
        self.ptr
            .push_node(NodeKind::Assumption(pred1.into()))
            .push_node(NodeKind::Head(pred2.into(), tag));
    }

    pub fn unpack(&mut self, ty: &Ty) -> Ty {
        self.unpacker().unpack(ty)
    }

    pub fn unpacker(&mut self) -> Unpacker<'_, 'rcx> {
        Unpacker::new(self)
    }

    pub fn assume_invariants(&mut self, ty: &Ty, overflow_checking: bool) {
        struct Visitor<'a, 'rcx> {
            rcx: &'a mut RefineCtxt<'rcx>,
            overflow_checking: bool,
        }
        impl TypeVisitor for Visitor<'_, '_> {
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
                    for invariant in bty.invariants(self.overflow_checking) {
                        let invariant = invariant.apply(idx);
                        self.rcx.assume_pred(&invariant);
                    }
                }
                ty.super_visit_with(self)
            }
        }
        ty.visit_with(&mut Visitor { rcx: self, overflow_checking });
    }

    pub fn replace_evars(&mut self, evars: &EVarSol) {
        self.ptr.borrow_mut().replace_evars(evars);
    }
}

enum AssumeInvariants {
    Yes { check_overflow: bool },
    No,
}

pub struct Unpacker<'a, 'rcx> {
    rcx: &'a mut RefineCtxt<'rcx>,
    in_mut_ref: bool,
    unpack_inside_mut_ref: bool,
    shallow: bool,
    unpack_exists: bool,
    assume_invariants: AssumeInvariants,
}

impl<'a, 'rcx> Unpacker<'a, 'rcx> {
    fn new(rcx: &'a mut RefineCtxt<'rcx>) -> Self {
        Self {
            rcx,
            in_mut_ref: false,
            unpack_inside_mut_ref: false,
            shallow: false,
            unpack_exists: true,
            assume_invariants: AssumeInvariants::No,
        }
    }

    pub fn assume_invariants(mut self, check_overflow: bool) -> Self {
        self.assume_invariants = AssumeInvariants::Yes { check_overflow };
        self
    }

    pub fn unpack_inside_mut_ref(mut self, unpack_inside_mut_ref: bool) -> Self {
        self.unpack_inside_mut_ref = unpack_inside_mut_ref;
        self
    }

    pub fn shallow(mut self, shallow: bool) -> Self {
        self.shallow = shallow;
        self
    }

    pub fn unpack_exists(mut self, unpack_exists: bool) -> Self {
        self.unpack_exists = unpack_exists;
        self
    }

    pub fn unpack(mut self, ty: &Ty) -> Ty {
        ty.fold_with(&mut self)
    }
}

impl TypeFolder for Unpacker<'_, '_> {
    fn fold_ty(&mut self, ty: &Ty) -> Ty {
        match ty.kind() {
            TyKind::Indexed(bty, idx) => Ty::indexed(bty.fold_with(self), idx.clone()),
            TyKind::Exists(bound_ty) if self.unpack_exists => {
                // HACK(nilehmann) In general we shouldn't unpack through mutable references because
                // that makes referent type too specific. We only have this as a workaround to infer
                // parameters under mutable references and it should be removed once we implement
                // opening of mutable references. See also `ConstrGen::check_fn_call`.
                if !self.in_mut_ref || self.unpack_inside_mut_ref {
                    let bound_ty = bound_ty
                        .replace_bound_refts_with(|sort, _, _| self.rcx.define_vars(sort))
                        .fold_with(self);
                    if let AssumeInvariants::Yes { check_overflow } = self.assume_invariants {
                        self.rcx.assume_invariants(&bound_ty, check_overflow);
                    }
                    bound_ty
                } else {
                    ty.clone()
                }
            }
            TyKind::Constr(pred, ty) => {
                self.rcx.assume_pred(pred.clone());
                ty.fold_with(self)
            }
            TyKind::StrgRef(re, path, ty) => Ty::strg_ref(*re, path.clone(), ty.fold_with(self)),
            TyKind::Downcast(..) if !self.shallow => ty.super_fold_with(self),
            _ => ty.clone(),
        }
    }

    fn fold_bty(&mut self, bty: &BaseTy) -> BaseTy {
        if self.shallow {
            return bty.clone();
        }
        match bty {
            BaseTy::Adt(adt_def, args) if adt_def.is_box() => {
                let (boxed, alloc) = args.box_args();
                let boxed = boxed.fold_with(self);
                BaseTy::adt(
                    adt_def.clone(),
                    vec![GenericArg::Ty(boxed), GenericArg::Ty(alloc.clone())],
                )
            }
            BaseTy::Ref(r, ty, mutbl) => {
                let in_mut_ref = self.in_mut_ref;
                self.in_mut_ref = matches!(mutbl, Mutability::Mut);
                let ty = ty.fold_with(self);
                self.in_mut_ref = in_mut_ref;
                BaseTy::Ref(*r, ty, *mutbl)
            }
            BaseTy::Tuple(_) => bty.super_fold_with(self),
            _ => bty.clone(),
        }
    }
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

impl Node {
    fn simplify(&mut self) {
        for child in &self.children {
            child.borrow_mut().simplify();
        }

        match &mut self.kind {
            NodeKind::Head(pred, tag) => {
                let pred = pred.simplify();
                if pred.is_trivially_true() {
                    self.kind = NodeKind::True;
                } else {
                    self.kind = NodeKind::Head(pred, *tag);
                }
            }
            NodeKind::True => {}
            NodeKind::Assumption(pred) => {
                *pred = pred.simplify();
                self.children
                    .extract_if(|child| {
                        matches!(child.borrow().kind, NodeKind::True)
                            || matches!(&child.borrow().kind, NodeKind::Head(head, _) if head == pred)
                    })
                    .for_each(drop);
            }
            NodeKind::Trace(_) | NodeKind::Root(_) | NodeKind::ForAll(..) => {
                self.children
                    .extract_if(|child| matches!(&child.borrow().kind, NodeKind::True))
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

    fn replace_evars(&mut self, sol: &EVarSol) {
        for child in &self.children {
            child.borrow_mut().replace_evars(sol);
        }
        match &mut self.kind {
            NodeKind::Assumption(pred) => *pred = pred.replace_evars(sol),
            NodeKind::Head(pred, _) => {
                *pred = pred.replace_evars(sol);
            }
            NodeKind::Trace(trace) => {
                trace.replace_evars(sol);
            }
            NodeKind::Root(_) | NodeKind::ForAll(..) | NodeKind::True => {}
        }
    }

    fn to_fixpoint(&self, cx: &mut FixpointCtxt<Tag>) -> QueryResult<Option<fixpoint::Constraint>> {
        let cstr = match &self.kind {
            NodeKind::Trace(_) | NodeKind::ForAll(_, Sort::Loc) => {
                children_to_fixpoint(cx, &self.children)?
            }

            NodeKind::Root(param_const_sorts) => {
                let Some(children) = children_to_fixpoint(cx, &self.children)? else {
                    return Ok(None);
                };
                let mut constr = children;
                for (param_const, sort) in param_const_sorts {
                    constr = fixpoint::Constraint::ForAll(
                        fixpoint::Bind {
                            name: fixpoint::Var::ConstGeneric(*param_const),
                            sort: cx.sort_to_fixpoint(sort),
                            pred: fixpoint::Pred::TRUE,
                        },
                        Box::new(constr),
                    );
                }
                Some(constr)
            }
            NodeKind::ForAll(name, sort) => {
                cx.with_name_map(*name, |cx, fresh| -> QueryResult<_> {
                    let Some(children) = children_to_fixpoint(cx, &self.children)? else {
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
                let (bindings, pred) = cx.assumption_to_fixpoint(pred)?;
                let Some(cstr) = children_to_fixpoint(cx, &self.children)? else {
                    return Ok(None);
                };
                Some(fixpoint::Constraint::ForAll(
                    fixpoint::Bind {
                        name: fixpoint::Var::Underscore,
                        sort: fixpoint::Sort::Int,
                        pred,
                    },
                    Box::new(fixpoint::Constraint::foralls(bindings, cstr)),
                ))
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

    use flux_common::format::PadAdapter;
    use flux_middle::pretty::*;

    use super::*;

    fn bindings_chain(ptr: &NodePtr) -> (Vec<(Name, Sort)>, Vec<NodePtr>) {
        fn go(ptr: &NodePtr, mut bindings: Vec<(Name, Sort)>) -> (Vec<(Name, Sort)>, Vec<NodePtr>) {
            let node = ptr.borrow();
            if let NodeKind::ForAll(name, sort) = &node.kind {
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

    fn flatten_conjs(nodes: &[NodePtr]) -> Vec<NodePtr> {
        fn go(ptr: &NodePtr, children: &mut Vec<NodePtr>) {
            let node = ptr.borrow();
            if let NodeKind::Root(ps) = &node.kind
                && ps.is_empty()
            {
                for child in &node.children {
                    go(child, children);
                }
            } else {
                children.push(NodePtr::clone(ptr));
            }
        }
        let mut children = vec![];
        for ptr in nodes {
            go(ptr, &mut children);
        }
        children
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
            define_scoped!(cx, f);
            w!("{:?}", &self.root)
        }
    }

    impl Pretty for NodePtr {
        fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            let node = self.borrow();
            match &node.kind {
                NodeKind::Trace(trace) => {
                    w!("@ {:?}", ^trace)?;
                    w!(PadAdapter::wrap_fmt(f, 2), "\n{:?}", join!("\n", &node.children))
                }
                NodeKind::Root(bindings) => {
                    w!(
                        "∀ {}.",
                        ^bindings
                            .into_iter()
                            .format_with(", ", |(name, sort), f| {
                                f(&format_args_cx!("{:?}: {:?}", ^name, sort))
                            })
                    )?;
                    fmt_children(&node.children, cx, f)
                }
                NodeKind::ForAll(name, sort) => {
                    let (bindings, children) = if cx.bindings_chain {
                        bindings_chain(self)
                    } else {
                        (vec![(*name, sort.clone())], node.children.clone())
                    };

                    w!(
                        "∀ {}.",
                        ^bindings
                            .into_iter()
                            .format_with(", ", |(name, sort), f| {
                                f(&format_args_cx!("{:?}: {:?}", ^name, sort))
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
                    let guard = Expr::and_from_iter(preds).simplify();
                    w!("{:?} =>", parens!(guard, !guard.is_atom()))?;
                    fmt_children(&children, cx, f)
                }
                NodeKind::Head(pred, tag) => {
                    let pred = if cx.simplify_exprs { pred.simplify() } else { pred.clone() };
                    w!("{:?}", parens!(pred, !pred.is_atom()))?;
                    if cx.tags {
                        w!(" ~ {:?}", tag)?;
                    }
                    Ok(())
                }
                NodeKind::True => {
                    w!("true")
                }
            }
        }
    }

    fn fmt_children(
        children: &[NodePtr],
        cx: &PrettyCx,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        let mut f = PadAdapter::wrap_fmt(f, 2);
        define_scoped!(cx, f);
        let children = flatten_conjs(children);
        match &children[..] {
            [] => w!(" true"),
            [n] => {
                if n.borrow().is_head() {
                    w!(" ")?;
                } else {
                    w!("\n")?;
                }
                w!("{:?}", NodePtr::clone(n))
            }
            _ => w!("\n{:?}", join!("\n", children)),
        }
    }

    impl Pretty for RefineCtxt<'_> {
        fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            let parents = ParentsIter::new(NodePtr::clone(&self.ptr)).collect_vec();
            write!(
                f,
                "{{{}}}",
                parents
                    .into_iter()
                    .rev()
                    .filter(|ptr| {
                        let node = ptr.borrow();
                        match &node.kind {
                            NodeKind::ForAll(..) => true,
                            NodeKind::Assumption(e) => !e.simplify().is_trivially_true(),
                            _ => false,
                        }
                    })
                    .format_with(", ", |n, f| {
                        let n = n.borrow();
                        match &n.kind {
                            NodeKind::ForAll(name, sort) => {
                                f(&format_args_cx!("{:?}: {:?}", ^name, sort))
                            }
                            NodeKind::Assumption(pred) => f(&format_args_cx!("{:?}", pred)),
                            _ => unreachable!(),
                        }
                    })
            )
        }
    }

    impl Pretty for Scope {
        fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            write!(
                f,
                "[bindings = {}, reftgenerics = {}]",
                self.bindings
                    .iter_enumerated()
                    .format_with(", ", |(name, sort), f| {
                        f(&format_args_cx!("{:?}: {:?}", ^name, sort))
                    }),
                self.reftgenerics
                    .iter()
                    .format_with(", ", |(param_const, sort), f| {
                        f(&format_args_cx!("{:?}: {:?}", ^param_const, sort))
                    }),
            )
        }
    }

    impl_debug_with_default_cx!(
        RefineTree => "refine_tree",
        RefineCtxt<'_> => "refine_ctxt",
        Scope,
    );
}
