use std::{cell::RefCell, iter, ops::ControlFlow, rc::Rc};

use flux_common::tracked_span_bug;
use flux_middle::{
    fhir::WeakKind,
    global_env::GlobalEnv,
    rty::{
        box_args,
        fold::{FallibleTypeFolder, TypeFoldable, TypeVisitable, TypeVisitor},
        AdtDef, BaseTy, Binder, EarlyBinder, Expr, GenericArg, Index, Layout, LayoutKind, Loc,
        Path, PtrKind, Ref, Sort, Substs, Ty, TyKind, Var, VariantIdx, VariantSig,
    },
    rustc::mir::{FieldIdx, Place, PlaceElem},
};
use itertools::Itertools;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;

use super::projection::{lookup, unfold};
use crate::{
    checker::errors::CheckerErrKind,
    constraint_gen::ConstrGen,
    refine_tree::{RefineCtxt, Scope, UnpackFlags},
    CheckerConfig,
};

#[derive(Default, Eq, PartialEq, Clone)]
pub(super) struct PlacesTree {
    map: LocMap,
}

type LocMap = FxHashMap<Loc, Root>;

#[derive(Eq, PartialEq)]
struct Root {
    kind: LocKind,
    ptr: NodePtr,
}

#[derive(Clone, Eq, PartialEq)]
pub(super) enum LocKind {
    Local,
    Box(Ty),
    Universal,
}

impl Clone for Root {
    fn clone(&self) -> Root {
        Root { kind: self.kind.clone(), ptr: self.ptr.deep_clone() }
    }
}

pub(super) struct LookupResult<'a> {
    tree: &'a mut PlacesTree,
    kind: LookupKind,
}

pub(super) trait LookupKey {
    type Iter<'a>: Iterator<Item = PlaceElem> + 'a
    where
        Self: 'a;

    fn loc(&self) -> Loc;

    fn proj(&self) -> Self::Iter<'_>;
}

impl LookupKey for Place {
    type Iter<'a> = impl Iterator<Item = PlaceElem> + 'a;

    fn loc(&self) -> Loc {
        Loc::Local(self.local)
    }

    fn proj(&self) -> Self::Iter<'_> {
        self.projection.iter().copied()
    }
}

impl LookupKey for Path {
    type Iter<'a> = impl Iterator<Item = PlaceElem> + 'a;

    fn loc(&self) -> Loc {
        self.loc.clone()
    }

    fn proj(&self) -> Self::Iter<'_> {
        self.projection().iter().map(|f| PlaceElem::Field(*f))
    }
}

enum LookupKind {
    Strg(Path, NodePtr),
    Weak(WeakKind, Ty),
    Raw(Ty),
}

pub(super) enum FoldResult {
    Strg(Path, Ty),
    Weak(WeakKind, Ty),
    Raw(Ty),
}

impl FoldResult {
    pub(super) fn ty(&self) -> Ty {
        match self {
            FoldResult::Strg(_, ty) | FoldResult::Weak(_, ty) | FoldResult::Raw(ty) => ty.clone(),
        }
    }
}

impl Root {
    fn new(node: Node, kind: LocKind) -> Root {
        Root { kind, ptr: node.into_ptr() }
    }
}

impl PlacesTree {
    pub(super) fn get(&self, path: &Path) -> Binding {
        let ptr = self.get_node(path);
        let node = ptr.borrow();
        match &*node {
            Node::Leaf(binding) => binding.clone(),
            Node::Internal(..) => tracked_span_bug!("expected `Node::Leaf`, got {node:?}"),
        }
    }

    fn get_node(&self, path: &Path) -> NodePtr {
        let mut ptr = NodePtr::clone(
            &self
                .map
                .get(&path.loc)
                .unwrap_or_else(|| tracked_span_bug!("key not found `{:?}`", path.loc))
                .ptr,
        );
        for f in path.projection() {
            ptr = {
                let node = ptr.borrow();
                match &*node {
                    Node::Leaf(_) => tracked_span_bug!("expected `Node::Internal`"),
                    Node::Internal(.., children) => NodePtr::clone(&children[f.as_usize()]),
                }
            };
        }
        ptr
    }

    pub fn update_binding(&mut self, path: &Path, binding: Binding) {
        *self.get_node(path).borrow_mut() = Node::Leaf(binding);
    }

    pub fn update(&mut self, path: &Path, new_ty: Ty) {
        *self.get_node(path).borrow_mut().expect_owned_mut() = new_ty;
    }

    pub(super) fn insert(&mut self, loc: Loc, ty: Ty, kind: LocKind) {
        self.map.insert(loc, Root::new(Node::owned(ty), kind));
    }

    pub(super) fn contains_loc(&self, loc: Loc) -> bool {
        self.map.contains_key(&loc)
    }

    pub(super) fn iter(&self, mut f: impl FnMut(&LocKind, Path, &Binding)) {
        fn go(
            ptr: &NodePtr,
            loc: &Loc,
            kind: &LocKind,
            proj: &mut Vec<FieldIdx>,
            f: &mut impl FnMut(&LocKind, Path, &Binding),
        ) {
            let node = ptr.borrow();
            match &*node {
                Node::Leaf(binding) => {
                    f(kind, Path::new(loc.clone(), proj.as_slice()), binding);
                }
                Node::Internal(_, children) => {
                    for (idx, ptr) in children.iter().enumerate() {
                        proj.push(FieldIdx::from(idx));
                        go(ptr, loc, kind, proj, f);
                        proj.pop();
                    }
                }
            }
        }
        let mut proj = vec![];
        for (loc, root) in &self.map {
            go(&root.ptr, loc, &root.kind, &mut proj, &mut f);
        }
    }

    pub(super) fn paths(&self) -> Vec<Path> {
        let mut paths = vec![];
        self.iter(|_, path, _| paths.push(path));
        paths
    }

    pub(super) fn flatten(&self) -> Vec<(LocKind, Path, Binding)> {
        let mut bindings = vec![];
        self.iter(|kind, path, binding| bindings.push((kind.clone(), path, binding.clone())));
        bindings
    }

    pub(super) fn lookup(
        &mut self,
        genv: &GlobalEnv,
        rcx: &mut RefineCtxt,
        key: &impl LookupKey,
        checker_conf: CheckerConfig,
    ) -> Result<LookupResult, CheckerErrKind> {
        let mut path = Path::from(key.loc());
        let place_proj = &mut key.proj();
        'outer: loop {
            let loc = path.loc.clone();
            let mut ptr = self.get_loc(&loc);
            let mut path_proj = vec![];

            for f in path.projection() {
                let next = NodePtr::clone(&ptr.borrow().expect_internal()[f.as_usize()]);
                ptr = next;
                path_proj.push(*f);
            }

            for elem in place_proj.by_ref() {
                match elem {
                    PlaceElem::Deref => {
                        let ty = ptr.borrow().expect_owned();
                        match ty.kind() {
                            TyKind::Ptr(_, ptr_path) => {
                                path = ptr_path.clone();
                                continue 'outer;
                            }
                            Ref!(_, ty, mutbl) => {
                                let ty = lookup(place_proj, ty)?;
                                return Ok(LookupResult {
                                    tree: self,
                                    kind: LookupKind::Weak(WeakKind::from(*mutbl), ty),
                                });
                            }
                            TyKind::Indexed(BaseTy::RawPtr(ty, _), _) => {
                                assert!(place_proj.next().is_none());
                                return Ok(LookupResult {
                                    tree: self,
                                    kind: LookupKind::Raw(ty.clone()),
                                });
                            }
                            _ => {
                                todo!("{ty:?}")
                            }
                        }
                    }
                    PlaceElem::Field(f) => {
                        let next = NodePtr::clone(&ptr.borrow().expect_internal()[f.as_usize()]);
                        ptr = next;
                        path_proj.push(f);
                    }
                    PlaceElem::Downcast(_, _) => {}
                    PlaceElem::Index(_) => {
                        let ty = ptr.borrow().expect_owned();
                        match ty.kind() {
                            TyKind::Indexed(BaseTy::Array(arr_ty, _), _) => {
                                let arr_ty = lookup(place_proj, arr_ty)?;
                                return Ok(LookupResult {
                                    tree: self,
                                    kind: LookupKind::Weak(WeakKind::Arr, arr_ty),
                                });
                            }
                            _ => tracked_span_bug!("unsupported index: {elem:?} {ty:?}"),
                        }
                    }
                }
            }

            return Ok(LookupResult {
                tree: self,
                kind: LookupKind::Strg(Path::new(loc, path_proj), ptr),
            });
        }
    }

    pub(super) fn unfold<'a>(
        &'a mut self,
        genv: &GlobalEnv,
        rcx: &mut RefineCtxt,
        key: &impl LookupKey,
        checker_config: CheckerConfig,
    ) -> Result<LookupResult<'a>, CheckerErrKind> {
        let mut path = Path::from(key.loc());
        let place_proj = &mut key.proj();

        'outer: loop {
            let loc = path.loc.clone();
            let mut path_proj = vec![];

            let mut ptr = self.get_loc(&loc);

            for field in path.projection() {
                ptr = ptr.proj(genv, rcx, *field, checker_config)?;
                path_proj.push(*field);
            }

            for elem in place_proj.by_ref() {
                match elem {
                    PlaceElem::Field(field) => {
                        path_proj.push(field);
                        ptr = ptr.proj(genv, rcx, field, checker_config)?;
                    }
                    PlaceElem::Downcast(_, variant_idx) => {
                        ptr.downcast(genv, rcx, variant_idx, checker_config)?;
                    }
                    PlaceElem::Deref => {
                        let ty = ptr.borrow().expect_owned();
                        let kind = match ty.kind() {
                            TyKind::Ptr(_, ptr_path) => {
                                path = ptr_path.clone();
                                continue 'outer;
                            }
                            TyKind::Indexed(BaseTy::Adt(adt, _), _) if adt.is_box() => {
                                let loc = ptr.borrow_mut().unfold_box(rcx, self);
                                path = Path::from(loc);
                                continue 'outer;
                            }
                            Ref!(re, deref_ty, mutbl) => {
                                let deref_ty =
                                    unfold(genv, rcx, place_proj, deref_ty, checker_config)?;
                                let ty = Ty::mk_ref(*re, deref_ty.clone(), *mutbl);
                                *ptr.borrow_mut() = Node::owned(ty);
                                LookupKind::Weak(WeakKind::from(*mutbl), deref_ty)
                            }
                            TyKind::Indexed(BaseTy::RawPtr(deref_ty, mutbl), idx) => {
                                let ty = Ty::indexed(
                                    BaseTy::RawPtr(deref_ty.clone(), *mutbl),
                                    idx.clone(),
                                );
                                *ptr.borrow_mut() = Node::owned(ty);
                                LookupKind::Raw(deref_ty.clone())
                            }
                            _ => {
                                tracked_span_bug!(
                                    "unsupported deref: elem = {elem:?}, ty = {ty:?}"
                                );
                            }
                        };
                        return Ok(LookupResult { tree: self, kind });
                    }
                    PlaceElem::Index(_) => {
                        let ty = ptr.borrow().expect_owned();
                        match ty.kind() {
                            TyKind::Indexed(BaseTy::Array(arr_ty, len), idx) => {
                                let arr_ty = unfold(genv, rcx, place_proj, arr_ty, checker_config)?;
                                let ty = Ty::indexed(
                                    BaseTy::Array(arr_ty.clone(), len.clone()),
                                    idx.clone(),
                                );
                                *ptr.borrow_mut() = Node::owned(ty);
                                return Ok(LookupResult {
                                    tree: self,
                                    kind: LookupKind::Weak(WeakKind::Arr, arr_ty),
                                });
                            }
                            _ => tracked_span_bug!("unsupported index: {elem:?} {ty:?}"),
                        }
                    }
                }
            }

            return Ok(LookupResult {
                tree: self,
                kind: LookupKind::Strg(Path::new(loc, path_proj), ptr),
            });
        }
    }

    pub fn close_boxes(
        &mut self,
        rcx: &mut RefineCtxt,
        gen: &mut ConstrGen,
        scope: &Scope,
    ) -> Result<(), CheckerErrKind> {
        let mut paths = self.paths();
        paths.sort();
        for path in paths.into_iter().rev() {
            let ptr = self.get_node(&path);
            let mut node = ptr.borrow_mut();
            if let Node::Leaf(Binding::Owned(ty)) = &mut *node
                && let TyKind::Ptr(_, path) = ty.kind()
                && let Some(Loc::TupleProj(Var::Free(name), proj)) = path.to_loc()
                && !scope.contains(name)
            {
                debug_assert!(proj.is_empty());
                node.fold(&mut self.map, rcx, gen, false, true)?;
            }
        }
        Ok(())
    }

    fn get_loc(&self, loc: &Loc) -> NodePtr {
        NodePtr::clone(
            &self
                .map
                .get(loc)
                .unwrap_or_else(|| tracked_span_bug!("loc not found `{loc:?}`"))
                .ptr,
        )
    }

    #[must_use]
    pub fn fmap(&self, f: impl FnMut(&Binding) -> Binding) -> PlacesTree {
        let mut tree = self.clone();
        tree.fmap_mut(f);
        tree
    }

    pub fn fmap_mut(&mut self, mut f: impl FnMut(&Binding) -> Binding) {
        for root in self.map.values_mut() {
            root.ptr.borrow_mut().fmap_mut(&mut f);
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct NodePtr(Rc<RefCell<Node>>);

#[derive(Debug, Clone, Eq, PartialEq)]
enum Node {
    Leaf(Binding),
    Internal(NodeKind, Vec<NodePtr>),
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Binding {
    Owned(Ty),
    Blocked(Ty),
}

#[derive(Debug, Clone, Eq, PartialEq)]
enum NodeKind {
    Adt(AdtDef, VariantIdx, Substs),
    Tuple,
    Uninit(Layout),
}

impl LookupResult<'_> {
    pub(super) fn fold(
        self,
        rcx: &mut RefineCtxt,
        gen: &mut ConstrGen,
        close_boxes: bool,
    ) -> Result<FoldResult, CheckerErrKind> {
        match self.kind {
            LookupKind::Strg(path, ptr) => {
                Ok(FoldResult::Strg(
                    path,
                    ptr.fold(&mut self.tree.map, rcx, gen, true, close_boxes)?,
                ))
            }
            LookupKind::Weak(rk, ty) => Ok(FoldResult::Weak(rk, ty)),
            LookupKind::Raw(ty) => Ok(FoldResult::Raw(ty)),
        }
    }

    pub(super) fn unblock(self, rcx: &mut RefineCtxt) -> FoldResult {
        match self.kind {
            LookupKind::Strg(path, ptr) => {
                FoldResult::Strg(path, ptr.borrow_mut().expect_leaf_mut().unblock(rcx))
            }
            LookupKind::Weak(wk, ty) => FoldResult::Weak(wk, ty),
            LookupKind::Raw(ty) => FoldResult::Raw(ty),
        }
    }

    pub(super) fn unfold(
        self,
        genv: &GlobalEnv,
        rcx: &mut RefineCtxt,
        checker_conf: CheckerConfig,
    ) -> Result<(), CheckerErrKind> {
        match self.kind {
            LookupKind::Strg(_, ptr) => ptr.unfold(genv, rcx, checker_conf, self.tree)?,
            LookupKind::Weak(..) | LookupKind::Raw(..) => {}
        }
        Ok(())
    }

    pub(super) fn block(
        self,
        rcx: &mut RefineCtxt,
        gen: &mut ConstrGen,
    ) -> Result<Ty, CheckerErrKind> {
        self.block_with_fn(rcx, gen, Clone::clone)
    }

    pub(super) fn block_with(
        self,
        rcx: &mut RefineCtxt,
        gen: &mut ConstrGen,
        updated: Ty,
    ) -> Result<Ty, CheckerErrKind> {
        self.block_with_fn(rcx, gen, |_| updated)
    }

    fn block_with_fn(
        self,
        rcx: &mut RefineCtxt,
        gen: &mut ConstrGen,
        update: impl FnOnce(&Ty) -> Ty,
    ) -> Result<Ty, CheckerErrKind> {
        match self.kind {
            LookupKind::Strg(_, ptr) => {
                let ty = ptr.fold(&mut self.tree.map, rcx, gen, true, true)?;
                *ptr.borrow_mut() = Node::Leaf(Binding::Blocked(update(&ty)));
                Ok(ty)
            }
            LookupKind::Weak(..) => tracked_span_bug!("blocking weak result"),
            LookupKind::Raw(..) => tracked_span_bug!("blocking raw result"),
        }
    }
}

impl Node {
    fn deep_clone(&self) -> Node {
        match self {
            Node::Leaf(binding) => Node::Leaf(binding.clone()),
            Node::Internal(kind, children) => {
                let children = children.iter().map(NodePtr::deep_clone).collect();
                Node::Internal(kind.clone(), children)
            }
        }
    }

    fn into_ptr(self) -> NodePtr {
        NodePtr(Rc::new(RefCell::new(self)))
    }

    fn owned(ty: Ty) -> Node {
        Node::Leaf(Binding::Owned(ty))
    }

    #[track_caller]
    fn expect_internal(&self) -> &[NodePtr] {
        match self {
            Node::Internal(_, children) => children,
            _ => tracked_span_bug!("expected `Node::Internal`, got `{self:?}`"),
        }
    }

    #[track_caller]
    fn expect_owned(&self) -> Ty {
        match self {
            Node::Leaf(Binding::Owned(ty)) => ty.clone(),
            _ => tracked_span_bug!("expected `Binding::Owned`"),
        }
    }

    #[track_caller]
    fn expect_leaf_mut(&mut self) -> &mut Binding {
        match self {
            Node::Leaf(binding) => binding,
            Node::Internal(_, _) => tracked_span_bug!("expected `Node::Leaf`, got {self:?}"),
        }
    }

    fn expect_owned_mut(&mut self) -> &mut Ty {
        match self {
            Node::Leaf(Binding::Owned(ty)) => ty,
            _ => tracked_span_bug!("expected `Binding::Owned`"),
        }
    }

    fn proj(
        &mut self,
        genv: &GlobalEnv,
        rcx: &mut RefineCtxt,
        field: FieldIdx,
        checker_config: CheckerConfig,
    ) -> Result<&NodePtr, CheckerErrKind> {
        if let Node::Leaf(_) = self {
            self.split(genv, rcx, checker_config)?;
        }
        match self {
            Node::Internal(_, children) => Ok(&children[field.as_usize()]),
            Node::Leaf(..) => unreachable!(),
        }
    }

    fn downcast(
        &mut self,
        genv: &GlobalEnv,
        rcx: &mut RefineCtxt,
        variant_idx: VariantIdx,
        checker_config: CheckerConfig,
    ) -> Result<(), CheckerErrKind> {
        match self {
            Node::Leaf(Binding::Owned(ty)) => {
                match ty.kind() {
                    TyKind::Indexed(BaseTy::Adt(adt_def, substs), idx) => {
                        let fields = downcast(genv, rcx, adt_def, substs, variant_idx, idx)?
                            .into_iter()
                            .map(|ty| {
                                let ty = rcx.unpack(&ty);
                                rcx.assume_invariants(&ty, checker_config.check_overflow);
                                Node::owned(ty).into_ptr()
                            })
                            .collect();
                        *self = Node::Internal(
                            NodeKind::Adt(adt_def.clone(), variant_idx, substs.clone()),
                            fields,
                        );
                    }
                    _ => tracked_span_bug!("type cannot be downcasted: `{ty:?}`"),
                }
            }
            Node::Internal(NodeKind::Adt(_, variant_idx2, _), _) => {
                debug_assert_eq!(variant_idx, *variant_idx2);
            }
            Node::Internal(..) => tracked_span_bug!("invalid downcast"),
            Node::Leaf(..) => tracked_span_bug!("blocked"),
        }
        Ok(())
    }

    fn split(
        &mut self,
        genv: &GlobalEnv,
        rcx: &mut RefineCtxt,
        checker_config: CheckerConfig,
    ) -> Result<(), CheckerErrKind> {
        let ty = self.expect_leaf_mut().unblock(rcx);
        match ty.kind() {
            TyKind::Indexed(BaseTy::Tuple(tys), _)
            | TyKind::Indexed(BaseTy::Closure(_, tys), _) => {
                let children = tys
                    .iter()
                    .cloned()
                    .map(|ty| Node::owned(ty).into_ptr())
                    .collect();
                *self = Node::Internal(NodeKind::Tuple, children);
            }
            TyKind::Indexed(BaseTy::Adt(def, ..), ..) if def.is_struct() => {
                self.downcast(genv, rcx, VariantIdx::from_u32(0), checker_config)?;
            }
            TyKind::Uninit(layout) => {
                let children = match layout.kind() {
                    LayoutKind::Adt(def_id) => {
                        struct_variant(genv, *def_id)?
                            .skip_binder()
                            .skip_binder()
                            .fields()
                            .iter()
                            .map(|ty| Node::owned(Ty::uninit(ty.layout())).into_ptr())
                            .collect()
                    }
                    LayoutKind::Tuple(layouts) => {
                        layouts
                            .iter()
                            .map(|layout| Node::owned(Ty::uninit(layout.clone())).into_ptr())
                            .collect()
                    }
                    LayoutKind::Block => {
                        tracked_span_bug!("type cannot be split: `{ty:?}`");
                    }
                };
                *self = Node::Internal(NodeKind::Uninit(layout.clone()), children);
            }
            _ => tracked_span_bug!("type cannot be split: `{ty:?}`"),
        }
        Ok(())
    }

    fn fold(
        &mut self,
        map: &mut LocMap,
        rcx: &mut RefineCtxt,
        gen: &mut ConstrGen,
        unblock: bool,
        close_boxes: bool,
    ) -> Result<Ty, CheckerErrKind> {
        let ty = match self {
            Node::Leaf(Binding::Owned(ty)) => {
                if let TyKind::Ptr(PtrKind::Box, path) = ty.kind() && close_boxes {
                    let loc = path.to_loc().unwrap();
                    let root = map.remove(&loc).unwrap();
                    let LocKind::Box(alloc) = root.kind else {
                        tracked_span_bug!("box pointer to non-box loc");
                    };
                    let boxed_ty = root.ptr.borrow_mut().fold(map, rcx, gen, unblock, close_boxes)?;
                    let ty = gen.genv.mk_box(boxed_ty, alloc);
                    *self = Node::owned(ty.clone());
                    ty
                } else {
                    ty.clone()
                }
            }
            Node::Leaf(Binding::Blocked(ty)) => {
                if unblock {
                    let ty = rcx.unpack(ty);
                    *self = Node::owned(ty.clone());
                    ty
                } else {
                    tracked_span_bug!("I don't know what to do if you don't ask me to unblock.");
                }
            }
            Node::Internal(NodeKind::Tuple, children) => {
                let tys: Vec<Ty> = children
                    .iter_mut()
                    .map(|node| node.fold(map, rcx, gen, unblock, close_boxes))
                    .try_collect()?;
                let partially_moved = tys.iter().any(|ty| ty.is_uninit());
                let ty = if partially_moved {
                    Ty::uninit(Layout::tuple(tys.iter().map(|ty| ty.layout()).collect()))
                } else {
                    Ty::tuple(tys)
                };
                *self = Node::owned(ty.clone());
                ty
            }
            Node::Internal(NodeKind::Adt(adt_def, variant_idx, substs), children) => {
                let variant = gen.genv.variant_sig(adt_def.did(), *variant_idx)?.expect("unexpected opaque struct");
                let fields: Vec<Ty> = children
                    .iter_mut()
                    .map(|node| {
                        let ty = node.fold(map, rcx, gen, unblock, close_boxes)?;
                        Ok::<_, CheckerErrKind>(rcx.unpack(&ty))
                    })
                    .try_collect()?;

                let partially_moved = fields.iter().any(|ty| ty.is_uninit());
                let ty = if partially_moved {
                    Ty::uninit(Layout::adt(adt_def.did()))
                } else {
                    gen.check_constructor(rcx, variant, substs, &fields)
                        .unwrap_or_else(|err| tracked_span_bug!("{err:?}"))
                };
                *self = Node::owned(ty.clone());
                ty
            }
            Node::Internal(NodeKind::Uninit(layout), _) => {
                let ty = Ty::uninit(layout.clone());
                *self = Node::owned(ty.clone());
                ty
            }
        };
        Ok(ty)
    }

    fn unfold(
        &mut self,
        genv: &GlobalEnv,
        rcx: &mut RefineCtxt,
        checker_conf: CheckerConfig,
        map: &mut PlacesTree,
    ) -> Result<(), CheckerErrKind> {
        match self {
            Node::Leaf(Binding::Blocked(ty) | Binding::Owned(ty)) => {
                if ty.is_box() {
                    self.unfold_box(rcx, map);
                } else if ty.is_tuple() | ty.is_closure() | ty.is_struct() | ty.is_uninit() {
                    self.split(genv, rcx, checker_conf)?;
                }

                Ok(())
            }
            Node::Internal(_, _) => Ok(()),
        }
    }

    fn unfold_box(&mut self, rcx: &mut RefineCtxt, map: &mut PlacesTree) -> Loc {
        let ty = self.expect_owned();
        match ty.kind() {
            TyKind::Indexed(BaseTy::Adt(adt, substs), _) => {
                debug_assert!(adt.is_box());
                let (boxed, alloc) = box_args(substs);
                let fresh = rcx.define_var(&Sort::Loc);
                let loc = Loc::from(fresh);
                *self = Node::owned(Ty::ptr(PtrKind::Box, loc.clone()));
                map.insert(loc.clone(), boxed.clone(), LocKind::Box(alloc.clone()));
                loc
            }
            _ => {
                tracked_span_bug!()
            }
        }
    }

    fn fmap_mut(&mut self, f: &mut impl FnMut(&Binding) -> Binding) {
        match self {
            Node::Leaf(binding) => *binding = f(binding),
            Node::Internal(.., fields) => {
                for field in fields {
                    field.borrow_mut().fmap_mut(f);
                }
            }
        }
    }
}

impl std::ops::Deref for NodePtr {
    type Target = RefCell<Node>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl NodePtr {
    fn deep_clone(&self) -> NodePtr {
        self.borrow().deep_clone().into_ptr()
    }

    fn fold(
        &self,
        map: &mut LocMap,
        rcx: &mut RefineCtxt,
        gen: &mut ConstrGen,
        unblock: bool,
        close_boxes: bool,
    ) -> Result<Ty, CheckerErrKind> {
        self.borrow_mut().fold(map, rcx, gen, unblock, close_boxes)
    }

    fn unfold(
        &self,
        genv: &GlobalEnv,
        rcx: &mut RefineCtxt,
        checker_conf: CheckerConfig,
        map: &mut PlacesTree,
    ) -> Result<(), CheckerErrKind> {
        self.borrow_mut().unfold(genv, rcx, checker_conf, map)
    }

    fn proj(
        &self,
        genv: &GlobalEnv,
        rcx: &mut RefineCtxt,
        field: FieldIdx,
        checker_config: CheckerConfig,
    ) -> Result<NodePtr, CheckerErrKind> {
        Ok(NodePtr::clone(self.borrow_mut().proj(genv, rcx, field, checker_config)?))
    }

    fn downcast(
        &self,
        genv: &GlobalEnv,
        rcx: &mut RefineCtxt,
        variant_idx: VariantIdx,
        checker_config: CheckerConfig,
    ) -> Result<(), CheckerErrKind> {
        self.borrow_mut()
            .downcast(genv, rcx, variant_idx, checker_config)
    }
}

impl Binding {
    #[track_caller]
    pub fn expect_owned(&self) -> Ty {
        match self {
            Binding::Owned(ty) => ty.clone(),
            Binding::Blocked(_) => tracked_span_bug!("expected `Binding::Owned`"),
        }
    }

    pub fn ty(&self) -> &Ty {
        match self {
            Binding::Owned(ty) | Binding::Blocked(ty) => ty,
        }
    }

    fn is_uninit(&self) -> bool {
        match self {
            Binding::Owned(ty) | Binding::Blocked(ty) => ty.is_uninit(),
        }
    }

    pub(crate) fn unblock(&mut self, rcx: &mut RefineCtxt) -> Ty {
        match self {
            Binding::Owned(ty) => ty.clone(),
            Binding::Blocked(ty) => {
                let ty = rcx.unpack(ty);
                *self = Binding::Owned(ty.clone());
                ty
            }
        }
    }
}

impl TypeVisitable for Binding {
    fn visit_with<V: TypeVisitor>(&self, visitor: &mut V) -> ControlFlow<V::BreakTy, ()> {
        match self {
            Binding::Owned(ty) | Binding::Blocked(ty) => ty.visit_with(visitor),
        }
    }
}

impl TypeFoldable for Binding {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        let binding = match self {
            Binding::Owned(ty) => Binding::Owned(ty.try_fold_with(folder)?),
            Binding::Blocked(ty) => Binding::Blocked(ty.try_fold_with(folder)?),
        };
        Ok(binding)
    }
}

pub(crate) fn downcast(
    genv: &GlobalEnv,
    rcx: &mut RefineCtxt,
    adt: &AdtDef,
    substs: &[GenericArg],
    variant_idx: VariantIdx,
    idx: &Index,
) -> Result<Vec<Ty>, CheckerErrKind> {
    if adt.is_struct() {
        debug_assert_eq!(variant_idx.as_u32(), 0);
        downcast_struct(genv, adt, substs, idx)
    } else if adt.is_enum() {
        downcast_enum(genv, rcx, adt, variant_idx, substs, idx)
    } else {
        tracked_span_bug!("Downcast without struct or enum!")
    }
}

/// `downcast` on struct works as follows
/// Given a struct definition
///     struct S<A..>[(i...)] { fld : T, ...}
/// and a
///     * "place" `x: S<t..>[e..]`
/// the `downcast` returns a vector of `ty` for each `fld` of `x` where
///     * `x.fld : T[A := t ..][i := e...]`
/// i.e. by substituting the type and value indices using the types and values from `x`.
pub(crate) fn downcast_struct(
    genv: &GlobalEnv,
    adt: &AdtDef,
    substs: &[GenericArg],
    idx: &Index,
) -> Result<Vec<Ty>, CheckerErrKind> {
    Ok(struct_variant(genv, adt.did())?
        .subst_generics(substs)
        .replace_bound_exprs(idx.expr.expect_tuple())
        .fields
        .to_vec())
}

fn struct_variant(
    genv: &GlobalEnv,
    def_id: DefId,
) -> Result<EarlyBinder<Binder<VariantSig>>, CheckerErrKind> {
    debug_assert!(genv.adt_def(def_id)?.is_struct());
    genv.variant_sig(def_id, VariantIdx::from_u32(0))?
        .ok_or_else(|| CheckerErrKind::OpaqueStruct(def_id))
}

/// In contrast (w.r.t. `struct`) downcast on `enum` works as follows.
/// Given
///     * a "place" `x : T[i..]`
///     * a "variant" of type `forall z..,(y:t...) => E[j...]`
/// We want `downcast` to return a vector of types _and an assertion_ by
///     1. *Instantiate* the type to fresh names `z'...` to get `(y:t'...) => T[j'...]`
///     2. *Unpack* the fields using `y:t'...`
///     3. *Assert* the constraint `i == j'...`
fn downcast_enum(
    genv: &GlobalEnv,
    rcx: &mut RefineCtxt,
    adt: &AdtDef,
    variant_idx: VariantIdx,
    substs: &[GenericArg],
    idx1: &Index,
) -> Result<Vec<Ty>, CheckerErrKind> {
    let variant_def = genv
        .variant_sig(adt.did(), variant_idx)?
        .expect("enums cannot be opaque")
        .subst_generics(substs)
        .replace_bound_exprs_with(|sort| rcx.define_vars(sort));

    let (.., idx2) = variant_def.ret.expect_adt();
    // FIXME(nilehmann) flatten indices
    let exprs1 = idx1.expr.expect_tuple();
    let exprs2 = idx2.expr.expect_tuple();
    debug_assert_eq!(exprs1.len(), exprs2.len());
    let constr = Expr::and(iter::zip(exprs1, exprs2).filter_map(|(e1, e2)| {
        if !e1.is_abs() && !e2.is_abs() {
            Some(Expr::eq(e1, e2))
        } else {
            None
        }
    }));
    rcx.assume_pred(constr);

    Ok(variant_def.fields.to_vec())
}

mod pretty {
    use std::fmt;

    use flux_middle::pretty::*;
    use itertools::Itertools;
    use rustc_middle::ty::TyCtxt;

    use super::*;

    impl Pretty for PlacesTree {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            let bindings = self
                .flatten()
                .into_iter()
                .filter(|(_, path, ty)| {
                    !path.projection().is_empty() || !cx.hide_uninit || !ty.is_uninit()
                })
                .sorted_by(|(_, path1, _), (_, path2, _)| path1.cmp(path2));
            w!(
                "{{{}}}",
                ^bindings
                    .format_with(", ", |(kind, loc, binding), f| {
                        match binding {
                            Binding::Owned(ty) => {
                                f(&format_args_cx!("{:?}:{:?} {:?}", loc, kind, ty))
                            }
                            Binding::Blocked(ty) => {
                                f(&format_args_cx!("{:?}:†{:?} {:?}", loc, kind, ty))
                            }
                        }
                    })
            )
        }

        fn default_cx(tcx: TyCtxt) -> PPrintCx {
            PPrintCx::default(tcx).kvar_args(KVarArgs::Hide)
        }
    }

    impl Pretty for LocKind {
        fn fmt(&self, _cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                LocKind::Local | LocKind::Universal => Ok(()),
                LocKind::Box(_) => w!("[box]"),
            }
        }
    }

    impl_debug_with_default_cx!(PlacesTree);
}
