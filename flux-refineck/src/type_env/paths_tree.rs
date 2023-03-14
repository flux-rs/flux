use std::{cell::RefCell, iter, rc::Rc};

use flux_common::tracked_span_bug;
use flux_middle::{
    fhir::WeakKind,
    global_env::GlobalEnv,
    rty::{
        box_args,
        fold::{TypeFoldable, TypeFolder, TypeVisitor},
        AdtDef, BaseTy, Expr, GenericArg, Index, Loc, Path, PtrKind, Ref, Sort, Substs, Ty, TyKind,
        Var, VariantIdx,
    },
    rustc::mir::{Field, Place, PlaceElem},
};
use itertools::Itertools;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;

use crate::{
    checker::errors::CheckerErrKind,
    constraint_gen::ConstrGen,
    refine_tree::{RefineCtxt, Scope, UnpackFlags},
};

#[derive(Default, Eq, PartialEq, Clone)]
pub(super) struct PathsTree {
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
    tree: &'a mut PathsTree,
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

impl PathsTree {
    pub(super) fn get(&self, path: &Path) -> Binding {
        let ptr = self.get_node(path);
        let node = ptr.borrow();
        match &*node {
            Node::Leaf(binding) => binding.clone(),
            Node::Internal(..) => tracked_span_bug!("expected `Node::Leaf`"),
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
            proj: &mut Vec<Field>,
            f: &mut impl FnMut(&LocKind, Path, &Binding),
        ) {
            let node = ptr.borrow();
            match &*node {
                Node::Leaf(binding) => {
                    f(kind, Path::new(loc.clone(), proj.as_slice()), binding);
                }
                Node::Internal(_, children) => {
                    for (idx, ptr) in children.iter().enumerate() {
                        proj.push(Field::from(idx));
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

    pub(super) fn join_with(
        &mut self,
        rcx: &mut RefineCtxt,
        gen: &mut ConstrGen,
        other: &mut PathsTree,
    ) -> Result<(), CheckerErrKind> {
        for (loc, root1) in &self.map {
            let node2 = &mut *other.map[loc].ptr.borrow_mut();
            root1.ptr.borrow_mut().join_with(gen, rcx, node2)?;
        }
        Ok(())
    }

    pub(super) fn lookup<'a>(
        &'a mut self,
        genv: &GlobalEnv,
        rcx: &mut RefineCtxt,
        key: &impl LookupKey,
    ) -> Result<LookupResult<'a>, CheckerErrKind> {
        let mut path = Path::from(key.loc());
        let place_proj = &mut key.proj();

        'outer: loop {
            let loc = path.loc.clone();
            let mut path_proj = vec![];

            let mut ptr = NodePtr::clone(
                &self
                    .map
                    .get(&loc)
                    .unwrap_or_else(|| tracked_span_bug!("PANIC: {loc:?}"))
                    .ptr,
            );

            for field in path.projection() {
                ptr = ptr.proj(genv, rcx, *field)?;
                path_proj.push(*field);
            }

            for elem in place_proj.by_ref() {
                match elem {
                    PlaceElem::Field(field) => {
                        path_proj.push(field);
                        ptr = ptr.proj(genv, rcx, field)?;
                    }
                    PlaceElem::Downcast(variant_idx) => {
                        ptr.downcast(genv, rcx, variant_idx)?;
                    }
                    PlaceElem::Deref => {
                        let ty = ptr.borrow().expect_owned();
                        match ty.kind() {
                            TyKind::Ptr(_, ptr_path) => {
                                path = ptr_path.clone();
                                continue 'outer;
                            }
                            Ref!(rk, ty) => {
                                let (rk, ty) = Self::lookup_ty(
                                    genv,
                                    rcx,
                                    WeakKind::from(*rk),
                                    ty,
                                    place_proj,
                                )?;
                                return Ok(LookupResult {
                                    tree: self,
                                    kind: LookupKind::Weak(rk, ty),
                                });
                            }
                            TyKind::Indexed(BaseTy::Adt(adt, substs), _) if adt.is_box() => {
                                let (boxed, alloc) = box_args(substs);
                                let fresh = rcx.define_var(&Sort::Loc);
                                let loc = Loc::from(fresh);
                                *ptr.borrow_mut() = Node::owned(Ty::ptr(PtrKind::Box, loc.clone()));
                                self.insert(
                                    loc.clone(),
                                    boxed.clone(),
                                    LocKind::Box(alloc.clone()),
                                );
                                path = Path::from(loc);
                                continue 'outer;
                            }
                            TyKind::Indexed(BaseTy::RawPtr(ty, _), _) => {
                                return Ok(LookupResult {
                                    tree: self,
                                    kind: LookupKind::Raw(ty.clone()),
                                });
                            }
                            _ => {
                                tracked_span_bug!(
                                    "unsupported deref: elem = {elem:?}, ty = {ty:?}"
                                );
                            }
                        }
                    }
                    PlaceElem::Index(_) => {
                        let ty = ptr.borrow().expect_owned();
                        match ty.kind() {
                            TyKind::Indexed(BaseTy::Array(arr_ty, _), _) => {
                                let (rk, ty) =
                                    Self::lookup_ty(genv, rcx, WeakKind::Arr, arr_ty, place_proj)?;
                                return Ok(LookupResult {
                                    tree: self,
                                    kind: LookupKind::Weak(rk, ty),
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

    fn lookup_ty(
        genv: &GlobalEnv,
        rcx: &mut RefineCtxt,
        mut rk: WeakKind,
        ty: &Ty,
        proj: &mut impl Iterator<Item = PlaceElem>,
    ) -> Result<(WeakKind, Ty), CheckerErrKind> {
        use PlaceElem::*;
        let mut ty = ty.clone();
        for elem in proj.by_ref() {
            ty = rcx.unpack_with(&ty, UnpackFlags::SHALLOW);
            match (elem, ty.kind()) {
                (Deref, Ref!(rk2, ty2)) => {
                    rk = rk.min(WeakKind::from(*rk2));
                    ty = ty2.clone();
                }
                (Deref, TyKind::Indexed(BaseTy::Adt(adt, substs), _)) if adt.is_box() => {
                    let (boxed, _) = box_args(substs);
                    ty = boxed.clone();
                }
                (Field(field), TyKind::Indexed(BaseTy::Tuple(tys), _)) => {
                    ty = tys[field.as_usize()].clone();
                }
                (Field(field), TyKind::Indexed(BaseTy::Adt(adt, substs), idx)) => {
                    let fields =
                        downcast(genv, rcx, adt.def_id(), VariantIdx::from_u32(0), substs, idx)?;
                    ty = fields[field.as_usize()].clone();
                }
                (Downcast(variant_idx), TyKind::Indexed(BaseTy::Adt(adt_def, substs), idx)) => {
                    let tys = downcast(genv, rcx, adt_def.def_id(), variant_idx, substs, idx)?;
                    ty = Ty::tuple(tys);
                    rcx.assume_invariants(&ty);
                }
                (Index(_), TyKind::Indexed(BaseTy::Slice(slice_ty), _)) => ty = slice_ty.clone(),
                _ => tracked_span_bug!("unexpected type and projection {elem:?} {ty:?}"),
            }
        }
        Ok((rk, ty))
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
                && let Some(Loc::Var(Var::Free(name), proj)) = path.to_loc()
                && !scope.contains(name)
            {
                debug_assert!(proj.is_empty());
                node.fold(&mut self.map, rcx, gen, false, true)?;
            }
        }
        Ok(())
    }

    #[must_use]
    pub fn fmap(&self, f: impl FnMut(&Binding) -> Binding) -> PathsTree {
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
    Uninit,
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
            Node::Internal(_, _) => tracked_span_bug!("expected `Node::Leaf`"),
        }
    }

    fn expect_owned_mut(&mut self) -> &mut Ty {
        match self {
            Node::Leaf(Binding::Owned(ty)) => ty,
            _ => tracked_span_bug!("expected `Binding::Owned`"),
        }
    }

    fn join_with(
        &mut self,
        gen: &mut ConstrGen,
        rcx: &mut RefineCtxt,
        other: &mut Node,
    ) -> Result<(), CheckerErrKind> {
        let map = &mut FxHashMap::default();
        match (&mut *self, &mut *other) {
            (Node::Internal(..), Node::Leaf(_)) => {
                other.join_with(gen, rcx, self)?;
            }
            (Node::Leaf(_), Node::Leaf(_)) => {}
            (Node::Leaf(_), Node::Internal(NodeKind::Adt(def, ..), _)) if def.is_enum() => {
                other.fold(map, rcx, gen, false, false)?;
            }
            (Node::Leaf(_), Node::Internal(..)) => {
                self.split(gen.genv, rcx)?;
                self.join_with(gen, rcx, other)?;
            }
            (
                Node::Internal(NodeKind::Adt(_, variant1, _), children1),
                Node::Internal(NodeKind::Adt(_, variant2, _), children2),
            ) => {
                if variant1 == variant2 {
                    for (ptr1, ptr2) in iter::zip(children1, children2) {
                        ptr1.borrow_mut()
                            .join_with(gen, rcx, &mut ptr2.borrow_mut())?;
                    }
                } else {
                    self.fold(map, rcx, gen, false, false)?;
                    other.fold(map, rcx, gen, false, false)?;
                }
            }
            (Node::Internal(kind1, children1), Node::Internal(kind2, children2)) => {
                let max = usize::max(children1.len(), children2.len());
                if let NodeKind::Uninit = kind1 {
                    children1.resize_with(max, || Node::owned(Ty::uninit()).into_ptr());
                }
                if let NodeKind::Uninit = kind2 {
                    children1.resize_with(max, || Node::owned(Ty::uninit()).into_ptr());
                }

                for (ptr1, ptr2) in iter::zip(children1, children2) {
                    ptr1.borrow_mut()
                        .join_with(gen, rcx, &mut ptr2.borrow_mut())?;
                }
            }
        };
        Ok(())
    }

    fn proj(
        &mut self,
        genv: &GlobalEnv,
        rcx: &mut RefineCtxt,
        field: Field,
    ) -> Result<&NodePtr, CheckerErrKind> {
        if let Node::Leaf(_) = self {
            self.split(genv, rcx)?;
        }
        match self {
            Node::Internal(kind, children) => {
                if let NodeKind::Uninit = kind {
                    let max = usize::max(field.as_usize() + 1, children.len());
                    children.resize_with(max, || Node::owned(Ty::uninit()).into_ptr());
                }
                Ok(&children[field.as_usize()])
            }
            Node::Leaf(..) => unreachable!(),
        }
    }

    fn downcast(
        &mut self,
        genv: &GlobalEnv,
        rcx: &mut RefineCtxt,
        variant_idx: VariantIdx,
    ) -> Result<(), CheckerErrKind> {
        match self {
            Node::Leaf(Binding::Owned(ty)) => {
                match ty.kind() {
                    TyKind::Indexed(BaseTy::Adt(adt_def, substs), idx) => {
                        let fields =
                            downcast(genv, rcx, adt_def.def_id(), variant_idx, substs, idx)?
                                .into_iter()
                                .map(|ty| {
                                    let ty = rcx.unpack(&ty);
                                    rcx.assume_invariants(&ty);
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

    fn split(&mut self, genv: &GlobalEnv, rcx: &mut RefineCtxt) -> Result<(), CheckerErrKind> {
        let ty = self.expect_leaf_mut().unblock(rcx);
        match ty.kind() {
            TyKind::Indexed(BaseTy::Tuple(tys), _) => {
                let children = tys
                    .iter()
                    .cloned()
                    .map(|ty| Node::owned(ty).into_ptr())
                    .collect();
                *self = Node::Internal(NodeKind::Tuple, children);
            }
            TyKind::Indexed(BaseTy::Adt(def, ..), ..) if def.is_struct() => {
                self.downcast(genv, rcx, VariantIdx::from_u32(0))?;
            }
            TyKind::Uninit => *self = Node::Internal(NodeKind::Uninit, vec![]),
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
                let ty = if partially_moved { Ty::uninit() } else { Ty::tuple(tys) };
                *self = Node::owned(ty.clone());
                ty
            }
            Node::Internal(NodeKind::Adt(adt_def, variant_idx, substs), children) => {
                let variant = gen.genv.variant(adt_def.def_id(), *variant_idx)?.expect("unexpected opaque struct");
                let fields: Vec<Ty> = children
                    .iter_mut()
                    .map(|node| {
                        let ty = node.fold(map, rcx, gen, unblock, close_boxes)?;
                        Ok::<_, CheckerErrKind>(rcx.unpack(&ty))
                    })
                    .try_collect()?;

                let partially_moved = fields.iter().any(|ty| ty.is_uninit());
                let ty = if partially_moved {
                    Ty::uninit()
                } else {
                    gen.check_constructor(rcx, &variant, substs, &fields)
                        .unwrap_or_else(|err| tracked_span_bug!("{err:?}"))
                };
                *self = Node::owned(ty.clone());
                ty
            }
            Node::Internal(NodeKind::Uninit, _) => {
                *self = Node::owned(Ty::uninit());
                Ty::uninit()
            }
        };
        Ok(ty)
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

    fn proj(
        &self,
        genv: &GlobalEnv,
        rcx: &mut RefineCtxt,
        field: Field,
    ) -> Result<NodePtr, CheckerErrKind> {
        Ok(NodePtr::clone(self.borrow_mut().proj(genv, rcx, field)?))
    }

    fn downcast(
        &self,
        genv: &GlobalEnv,
        rcx: &mut RefineCtxt,
        variant_idx: VariantIdx,
    ) -> Result<(), CheckerErrKind> {
        self.borrow_mut().downcast(genv, rcx, variant_idx)
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

impl TypeFoldable for Binding {
    fn super_fold_with<F: TypeFolder>(&self, folder: &mut F) -> Self {
        match self {
            Binding::Owned(ty) => Binding::Owned(ty.fold_with(folder)),
            Binding::Blocked(ty) => Binding::Blocked(ty.fold_with(folder)),
        }
    }

    fn super_visit_with<V: TypeVisitor>(&self, visitor: &mut V) {
        match self {
            Binding::Owned(ty) | Binding::Blocked(ty) => ty.visit_with(visitor),
        }
    }
}

fn downcast(
    genv: &GlobalEnv,
    rcx: &mut RefineCtxt,
    def_id: DefId,
    variant_idx: VariantIdx,
    substs: &[GenericArg],
    idx: &Index,
) -> Result<Vec<Ty>, CheckerErrKind> {
    if genv.tcx.adt_def(def_id).is_struct() {
        downcast_struct(genv, def_id, variant_idx, substs, idx)
    } else if genv.tcx.adt_def(def_id).is_enum() {
        downcast_enum(genv, rcx, def_id, variant_idx, substs, idx)
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
fn downcast_struct(
    genv: &GlobalEnv,
    def_id: DefId,
    variant_idx: VariantIdx,
    substs: &[GenericArg],
    idx: &Index,
) -> Result<Vec<Ty>, CheckerErrKind> {
    Ok(genv
        .variant(def_id, variant_idx)?
        .ok_or_else(|| CheckerErrKind::OpaqueStruct(def_id))?
        .replace_bvar(&idx.expr)
        .replace_generics(substs)
        .fields
        .to_vec())
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
    def_id: DefId,
    variant_idx: VariantIdx,
    substs: &[GenericArg],
    idx1: &Index,
) -> Result<Vec<Ty>, CheckerErrKind> {
    let variant_def = genv
        .variant(def_id, variant_idx)?
        .expect("enums cannot be opaque")
        .replace_generics(substs)
        .replace_bvar_with(|sort| rcx.define_vars(sort));

    let (.., idx2) = variant_def.ret.expect_adt();
    // FIXME(nilehmann) flatten indices
    debug_assert_eq!(idx2.expr.as_tuple().len(), idx1.expr.as_tuple().len());
    let constr =
        Expr::and(iter::zip(idx1.expr.as_tuple(), idx2.expr.as_tuple()).filter_map(|(e1, e2)| {
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

    impl Pretty for PathsTree {
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

    impl_debug_with_default_cx!(PathsTree);
}
