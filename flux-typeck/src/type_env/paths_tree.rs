use std::{cell::RefCell, iter, rc::Rc};

use flux_middle::{
    fhir::WeakKind,
    global_env::{GlobalEnv, OpaqueStructErr},
    rty::{
        box_args,
        fold::{TypeFoldable, TypeFolder, TypeVisitor},
        AdtDef, BaseTy, Expr, GenericArg, Loc, Path, RefineArg, Sort, Substs, Ty, TyKind,
        VariantIdx,
    },
    rustc::mir::{Field, Place, PlaceElem, SourceInfo},
};
use itertools::Itertools;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_span::Span;

use crate::{
    constraint_gen::ConstrGen,
    refine_tree::{RefineCtxt, Scope, UnpackFlags},
};

#[derive(Default, Eq, PartialEq, Clone)]
pub struct PathsTree {
    map: LocMap,
}

type LocMap = FxHashMap<Loc, Root>;

#[derive(Eq, PartialEq)]
struct Root {
    kind: LocKind,
    ptr: NodePtr,
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub(super) enum LocKind {
    Local,
    Box,
    Universal,
}

impl Clone for Root {
    fn clone(&self) -> Root {
        Root { kind: self.kind, ptr: self.ptr.deep_clone() }
    }
}

pub struct LookupResult<'a> {
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
        self.loc
    }

    fn proj(&self) -> Self::Iter<'_> {
        self.projection().iter().map(|f| PlaceElem::Field(*f))
    }
}

enum LookupKind {
    Strg(Path, NodePtr),
    Weak(WeakKind, Ty),
}

pub enum FoldResult {
    Strg(Path, Ty),
    Weak(WeakKind, Ty),
}

impl FoldResult {
    pub fn ty(&self) -> Ty {
        match self {
            FoldResult::Strg(_, ty) | FoldResult::Weak(_, ty) => ty.clone(),
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
            Node::Internal(..) => panic!("expected `Node::Leaf`"),
        }
    }

    fn get_node(&self, path: &Path) -> NodePtr {
        let mut ptr = NodePtr::clone(
            &self
                .map
                .get(&path.loc)
                .unwrap_or_else(|| panic!("key not found `{:?}`", path.loc))
                .ptr,
        );
        for f in path.projection() {
            ptr = {
                let node = ptr.borrow();
                match &*node {
                    Node::Leaf(_) => panic!("expected `Node::Internal`"),
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

    pub fn block(&mut self, path: &Path) {
        let ptr = self.get_node(path);
        let mut node = ptr.borrow_mut();
        match &mut *node {
            Node::Leaf(Binding::Owned(ty)) => *node = Node::Leaf(Binding::Blocked(ty.clone())),
            _ => panic!("expected owned binding"),
        }
    }

    pub(super) fn insert(&mut self, loc: Loc, ty: Ty, kind: LocKind) {
        self.map.insert(loc, Root::new(Node::owned(ty), kind));
    }

    pub fn contains_loc(&self, loc: Loc) -> bool {
        self.map.contains_key(&loc)
    }

    pub fn iter(&self, mut f: impl FnMut(Path, &Binding)) {
        fn go(ptr: &NodePtr, loc: Loc, proj: &mut Vec<Field>, f: &mut impl FnMut(Path, &Binding)) {
            let node = ptr.borrow();
            match &*node {
                Node::Leaf(binding) => {
                    f(Path::new(loc, proj.as_slice()), binding);
                }
                Node::Internal(_, children) => {
                    for (idx, ptr) in children.iter().enumerate() {
                        proj.push(Field::from(idx));
                        go(ptr, loc, proj, f);
                        proj.pop();
                    }
                }
            }
        }
        let mut proj = vec![];
        for (loc, root) in &self.map {
            go(&root.ptr, *loc, &mut proj, &mut f);
        }
    }

    pub(super) fn paths(&self) -> Vec<Path> {
        let mut paths = vec![];
        self.iter(|path, _| paths.push(path));
        paths
    }

    pub(super) fn flatten(&self) -> Vec<(Path, Binding)> {
        let mut bindings = vec![];
        self.iter(|path, binding| bindings.push((path, binding.clone())));
        bindings
    }

    pub(super) fn join_with(
        &mut self,
        rcx: &mut RefineCtxt,
        gen: &mut ConstrGen,
        other: &mut PathsTree,
        src_info: Option<SourceInfo>,
    ) {
        for (loc, root1) in &self.map {
            let node2 = &mut *other.map[loc].ptr.borrow_mut();
            root1.ptr.borrow_mut().join_with(gen, rcx, node2, src_info);
        }
    }

    pub(super) fn lookup<'a>(
        &'a mut self,
        genv: &GlobalEnv,
        rcx: &mut RefineCtxt,
        key: &impl LookupKey,
        src_info: Option<SourceInfo>,
    ) -> Result<LookupResult<'a>, OpaqueStructErr> {
        let span = src_info.map(|src_info| src_info.span);
        let mut path = Path::from(key.loc());
        let place_proj = &mut key.proj();

        'outer: loop {
            let loc = path.loc;
            let mut path_proj = vec![];

            let mut ptr = NodePtr::clone(&self.map[&loc].ptr);

            for field in path.projection() {
                ptr = ptr.proj(genv, rcx, *field, span)?;
                path_proj.push(*field);
            }

            for elem in place_proj.by_ref() {
                match elem {
                    PlaceElem::Field(field) => {
                        path_proj.push(field);
                        ptr = ptr.proj(genv, rcx, field, span)?;
                    }
                    PlaceElem::Downcast(variant_idx) => {
                        ptr.downcast(genv, rcx, variant_idx)?;
                    }
                    PlaceElem::Deref => {
                        let ty = ptr.borrow().expect_owned(span);
                        match ty.kind() {
                            TyKind::Ptr(_, ptr_path) => {
                                path = ptr_path.clone();
                                continue 'outer;
                            }
                            TyKind::BoxPtr(loc, _) => {
                                path = Path::from(Loc::from(*loc));
                                continue 'outer;
                            }
                            TyKind::Ref(rk, ty) => {
                                let (rk, ty) = Self::lookup_ty(
                                    genv,
                                    rcx,
                                    WeakKind::from(*rk),
                                    ty,
                                    place_proj,
                                    src_info,
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
                                *ptr.borrow_mut() = Node::owned(Ty::box_ptr(fresh, alloc.clone()));
                                self.insert(loc, boxed.clone(), LocKind::Box);
                                path = Path::from(loc);
                                continue 'outer;
                            }
                            _ => panic!("Unsupported Deref: {elem:?} {ty:?} at {src_info:?}"),
                        }
                    }
                    PlaceElem::Index(_) => {
                        let ty = ptr.borrow().expect_owned(span);
                        match ty.kind() {
                            TyKind::Array(arr_ty, _) => {
                                let (rk, ty) = Self::lookup_ty(
                                    genv,
                                    rcx,
                                    WeakKind::Arr,
                                    arr_ty,
                                    place_proj,
                                    src_info,
                                )?;
                                return Ok(LookupResult {
                                    tree: self,
                                    kind: LookupKind::Weak(rk, ty),
                                });
                            }
                            _ => panic!("Unsupported Index: {elem:?} {ty:?} at {src_info:?}"),
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
        src_info: Option<SourceInfo>,
    ) -> Result<(WeakKind, Ty), OpaqueStructErr> {
        use PlaceElem::*;
        let mut ty = ty.clone();
        for elem in proj.by_ref() {
            match (elem, ty.kind()) {
                (Deref, TyKind::Ref(rk2, ty2)) => {
                    rk = rk.min(WeakKind::from(*rk2));
                    ty = ty2.clone();
                }
                (Deref, TyKind::Indexed(BaseTy::Adt(adt, substs), _)) if adt.is_box() => {
                    let (boxed, _) = box_args(substs);
                    ty = boxed.clone();
                }
                (Field(field), TyKind::Tuple(tys)) => {
                    ty = tys[field.as_usize()].clone();
                }
                (Field(field), TyKind::Indexed(BaseTy::Adt(adt, substs), idxs)) => {
                    let fields = downcast(
                        genv,
                        rcx,
                        adt.def_id(),
                        VariantIdx::from_u32(0),
                        substs,
                        idxs.args(),
                    )?;
                    ty = fields[field.as_usize()].clone();
                }
                (Downcast(variant_idx), TyKind::Indexed(BaseTy::Adt(adt_def, substs), idxs)) => {
                    let tys =
                        downcast(genv, rcx, adt_def.def_id(), variant_idx, substs, idxs.args())?;
                    ty = rcx.unpack_with(&Ty::tuple(tys), UnpackFlags::INVARIANTS);
                }
                (Index(_), TyKind::Indexed(BaseTy::Slice(slice_ty), _)) => ty = slice_ty.clone(),
                _ => todo!("lookup_ty {elem:?} {ty:?} at {src_info:?}"),
            }
        }
        Ok((rk, ty))
    }

    pub fn close_boxes(&mut self, rcx: &mut RefineCtxt, gen: &mut ConstrGen, scope: &Scope) {
        let mut paths = self.paths();
        paths.sort();
        for path in paths.into_iter().rev() {
            let ptr = self.get_node(&path);
            let mut node = ptr.borrow_mut();
            if let Node::Leaf(Binding::Owned(ty)) = &mut *node &&
                let TyKind::BoxPtr(loc, _) = ty.kind() &&
                !scope.contains(*loc)
            {
                node.fold(&mut self.map, rcx, gen, false, true);
            }
        }
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
    pub fn fold(self, rcx: &mut RefineCtxt, gen: &mut ConstrGen, close_boxes: bool) -> FoldResult {
        match self.kind {
            LookupKind::Strg(path, ptr) => {
                FoldResult::Strg(path, ptr.fold(&mut self.tree.map, rcx, gen, true, close_boxes))
            }
            LookupKind::Weak(rk, ty) => FoldResult::Weak(rk, ty),
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
    fn expect_owned(&self, span: Option<Span>) -> Ty {
        match self {
            Node::Leaf(Binding::Owned(ty)) => ty.clone(),
            _ => panic!("expected type at {span:?}"),
        }
    }

    fn expect_owned_mut(&mut self) -> &mut Ty {
        match self {
            Node::Leaf(Binding::Owned(ty)) => ty,
            _ => panic!("expected type"),
        }
    }

    fn join_with(
        &mut self,
        gen: &mut ConstrGen,
        rcx: &mut RefineCtxt,
        other: &mut Node,
        src_info: Option<SourceInfo>,
    ) {
        let map = &mut FxHashMap::default();
        let span = src_info.map(|info| info.span);
        match (&mut *self, &mut *other) {
            (Node::Internal(..), Node::Leaf(_)) => {
                other.join_with(gen, rcx, self, src_info);
            }
            (Node::Leaf(_), Node::Leaf(_)) => {}
            (Node::Leaf(_), Node::Internal(NodeKind::Adt(def, ..), _)) if def.is_enum() => {
                other.fold(map, rcx, gen, false, false);
            }
            (Node::Leaf(_), Node::Internal(..)) => {
                self.split(gen.genv, rcx, span).unwrap();
                self.join_with(gen, rcx, other, src_info);
            }
            (
                Node::Internal(NodeKind::Adt(_, variant1, _), children1),
                Node::Internal(NodeKind::Adt(_, variant2, _), children2),
            ) => {
                if variant1 == variant2 {
                    for (ptr1, ptr2) in iter::zip(children1, children2) {
                        ptr1.borrow_mut()
                            .join_with(gen, rcx, &mut ptr2.borrow_mut(), src_info);
                    }
                } else {
                    self.fold(map, rcx, gen, false, false);
                    other.fold(map, rcx, gen, false, false);
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
                        .join_with(gen, rcx, &mut ptr2.borrow_mut(), src_info);
                }
            }
        };
    }

    fn proj(
        &mut self,
        genv: &GlobalEnv,
        rcx: &mut RefineCtxt,
        field: Field,
        span: Option<Span>,
    ) -> Result<&NodePtr, OpaqueStructErr> {
        if let Node::Leaf(_) = self {
            self.split(genv, rcx, span)?;
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
    ) -> Result<(), OpaqueStructErr> {
        match self {
            Node::Leaf(Binding::Owned(ty)) => {
                match ty.kind() {
                    TyKind::Indexed(BaseTy::Adt(adt_def, substs), idxs) => {
                        let fields = downcast(
                            genv,
                            rcx,
                            adt_def.def_id(),
                            variant_idx,
                            substs,
                            idxs.args(),
                        )?
                        .into_iter()
                        .map(|ty| {
                            let ty = rcx.unpack_with(&ty, UnpackFlags::INVARIANTS);
                            Node::owned(ty).into_ptr()
                        })
                        .collect();
                        *self = Node::Internal(
                            NodeKind::Adt(adt_def.clone(), variant_idx, substs.clone()),
                            fields,
                        );
                    }
                    _ => panic!("type cannot be downcasted: `{ty:?}`"),
                }
            }
            Node::Internal(NodeKind::Adt(_, variant_idx2, _), _) => {
                debug_assert_eq!(variant_idx, *variant_idx2);
            }
            Node::Internal(..) => panic!("invalid downcast"),
            Node::Leaf(..) => panic!("blocked"),
        }
        Ok(())
    }

    fn split(
        &mut self,
        genv: &GlobalEnv,
        rcx: &mut RefineCtxt,
        span: Option<Span>,
    ) -> Result<(), OpaqueStructErr> {
        let ty = self.expect_owned(span);
        match ty.kind() {
            TyKind::Tuple(tys) => {
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
            _ => panic!("type cannot be split: `{ty:?}`"),
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
    ) -> Ty {
        match self {
            Node::Leaf(Binding::Owned(ty)) => {
                if let TyKind::BoxPtr(loc, alloc) = ty.kind() && close_boxes {
                    let root = map.remove(&Loc::from(*loc)).unwrap();
                    debug_assert!(matches!(root.kind, LocKind::Box));
                    let boxed_ty = root.ptr.borrow_mut().fold(map, rcx, gen, unblock, close_boxes);
                    let ty = gen.genv.mk_box(boxed_ty, alloc.clone());
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
                    panic!("I don't know what to do if you don't ask me to unblock.");
                }
            }
            Node::Internal(NodeKind::Tuple, children) => {
                let tys= children
                    .iter_mut()
                    .map(|node| node.fold(map, rcx, gen, unblock, close_boxes))
                    .collect_vec();
                let ty = Ty::tuple(tys);
                *self = Node::owned(ty.clone());
                ty
            }
            Node::Internal(NodeKind::Adt(adt_def, variant_idx, substs), children) => {
                let variant = gen.genv.variant(adt_def.def_id(), *variant_idx).unwrap();
                let fields = children
                    .iter_mut()
                    .map(|node| node.fold(map, rcx, gen, unblock, close_boxes))
                    .collect_vec();

                let partially_moved = fields.iter().any(|ty| ty.is_uninit());
                if partially_moved {
                    *self = Node::owned(Ty::uninit());
                    Ty::uninit()
                } else {
                    let output = gen
                        .check_constructor(rcx, &variant, substs, &fields)
                        .unwrap()
                        .to_ty();
                    *self = Node::owned(output.clone());
                    output
                }
            }
            Node::Internal(NodeKind::Uninit, _) => {
                *self = Node::owned(Ty::uninit());
                Ty::uninit()
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
    ) -> Ty {
        self.borrow_mut().fold(map, rcx, gen, unblock, close_boxes)
    }

    fn proj(
        &self,
        genv: &GlobalEnv,
        rcx: &mut RefineCtxt,
        field: Field,
        span: Option<Span>,
    ) -> Result<NodePtr, OpaqueStructErr> {
        Ok(NodePtr::clone(self.borrow_mut().proj(genv, rcx, field, span)?))
    }

    fn downcast(
        &self,
        genv: &GlobalEnv,
        rcx: &mut RefineCtxt,
        variant_idx: VariantIdx,
    ) -> Result<(), OpaqueStructErr> {
        self.borrow_mut().downcast(genv, rcx, variant_idx)
    }
}

impl Binding {
    pub fn expect_owned(&self, span: Option<Span>) -> Ty {
        match self {
            Binding::Owned(ty) => ty.clone(),
            Binding::Blocked(_) => panic!("expected owned at {span:?}"),
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
    args: &[RefineArg],
) -> Result<Vec<Ty>, OpaqueStructErr> {
    if genv.tcx.adt_def(def_id).is_struct() {
        downcast_struct(genv, def_id, variant_idx, substs, args)
    } else if genv.tcx.adt_def(def_id).is_enum() {
        Ok(downcast_enum(genv, rcx, def_id, variant_idx, substs, args))
    } else {
        panic!("Downcast without struct or enum!")
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
    args: &[RefineArg],
) -> Result<Vec<Ty>, OpaqueStructErr> {
    Ok(genv
        .variant(def_id, variant_idx)?
        .replace_bvars(args)
        .replace_generic_args(substs)
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
    args: &[RefineArg],
) -> Vec<Ty> {
    let variant_def = genv
        .variant(def_id, variant_idx)
        .unwrap()
        .replace_bvars_with_fresh_fvars(|sort| rcx.define_var(sort))
        .replace_generic_args(substs);

    debug_assert_eq!(variant_def.ret.args.len(), args.len());
    let constr = Expr::and(iter::zip(&variant_def.ret.args, args).filter_map(|(arg1, arg2)| {
        if let (RefineArg::Expr(e1), RefineArg::Expr(e2)) = (arg1, arg2) {
            Some(Expr::eq(e1, e2))
        } else {
            None
        }
    }));
    rcx.assume_pred(constr);

    variant_def.fields.to_vec()
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
                .filter(|(_, ty)| !cx.hide_uninit || !ty.is_uninit())
                .sorted_by(|(path1, _), (path2, _)| path1.cmp(path2));
            w!(
                "{{{}}}",
                ^bindings
                    .format_with(", ", |(loc, binding), f| {
                        match binding {
                            Binding::Owned(ty) => {
                                f(&format_args_cx!("{:?}: {:?}", loc, ty))
                            }
                            Binding::Blocked(ty) => {
                                f(&format_args_cx!("{:?}:† {:?}", loc, ty))
                            }
                        }
                    })
            )
        }

        fn default_cx(tcx: TyCtxt) -> PPrintCx {
            PPrintCx::default(tcx).kvar_args(KVarArgs::Hide)
        }
    }

    impl_debug_with_default_cx!(PathsTree);
}
