use std::{cell::RefCell, iter, rc::Rc};

use flux_middle::{
    global_env::{GlobalEnv, OpaqueStructErr},
    rty::{
        fold::{TypeFoldable, TypeFolder, TypeVisitor},
        AdtDef, BaseTy, Expr, Loc, Path, RefKind, Sort, Substs, Ty, TyKind, VariantIdx,
    },
    rustc::mir::{Field, Place, PlaceElem},
};
use itertools::Itertools;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;

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
        Root { kind: self.kind, ptr: self.ptr.borrow().clone().into_ptr() }
    }
}

pub enum LookupResult {
    Ptr(Path, Ty),
    Ref(RefKind, Ty),
}

impl LookupResult {
    pub fn ty(&self) -> Ty {
        match self {
            LookupResult::Ptr(_, ty) => ty.clone(),
            LookupResult::Ref(_, ty) => ty.clone(),
        }
    }
}

impl Root {
    fn new(node: Node, kind: LocKind) -> Root {
        Root { kind, ptr: node.into_ptr() }
    }
}

/// `downcast` on struct works as follows
/// Given a struct definition
///     struct Foo<A..>[(i...)] { fld : T, ...}
/// and a
///     * "place" `x: T<t..>[e..]`
/// the `downcast` returns a vector of `ty` for each `fld` of `x` where
///     * `x.fld : T[A := t ..]<i := e...>`
/// i.e. by substituting the type and value indices using the types and values from `x`.
fn downcast_struct(
    genv: &GlobalEnv,
    def_id: DefId,
    variant_idx: VariantIdx,
    substs: &[Ty],
    exprs: &[Expr],
) -> Result<Vec<Ty>, OpaqueStructErr> {
    Ok(genv
        .variant(def_id, variant_idx)?
        .replace_bound_vars(exprs)
        .replace_generic_types(substs)
        .fields
        .to_vec())
}

/// In contrast (w.r.t. `struct`) downcast on `enum` works as follows.
/// Given
///     * a "place" `x : T[i..]`
///     * a "variant" of type `forall z..,(y:t...) => T[j...]`
/// We want `downcast` to return a vector of types _and an assertion_ by
///     1. *Instantiate* the type to fresh names `z'...` to get `(y:t'...) => T[j'...]`
///     2. *Unpack* the fields using `y:t'...`
///     3. *Assert* the constraint `i == j'...`
fn downcast_enum(
    genv: &GlobalEnv,
    rcx: &mut RefineCtxt,
    def_id: DefId,
    variant_idx: VariantIdx,
    substs: &[Ty],
    exprs: &[Expr],
) -> Result<Vec<Ty>, OpaqueStructErr> {
    let variant_def = genv
        .variant(def_id, variant_idx)?
        .replace_bvars_with_fresh_fvars(|sort| rcx.define_var(sort))
        .replace_generic_types(substs);

    debug_assert_eq!(variant_def.ret.indices.len(), exprs.len());
    let constr =
        Expr::and(iter::zip(&variant_def.ret.indices, exprs).map(|(idx, e)| Expr::eq(idx, e)));
    rcx.assume_pred(constr);

    Ok(variant_def.fields.to_vec())
}

fn downcast(
    genv: &GlobalEnv,
    rcx: &mut RefineCtxt,
    def_id: DefId,
    variant_idx: VariantIdx,
    substs: &[Ty],
    exprs: &[Expr],
) -> Result<Vec<Ty>, OpaqueStructErr> {
    if genv.tcx.adt_def(def_id).is_struct() {
        downcast_struct(genv, def_id, variant_idx, substs, exprs)
    } else if genv.tcx.adt_def(def_id).is_enum() {
        downcast_enum(genv, rcx, def_id, variant_idx, substs, exprs)
    } else {
        panic!("Downcast without struct or enum!")
    }
}

impl PathsTree {
    pub fn lookup_place(
        &mut self,
        rcx: &mut RefineCtxt,
        gen: &mut ConstrGen,
        place: &Place,
    ) -> Result<LookupResult, OpaqueStructErr> {
        self.lookup_place_iter(
            rcx,
            gen,
            Loc::Local(place.local),
            &mut place.projection.iter().copied(),
            true,
        )
    }

    pub fn lookup_path(
        &mut self,
        rcx: &mut RefineCtxt,
        gen: &mut ConstrGen,
        path: &Path,
    ) -> Result<LookupResult, OpaqueStructErr> {
        let mut proj = path
            .projection()
            .iter()
            .map(|field| PlaceElem::Field(*field));
        self.lookup_place_iter(rcx, gen, path.loc, &mut proj, false)
    }

    pub fn get(&self, path: &Path) -> Binding {
        let mut node = &*self.map.get(&path.loc).unwrap().ptr.borrow();
        for f in path.projection() {
            match node {
                Node::Leaf(_) => panic!("expected `Node::Adt`"),
                Node::Internal(.., children) => node = &children[f.as_usize()],
            }
        }
        match node {
            Node::Leaf(binding) => binding.clone(),
            Node::Internal(..) => panic!("expcted `Node::Ty`"),
        }
    }

    pub fn update_binding(&mut self, path: &Path, binding: Binding) {
        self.get_node_mut(path, |node, _| {
            *node = Node::Leaf(binding);
        });
    }

    pub fn update(&mut self, path: &Path, new_ty: Ty) {
        self.get_node_mut(path, |node, _| {
            *node.expect_owned_mut() = new_ty;
        });
    }

    pub fn block(&mut self, path: &Path) {
        self.get_node_mut(path, |node, _| {
            match node {
                Node::Leaf(Binding::Owned(ty)) => *node = Node::Leaf(Binding::Blocked(ty.clone())),
                _ => panic!("expected owned binding"),
            }
        });
    }

    fn get_node_mut(&mut self, path: &Path, f: impl FnOnce(&mut Node, &mut LocMap)) {
        let root = Rc::clone(&self.map.get(&path.loc).unwrap().ptr);
        let mut node = &mut *root.borrow_mut();
        for f in path.projection() {
            match node {
                Node::Leaf(_) => panic!("expected `Node::Adt"),
                Node::Internal(.., children) => node = &mut children[f.as_usize()],
            }
        }
        f(node, &mut self.map);
    }

    pub(super) fn insert(&mut self, loc: Loc, ty: Ty, kind: LocKind) {
        self.map.insert(loc, Root::new(Node::owned(ty), kind));
    }

    pub fn contains_loc(&self, loc: Loc) -> bool {
        self.map.contains_key(&loc)
    }

    pub fn iter(&self, mut f: impl FnMut(Path, &Binding)) {
        fn go(node: &Node, loc: Loc, proj: &mut Vec<Field>, f: &mut impl FnMut(Path, &Binding)) {
            match node {
                Node::Leaf(binding) => {
                    f(Path::new(loc, proj.as_slice()), binding);
                }
                Node::Internal(_, children) => {
                    for (idx, node) in children.iter().enumerate() {
                        proj.push(Field::from(idx));
                        go(node, loc, proj, f);
                        proj.pop();
                    }
                }
            }
        }
        let mut proj = vec![];
        for (loc, root) in &self.map {
            go(&root.ptr.borrow(), *loc, &mut proj, &mut f);
        }
    }

    pub fn paths(&self) -> Vec<Path> {
        let mut paths = vec![];
        self.iter(|path, _| paths.push(path));
        paths
    }

    pub fn flatten(&self) -> Vec<(Path, Binding)> {
        let mut bindings = vec![];
        self.iter(|path, binding| bindings.push((path, binding.clone())));
        bindings
    }

    pub fn join_with(&mut self, rcx: &mut RefineCtxt, gen: &mut ConstrGen, other: &mut PathsTree) {
        for (loc, root1) in &self.map {
            let node2 = &mut *other.map[loc].ptr.borrow_mut();
            root1.ptr.borrow_mut().join_with(gen, rcx, node2);
        }
    }

    fn lookup_place_iter(
        &mut self,
        rcx: &mut RefineCtxt,
        gen: &mut ConstrGen,
        loc: Loc,
        place_proj: &mut impl Iterator<Item = PlaceElem>,
        close_boxes: bool,
    ) -> Result<LookupResult, OpaqueStructErr> {
        let mut path = Path::from(loc);
        'outer: loop {
            let loc = path.loc;
            let mut path_proj = vec![];

            let root = Rc::clone(&self.map[&loc].ptr);

            let mut node = &mut *root.borrow_mut();

            for field in path.projection() {
                node = node.proj(gen.genv, rcx, *field)?;
                path_proj.push(*field);
            }

            for elem in place_proj.by_ref() {
                match elem {
                    PlaceElem::Field(field) => {
                        path_proj.push(field);
                        node = node.proj(gen.genv, rcx, field)?;
                    }
                    PlaceElem::Downcast(variant_idx) => {
                        node.downcast(gen.genv, rcx, variant_idx)?;
                    }
                    PlaceElem::Deref => {
                        let ty = node.expect_owned();
                        match ty.kind() {
                            TyKind::Ptr(_, ptr_path) => {
                                path = ptr_path.clone();
                                continue 'outer;
                            }
                            TyKind::BoxPtr(loc, _) => {
                                path = Path::from(Loc::Free(*loc));
                                continue 'outer;
                            }
                            TyKind::Ref(mode, ty) => {
                                return Self::lookup_place_iter_ty(rcx, gen, *mode, ty, place_proj);
                            }
                            TyKind::Indexed(BaseTy::Adt(_, substs), _) if ty.is_box() => {
                                let fresh = rcx.define_var(&Sort::Loc);
                                let loc = Loc::Free(fresh);
                                *node = Node::owned(Ty::box_ptr(fresh, substs[1].clone()));
                                self.insert(loc, substs[0].clone(), LocKind::Box);
                                path = Path::from(loc);
                                continue 'outer;
                            }
                            _ => panic!("Unsupported Deref: {elem:?} {ty:?}"),
                        }
                    }
                }
            }
            return Ok(LookupResult::Ptr(
                Path::new(loc, path_proj),
                node.fold(&mut self.map, rcx, gen, true, close_boxes),
            ));
        }
    }

    fn lookup_place_iter_ty(
        rcx: &mut RefineCtxt,
        gen: &mut ConstrGen,
        mut rk: RefKind,
        ty: &Ty,
        proj: &mut impl Iterator<Item = PlaceElem>,
    ) -> Result<LookupResult, OpaqueStructErr> {
        use PlaceElem::*;
        let mut ty = ty.clone();
        for elem in proj.by_ref() {
            match (elem, ty.kind()) {
                (Deref, TyKind::Ref(rk2, ty2)) => {
                    rk = rk.min(*rk2);
                    ty = ty2.clone();
                }
                (Deref, TyKind::Indexed(BaseTy::Adt(_, substs), _)) if ty.is_box() => {
                    ty = substs[0].clone();
                }
                (Field(field), TyKind::Tuple(tys)) => {
                    ty = tys[field.as_usize()].clone();
                }
                (Field(field), TyKind::Indexed(BaseTy::Adt(adt, substs), idxs)) => {
                    let fields = downcast(
                        gen.genv,
                        rcx,
                        adt.def_id(),
                        VariantIdx::from_u32(0),
                        substs,
                        &idxs.to_exprs(),
                    )?;
                    ty = fields[field.as_usize()].clone();
                }
                (Downcast(variant_idx), TyKind::Indexed(BaseTy::Adt(adt_def, substs), idxs)) => {
                    let tys = downcast(
                        gen.genv,
                        rcx,
                        adt_def.def_id(),
                        variant_idx,
                        substs,
                        &idxs.to_exprs(),
                    )?;
                    ty = rcx.unpack_with(&Ty::tuple(tys), UnpackFlags::INVARIANTS);
                }
                _ => unreachable!("{elem:?} {ty:?}"),
            }
        }
        Ok(LookupResult::Ref(rk, ty))
    }

    pub fn close_boxes(&mut self, rcx: &mut RefineCtxt, gen: &mut ConstrGen, scope: &Scope) {
        let mut paths = self.paths();
        paths.sort();
        for path in paths.into_iter().rev() {
            self.get_node_mut(&path, |node, map| {
                if let Node::Leaf(Binding::Owned(ty)) = node &&
                   let TyKind::BoxPtr(loc, _) = ty.kind() &&
                   !scope.contains(*loc)
                {
                    node.fold(map, rcx, gen, false, true);
                }
            });
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

type NodePtr = Rc<RefCell<Node>>;

#[derive(Debug, Clone, Eq, PartialEq)]
enum Node {
    Leaf(Binding),
    Internal(NodeKind, Vec<Node>),
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

impl Node {
    fn into_ptr(self) -> NodePtr {
        Rc::new(RefCell::new(self))
    }

    fn owned(ty: Ty) -> Node {
        Node::Leaf(Binding::Owned(ty))
    }

    #[track_caller]
    fn expect_owned(&self) -> Ty {
        match self {
            Node::Leaf(Binding::Owned(ty)) => ty.clone(),
            _ => panic!("expected type"),
        }
    }

    fn expect_owned_mut(&mut self) -> &mut Ty {
        match self {
            Node::Leaf(Binding::Owned(ty)) => ty,
            _ => panic!("expected type"),
        }
    }

    fn join_with(&mut self, gen: &mut ConstrGen, rcx: &mut RefineCtxt, other: &mut Node) {
        let map = &mut FxHashMap::default();
        match (&mut *self, &mut *other) {
            (Node::Internal(..), Node::Leaf(_)) => {
                other.join_with(gen, rcx, self);
            }
            (Node::Leaf(_), Node::Leaf(_)) => {}
            (Node::Leaf(_), Node::Internal(NodeKind::Adt(def, ..), _)) if def.is_enum() => {
                other.fold(map, rcx, gen, false, false);
            }
            (Node::Leaf(_), Node::Internal(..)) => {
                self.split(gen.genv, rcx).unwrap();
                self.join_with(gen, rcx, other);
            }
            (
                Node::Internal(NodeKind::Adt(_, variant1, _), children1),
                Node::Internal(NodeKind::Adt(_, variant2, _), children2),
            ) => {
                if variant1 == variant2 {
                    for (node1, node2) in iter::zip(children1, children2) {
                        node1.join_with(gen, rcx, node2);
                    }
                } else {
                    self.fold(map, rcx, gen, false, false);
                    other.fold(map, rcx, gen, false, false);
                }
            }
            (Node::Internal(kind1, children1), Node::Internal(kind2, children2)) => {
                let max = usize::max(children1.len(), children2.len());
                if let NodeKind::Uninit = kind1 {
                    children1.resize(max, Node::owned(Ty::uninit()));
                }
                if let NodeKind::Uninit = kind2 {
                    children1.resize(max, Node::owned(Ty::uninit()));
                }

                for (node1, node2) in iter::zip(children1, children2) {
                    node1.join_with(gen, rcx, node2);
                }
            }
        };
    }

    fn proj(
        &mut self,
        genv: &GlobalEnv,
        rcx: &mut RefineCtxt,
        field: Field,
    ) -> Result<&mut Node, OpaqueStructErr> {
        if let Node::Leaf(_) = self {
            self.split(genv, rcx)?;
        }
        match self {
            Node::Internal(kind, children) => {
                if let NodeKind::Uninit = kind {
                    let max = usize::max(field.as_usize() + 1, children.len());
                    children.resize(max, Node::owned(Ty::uninit()));
                }
                Ok(&mut children[field.as_usize()])
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
                let ty = ty.unconstr();
                match ty.kind() {
                    TyKind::Indexed(BaseTy::Adt(adt_def, substs), idxs) => {
                        let fields = downcast(
                            genv,
                            rcx,
                            adt_def.def_id(),
                            variant_idx,
                            substs,
                            &idxs.to_exprs(),
                        )?
                        .into_iter()
                        .map(|ty| Node::owned(rcx.unpack(&ty)))
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

    fn split(&mut self, genv: &GlobalEnv, rcx: &mut RefineCtxt) -> Result<(), OpaqueStructErr> {
        let ty = self.expect_owned();
        match ty.kind() {
            TyKind::Tuple(tys) => {
                let children = tys.iter().cloned().map(Node::owned).collect();
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
                    let root = map.remove(&Loc::Free(*loc)).unwrap();
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
                    field.fmap_mut(f);
                }
            }
        }
    }
}

impl Binding {
    pub fn expect_owned(&self) -> Ty {
        match self {
            Binding::Owned(ty) => ty.clone(),
            Binding::Blocked(_) => panic!("expected owned"),
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

mod pretty {
    use std::fmt;

    use flux_middle::pretty::*;
    use itertools::Itertools;

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
    }

    impl_debug_with_default_cx!(PathsTree);
}
