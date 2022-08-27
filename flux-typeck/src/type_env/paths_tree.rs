use std::{cell::RefCell, iter, rc::Rc};

use flux_middle::{
    global_env::GlobalEnv,
    rustc::mir::{Field, Place, PlaceElem},
    ty::{
        fold::{TypeFoldable, TypeFolder, TypeVisitor},
        AdtDef, BaseTy, Loc, Path, RefKind, Sort, Substs, Ty, TyKind, VariantIdx,
    },
};
use itertools::Itertools;
use rustc_hash::FxHashMap;

use crate::{
    constraint_gen::ConstrGen,
    refine_tree::{RefineCtxt, Scope},
};

#[derive(Default, Eq, PartialEq)]
pub struct PathsTree {
    map: FxHashMap<Loc, NodePtr>,
}

impl Clone for PathsTree {
    fn clone(&self) -> Self {
        let map = self
            .map
            .iter()
            .map(|(loc, ptr)| (*loc, Rc::new(RefCell::new(ptr.borrow().clone()))))
            .collect();
        Self { map }
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

impl PathsTree {
    pub fn lookup_place(
        &mut self,
        rcx: &mut RefineCtxt,
        gen: &mut ConstrGen,
        place: &Place,
    ) -> LookupResult {
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
    ) -> LookupResult {
        let mut proj = path
            .projection()
            .iter()
            .map(|field| PlaceElem::Field(*field));
        self.lookup_place_iter(rcx, gen, path.loc, &mut proj, false)
    }

    pub fn get(&self, path: &Path) -> Binding {
        let mut node = &*self.map.get(&path.loc).unwrap().borrow();
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

    fn get_node_mut(
        &mut self,
        path: &Path,
        f: impl FnOnce(&mut Node, &mut FxHashMap<Loc, NodePtr>),
    ) {
        let root = Rc::clone(self.map.get(&path.loc).unwrap());
        let mut node = &mut *root.borrow_mut();
        for f in path.projection() {
            match node {
                Node::Leaf(_) => panic!("expected `Node::Adt"),
                Node::Internal(.., children) => node = &mut children[f.as_usize()],
            }
        }
        f(node, &mut self.map)
    }

    pub fn insert(&mut self, loc: Loc, ty: Ty) {
        self.map.insert(loc, Rc::new(RefCell::new(Node::owned(ty))));
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
        for (loc, node) in &self.map {
            go(&node.borrow(), *loc, &mut proj, &mut f)
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
        for (loc, node1) in &self.map {
            let node2 = &mut *other.map[loc].borrow_mut();
            node1.borrow_mut().join_with(gen, rcx, node2);
        }
    }

    fn lookup_place_iter(
        &mut self,
        rcx: &mut RefineCtxt,
        gen: &mut ConstrGen,
        loc: Loc,
        place_proj: &mut impl Iterator<Item = PlaceElem>,
        close_boxes: bool,
    ) -> LookupResult {
        let mut path = Path::from(loc);
        'outer: loop {
            let loc = path.loc;
            let mut path_proj = vec![];

            let root = Rc::clone(&self.map[&loc]);

            let mut node = &mut *root.borrow_mut();

            for field in path.projection() {
                node = node.proj(gen.genv, rcx, *field);
                path_proj.push(*field);
            }

            for elem in place_proj.by_ref() {
                match elem {
                    PlaceElem::Field(field) => {
                        path_proj.push(field);
                        node = node.proj(gen.genv, rcx, field);
                    }
                    PlaceElem::Downcast(variant_idx) => {
                        node.downcast(gen.genv, rcx, variant_idx);
                    }
                    PlaceElem::Deref => {
                        let ty = node.expect_owned();
                        match ty.kind() {
                            TyKind::Ptr(ptr_path) => {
                                path = ptr_path.clone();
                                continue 'outer;
                            }
                            TyKind::BoxPtr(loc, _) => {
                                path = Path::from(Loc::Free(*loc));
                                continue 'outer;
                            }
                            TyKind::Ref(mode, ty) => {
                                return self.lookup_place_iter_ty(gen, *mode, &ty, place_proj);
                            }
                            TyKind::Indexed(BaseTy::Adt(_, substs), _) if ty.is_box() => {
                                let fresh = rcx.define_var(&Sort::Loc);
                                let loc = Loc::Free(fresh);
                                *node = Node::owned(Ty::box_ptr(fresh, substs[1].clone()));
                                self.insert(loc, substs[0].clone());
                                path = Path::from(loc);
                                continue 'outer;
                            }
                            _ => panic!("Unsupported Deref: {elem:?} {ty:?}"),
                        }
                    }
                }
            }
            return LookupResult::Ptr(
                Path::new(loc, path_proj),
                node.fold(&mut self.map, rcx, gen, true, close_boxes),
            );
        }
    }

    fn lookup_place_iter_ty(
        &mut self,
        gen: &mut ConstrGen,
        mut rk: RefKind,
        ty: &Ty,
        proj: &mut impl Iterator<Item = PlaceElem>,
    ) -> LookupResult {
        use PlaceElem::*;
        let mut ty = ty.clone();
        // MERGE while let Some(elem) = proj.next() {
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
                    let fields = gen.genv.downcast(
                        adt.def_id(),
                        VariantIdx::from_u32(0),
                        substs,
                        &idxs.to_exprs(),
                    );
                    ty = fields[field.as_usize()].clone();
                }
                (Downcast(variant_idx), TyKind::Indexed(BaseTy::Adt(adt_def, substs), idxs)) => {
                    let tys =
                        gen.genv
                            .downcast(adt_def.def_id(), variant_idx, substs, &idxs.to_exprs());
                    ty = Ty::tuple(tys)
                }
                _ => unreachable!("{elem:?} {ty:?}"),
            }
        }
        LookupResult::Ref(rk, ty)
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
        for node in self.map.values_mut() {
            node.borrow_mut().fmap_mut(&mut f);
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
                self.split(gen.genv, rcx);
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

    fn proj(&mut self, genv: &GlobalEnv, rcx: &mut RefineCtxt, field: Field) -> &mut Node {
        if let Node::Leaf(_) = self {
            self.split(genv, rcx);
        }
        match self {
            Node::Internal(kind, children) => {
                if let NodeKind::Uninit = kind {
                    let max = usize::max(field.as_usize() + 1, children.len());
                    children.resize(max, Node::owned(Ty::uninit()));
                }
                &mut children[field.as_usize()]
            }
            _ => unreachable!(),
        }
    }

    fn downcast(&mut self, genv: &GlobalEnv, rcx: &mut RefineCtxt, variant_idx: VariantIdx) {
        match self {
            Node::Leaf(Binding::Owned(ty)) => {
                if let TyKind::Indexed(BaseTy::Adt(adt_def, substs), idxs) = ty.kind() {
                    let fields = genv
                        .downcast(adt_def.def_id(), variant_idx, substs, &idxs.to_exprs())
                        .into_iter()
                        .map(|ty| Node::owned(rcx.unpack(&ty, false)))
                        .collect();
                    *self = Node::Internal(
                        NodeKind::Adt(adt_def.clone(), variant_idx, substs.clone()),
                        fields,
                    );
                } else {
                    panic!("type cannot be downcasted: `{ty:?}`")
                }
            }
            Node::Internal(NodeKind::Adt(_, variant_idx2, _), _) => {
                debug_assert_eq!(variant_idx, *variant_idx2);
            }
            Node::Internal(..) => panic!("invalid downcast"),
            Node::Leaf(..) => panic!("blocked"),
        }
    }

    fn split(&mut self, genv: &GlobalEnv, rcx: &mut RefineCtxt) {
        let ty = self.expect_owned();
        match ty.kind() {
            TyKind::Tuple(tys) => {
                let children = tys.iter().cloned().map(Node::owned).collect();
                *self = Node::Internal(NodeKind::Tuple, children);
            }
            TyKind::Indexed(BaseTy::Adt(def, ..), ..) if def.is_struct() => {
                self.downcast(genv, rcx, VariantIdx::from_u32(0));
            }
            TyKind::Uninit => *self = Node::Internal(NodeKind::Uninit, vec![]),
            _ => panic!("type cannot be split: `{ty:?}`"),
        }
    }

    fn fold(
        &mut self,
        map: &mut FxHashMap<Loc, NodePtr>,
        rcx: &mut RefineCtxt,
        gen: &mut ConstrGen,
        unblock: bool,
        close_boxes: bool,
    ) -> Ty {
        match self {
            Node::Leaf(Binding::Owned(ty)) => {
                if let TyKind::BoxPtr(loc, alloc) = ty.kind() && close_boxes {
                    let root = map.remove(&Loc::Free(*loc)).unwrap();
                    let boxed_ty = root.borrow_mut().fold(map, rcx, gen, unblock, close_boxes);
                    let ty = gen.genv.mk_box(boxed_ty, alloc.clone());
                    *self = Node::owned(ty.clone());
                    ty
                } else {
                    ty.clone()
                }
            }
            Node::Leaf(Binding::Blocked(ty)) => {
                if unblock {
                    let ty = rcx.unpack(ty, false);
                    *self = Node::owned(ty.clone());
                    ty
                } else {
                    panic!("I don't know what to do if you don't ask me to unblock.");
                }
            }
            Node::Internal(NodeKind::Tuple, children) => {
                let tys = children
                    .iter_mut()
                    .map(|node| node.fold(map, rcx, gen, unblock, close_boxes))
                    .collect_vec();
                let ty = Ty::tuple(tys);
                *self = Node::owned(ty.clone());
                ty
            }
            Node::Internal(NodeKind::Adt(adt_def, variant_idx, substs), children) => {
                let fn_sig = gen.genv.variant_sig(adt_def.def_id(), *variant_idx);
                let actuals = children
                    .iter_mut()
                    .map(|node| node.fold(map, rcx, gen, unblock, close_boxes))
                    .collect_vec();

                let partially_moved = actuals.iter().any(|ty| ty.is_uninit());
                if partially_moved {
                    *self = Node::owned(Ty::uninit());
                    Ty::uninit()
                } else {
                    let env = &mut FxHashMap::default();
                    let output = gen
                        .check_fn_call(rcx, env, &fn_sig, substs, &actuals)
                        .unwrap();
                    assert!(output.ensures.is_empty());
                    *self = Node::owned(output.ret.clone());
                    output.ret
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
            Binding::Owned(ty) => ty,
            Binding::Blocked(ty) => ty,
        }
    }

    fn is_uninit(&self) -> bool {
        match self {
            Binding::Owned(ty) => ty.is_uninit(),
            Binding::Blocked(ty) => ty.is_uninit(),
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
            Binding::Owned(ty) => ty.visit_with(visitor),
            Binding::Blocked(ty) => ty.visit_with(visitor),
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
