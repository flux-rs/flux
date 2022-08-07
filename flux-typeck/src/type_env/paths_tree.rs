use std::iter;

use itertools::Itertools;

use rustc_hash::FxHashMap;

use flux_middle::{
    global_env::GlobalEnv,
    rustc::mir::{Field, Place, PlaceElem},
    ty::{
        fold::{TypeFoldable, TypeFolder, TypeVisitor},
        AdtDef, BaseTy, Loc, Path, RefKind, Substs, Ty, TyKind, VariantIdx,
    },
};

use crate::{constraint_gen::ConstrGen, refine_tree::RefineCtxt};

#[derive(Clone, Default, Eq, PartialEq)]
pub struct PathsTree {
    map: FxHashMap<Loc, Node>,
}

pub enum LookupResult {
    Ptr(Path, Ty),
    Ref(RefKind, Ty),
    Box(Ty),
}

impl LookupResult {
    pub fn ty(&self) -> Ty {
        match self {
            LookupResult::Ptr(_, ty) => ty.clone(),
            LookupResult::Ref(_, ty) => ty.clone(),
            LookupResult::Box(ty) => ty.clone(),
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
        self.lookup_place_iter(rcx, gen, path.loc, &mut proj)
    }

    pub fn get(&self, path: &Path) -> Binding {
        let mut node = self.map.get(&path.loc).unwrap();
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
        *self.get_node_mut(path) = Node::Leaf(binding);
    }

    pub fn update(&mut self, path: &Path, new_ty: Ty) {
        *self.get_node_mut(path).expect_owned_mut() = new_ty;
    }

    pub fn block(&mut self, path: &Path) {
        let node = self.get_node_mut(path);
        match node {
            Node::Leaf(Binding::Owned(ty)) => *node = Node::Leaf(Binding::Blocked(ty.clone())),
            _ => panic!("expected owned binding"),
        }
    }

    fn get_node_mut(&mut self, path: &Path) -> &mut Node {
        let mut node = self.map.get_mut(&path.loc).unwrap();
        for f in path.projection() {
            match node {
                Node::Leaf(_) => panic!("expected `Node::Adt"),
                Node::Internal(.., children) => node = &mut children[f.as_usize()],
            }
        }
        node
    }

    pub fn insert(&mut self, loc: Loc, ty: Ty) {
        self.map.insert(loc, Node::owned(ty));
    }

    pub fn contains_loc(&self, loc: Loc) -> bool {
        self.map.contains_key(&loc)
    }

    pub fn iter(&self) -> impl Iterator<Item = (Path, &Binding)> {
        self.map
            .iter()
            .flat_map(|(loc, node)| PathsIter::new(*loc, node))
    }

    pub fn paths(&self) -> impl Iterator<Item = Path> + '_ {
        self.iter().map(|(path, _)| path)
    }

    pub fn unfold_with(&mut self, genv: &GlobalEnv, rcx: &mut RefineCtxt, other: &mut PathsTree) {
        for (loc, node1) in &mut self.map {
            if let Some(node2) = other.map.get_mut(loc) {
                node1.unfold_with(genv, rcx, node2);
            }
        }
    }

    fn lookup_place_iter(
        &mut self,
        rcx: &mut RefineCtxt,
        gen: &mut ConstrGen,
        path: impl Into<Path>,
        place_proj: &mut impl Iterator<Item = PlaceElem>,
    ) -> LookupResult {
        let mut path = path.into();
        'outer: loop {
            let loc = path.loc;
            let mut path_proj = vec![];

            let mut node = self.map.get_mut(&loc).unwrap();

            for field in path.projection() {
                node = node.proj(gen.genv, rcx, *field);
                path_proj.push(*field);
            }

            while let Some(elem) = place_proj.next() {
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
                            TyKind::Ref(mode, ty) => {
                                return self.lookup_place_iter_ty(rcx, gen, *mode, ty, place_proj);
                            }
                            TyKind::Indexed(BaseTy::Adt(def, substs), _)
                            | TyKind::Exists(BaseTy::Adt(def, substs), _)
                                if def.is_box() =>
                            {
                                return LookupResult::Box(substs[0].clone());
                            }
                            _ => panic!("Unsupported Deref: {elem:?} {ty:?}"),
                        }
                    }
                }
            }
            return LookupResult::Ptr(Path::new(loc, path_proj), node.fold(rcx, gen, true));
        }
    }

    fn lookup_place_iter_ty(
        &mut self,
        rcx: &mut RefineCtxt,
        gen: &mut ConstrGen,
        mut rk: RefKind,
        ty: &Ty,
        proj: &mut impl Iterator<Item = PlaceElem>,
    ) -> LookupResult {
        use PlaceElem::*;
        let mut ty = ty.clone();
        while let Some(elem) = proj.next() {
            match (elem, ty.kind()) {
                (Deref, TyKind::Ref(rk2, ty2)) => {
                    rk = rk.min(*rk2);
                    ty = ty2.clone();
                }
                (Deref, TyKind::Ptr(ptr_path)) => {
                    return match self.lookup_place_iter(rcx, gen, ptr_path.clone(), proj) {
                        LookupResult::Ptr(_, ty2) => LookupResult::Ref(rk, ty2),
                        LookupResult::Ref(rk2, ty2) => LookupResult::Ref(rk.min(rk2), ty2),
                        LookupResult::Box(ty2) => LookupResult::Ref(rk, ty2),
                    }
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

    #[must_use]
    pub fn fmap(&self, f: impl FnMut(&Binding) -> Binding) -> PathsTree {
        let mut tree = self.clone();
        tree.fmap_mut(f);
        tree
    }

    pub fn fmap_mut(&mut self, mut f: impl FnMut(&Binding) -> Binding) {
        for node in self.map.values_mut() {
            node.fmap_mut(&mut f);
        }
    }
}

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

    fn unfold_with(&mut self, genv: &GlobalEnv, rcx: &mut RefineCtxt, other: &mut Node) {
        match (&mut *self, &mut *other) {
            (Node::Leaf(_), Node::Leaf(_)) => {}
            (Node::Leaf(_), Node::Internal(..)) => {
                self.uninit();
                self.split(genv, rcx);
                self.unfold_with(genv, rcx, other);
            }
            (Node::Internal(..), Node::Leaf(_)) => {
                other.uninit();
                other.split(genv, rcx);
                self.unfold_with(genv, rcx, other);
            }
            (Node::Internal(_, children1), Node::Internal(_, children2)) => {
                let max = usize::max(children1.len(), children2.len());
                children1.resize(max, Node::owned(Ty::uninit()));
                children2.resize(max, Node::owned(Ty::uninit()));
                for (node1, node2) in iter::zip(children1, children2) {
                    node1.unfold_with(genv, rcx, node2);
                }
            }
        };
    }

    fn proj(&mut self, genv: &GlobalEnv, rcx: &mut RefineCtxt, field: Field) -> &mut Node {
        if let Node::Leaf(_) = self {
            self.split(genv, rcx);
        }
        match self {
            Node::Internal(NodeKind::Adt(..) | NodeKind::Uninit, children) => {
                let max = usize::max(field.as_usize() + 1, children.len());
                children.resize(max, Node::owned(Ty::uninit()));
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
                    let substs = substs.with_holes();
                    *self =
                        Node::Internal(NodeKind::Adt(adt_def.clone(), variant_idx, substs), fields);
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
            // TODO(nilehmann) we should check here whether this is a struct and not an enum
            TyKind::Indexed(BaseTy::Adt(..), ..) => {
                self.downcast(genv, rcx, VariantIdx::from_u32(0));
            }
            TyKind::Uninit => *self = Node::Internal(NodeKind::Uninit, vec![]),
            _ => panic!("type cannot be split: `{ty:?}`"),
        }
    }

    fn uninit(&mut self) {
        *self = Node::owned(Ty::uninit());
    }

    // NOTE(nilehmann) The extra `unblock` parameter is there on purpose to force future clients of
    // this function to think harder about whether it should simply unblock bindings. Right now it's
    // being used in a single place with `unblock = true`.
    fn fold(&mut self, rcx: &mut RefineCtxt, gen: &mut ConstrGen, unblock: bool) -> Ty {
        match self {
            Node::Leaf(Binding::Owned(ty)) => ty.clone(),
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
                    .map(|node| node.fold(rcx, gen, unblock))
                    .collect_vec();
                let ty = Ty::tuple(tys);
                *self = Node::owned(ty.clone());
                ty
            }
            Node::Internal(NodeKind::Adt(adt_def, variant_idx, substs), children) => {
                let fn_sig = gen.genv.variant_sig(adt_def.def_id(), *variant_idx);
                let actuals = children
                    .iter_mut()
                    .map(|node| node.fold(rcx, gen, unblock))
                    .collect_vec();
                let env = &mut FxHashMap::default();
                let output = gen
                    .check_fn_call(rcx, env, &fn_sig, substs, &actuals)
                    .unwrap();
                assert!(output.ensures.is_empty());
                *self = Node::owned(output.ret.clone());
                output.ret
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

enum PathsIter<'a> {
    Adt {
        stack: Vec<std::iter::Enumerate<std::slice::Iter<'a, Node>>>,
        loc: Loc,
        projection: Vec<Field>,
    },
    Leaf(Option<(Loc, &'a Binding)>),
}

impl<'a> PathsIter<'a> {
    fn new(loc: Loc, root: &'a Node) -> Self {
        match root {
            Node::Leaf(binding) => PathsIter::Leaf(Some((loc, binding))),
            Node::Internal(.., fields) => {
                PathsIter::Adt { loc, projection: vec![], stack: vec![fields.iter().enumerate()] }
            }
        }
    }
}

impl<'a> Iterator for PathsIter<'a> {
    type Item = (Path, &'a Binding);

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            PathsIter::Adt { stack, loc, projection } => {
                while let Some(top) = stack.last_mut() {
                    if let Some((i, node)) = top.next() {
                        match node {
                            Node::Internal(.., fields) => {
                                projection.push(Field::from(i));
                                stack.push(fields.iter().enumerate());
                            }
                            Node::Leaf(binding) => {
                                projection.push(Field::from(i));
                                let path = Path::new(*loc, projection.as_slice());
                                projection.pop();
                                return Some((path, binding));
                            }
                        }
                    } else {
                        projection.pop();
                        stack.pop();
                    }
                }
                None
            }
            PathsIter::Leaf(item) => item.take().map(|(loc, ty)| (Path::new(loc, vec![]), ty)),
        }
    }
}

mod pretty {
    use super::*;
    use flux_middle::pretty::*;
    use itertools::Itertools;
    use std::fmt;

    impl Pretty for PathsTree {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            let bindings = self
                .iter()
                .filter(|(_, ty)| !cx.hide_uninit || !ty.is_uninit())
                .sorted_by(|(path1, _), (path2, _)| path1.cmp(path2))
                .collect_vec();
            w!(
                "{{{}}}",
                ^bindings
                    .into_iter()
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
