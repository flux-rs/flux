use std::iter;

use itertools::Itertools;

use rustc_hash::FxHashMap;

use liquid_rust_middle::{
    global_env::GlobalEnv,
    rustc::mir::{Field, Place, PlaceElem},
    ty::{fold::TypeFoldable, AdtDef, BaseTy, Loc, Path, RefKind, Substs, Ty, TyKind, VariantIdx},
};

use crate::{constraint_gen::ConstrGen, refine_tree::RefineCtxt};

#[derive(Clone, Default, Eq, PartialEq)]
pub struct PathsTree {
    map: FxHashMap<Loc, Node>,
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

    pub fn downcast(
        &mut self,
        genv: &GlobalEnv,
        rcx: &mut RefineCtxt,
        path: &Path,
        variant_idx: VariantIdx,
    ) {
        self.get_node_mut(path).downcast(genv, rcx, variant_idx);
    }

    pub fn get(&self, path: &Path) -> Ty {
        let mut node = self.map.get(&path.loc).unwrap();
        for f in path.projection() {
            match node {
                Node::Ty(_) => panic!("expected `Node::Adt`"),
                Node::Internal(.., children) => node = &children[f.as_usize()],
            }
        }
        match node {
            Node::Ty(ty) => ty.clone(),
            Node::Internal(..) => panic!("expcted `Node::Ty`"),
        }
    }

    pub fn update(&mut self, path: &Path, new_ty: Ty) {
        *self.get_node_mut(path).expect_ty_mut() = new_ty;
    }

    fn get_node_mut(&mut self, path: &Path) -> &mut Node {
        let mut node = self.map.get_mut(&path.loc).unwrap();
        for f in path.projection() {
            match node {
                Node::Ty(_) => panic!("expected `Node::Adt"),
                Node::Internal(.., children) => node = &mut children[f.as_usize()],
            }
        }
        node
    }

    pub fn insert(&mut self, loc: Loc, ty: Ty) {
        self.map.insert(loc, Node::Ty(ty));
    }

    pub fn remove(&mut self, loc: Loc) {
        self.map.remove(&loc);
    }

    pub fn locs(&self) -> impl Iterator<Item = Loc> + '_ {
        self.map.keys().copied()
    }

    pub fn contains_loc(&self, loc: Loc) -> bool {
        self.map.contains_key(&loc)
    }

    pub fn iter(&self) -> impl Iterator<Item = (Path, &Ty)> {
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
                        let ty = node.expect_ty();
                        match ty.kind() {
                            TyKind::Ptr(ptr_path) => {
                                path = ptr_path.clone();
                                continue 'outer;
                            }
                            TyKind::Ref(mode, ty) => {
                                return self.lookup_place_iter_ty(rcx, gen, *mode, ty, place_proj);
                            }
                            _ => panic!(),
                        }
                    }
                }
            }
            return LookupResult::Ptr(Path::new(loc, path_proj), node.fold(rcx, gen));
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
        let mut ty = ty.clone();
        while let Some(elem) = proj.next() {
            match (elem, ty.kind()) {
                (PlaceElem::Deref, TyKind::Ref(rk2, ty2)) => {
                    rk = rk.min(*rk2);
                    ty = ty2.clone();
                }
                (PlaceElem::Deref, TyKind::Ptr(ptr_path)) => {
                    return match self.lookup_place_iter(rcx, gen, ptr_path.clone(), proj) {
                        LookupResult::Ptr(_, ty2) => LookupResult::Ref(rk, ty2),
                        LookupResult::Ref(rk2, ty2) => LookupResult::Ref(rk.min(rk2), ty2),
                    }
                }
                (PlaceElem::Field(field), TyKind::Indexed(BaseTy::Adt(adt_def, substs), idxs)) => {
                    let fields = gen.genv.downcast(
                        adt_def.def_id(),
                        VariantIdx::from_u32(0),
                        substs,
                        &idxs.to_exprs(),
                    );
                    ty = fields[field.as_usize()].clone();
                }
                _ => unreachable!(),
            }
        }
        LookupResult::Ref(rk, ty)
    }

    #[must_use]
    pub fn fmap(&self, f: impl FnMut(&Ty) -> Ty) -> PathsTree {
        let mut tree = self.clone();
        tree.fmap_mut(f);
        tree
    }

    pub fn fmap_mut(&mut self, mut f: impl FnMut(&Ty) -> Ty) {
        let f = &mut f;
        for node in self.map.values_mut() {
            node.fmap_mut(f);
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
enum Node {
    Ty(Ty),
    Internal(NodeKind, Vec<Node>),
}

#[derive(Debug, Clone, Eq, PartialEq)]
enum NodeKind {
    Adt(AdtDef, VariantIdx, Substs),
    Tuple,
    Uninit,
}

impl Node {
    fn expect_ty(&self) -> Ty {
        match self {
            Node::Ty(ty) => ty.clone(),
            _ => panic!("expected type"),
        }
    }

    fn expect_ty_mut(&mut self) -> &mut Ty {
        match self {
            Node::Ty(ty) => ty,
            _ => panic!("expected type"),
        }
    }

    fn unfold_with(&mut self, genv: &GlobalEnv, rcx: &mut RefineCtxt, other: &mut Node) {
        match (&mut *self, &mut *other) {
            (Node::Ty(_), Node::Ty(_)) => {}
            (Node::Ty(_), Node::Internal(..)) => {
                self.uninit();
                self.split(genv, rcx);
                self.unfold_with(genv, rcx, other);
            }
            (Node::Internal(..), Node::Ty(_)) => {
                other.uninit();
                other.split(genv, rcx);
                self.unfold_with(genv, rcx, other);
            }
            (Node::Internal(_, children1), Node::Internal(_, children2)) => {
                let max = usize::max(children1.len(), children2.len());
                children1.resize(max, Node::Ty(Ty::uninit()));
                children2.resize(max, Node::Ty(Ty::uninit()));
                for (node1, node2) in iter::zip(children1, children2) {
                    node1.unfold_with(genv, rcx, node2);
                }
            }
        };
    }

    fn proj(&mut self, genv: &GlobalEnv, rcx: &mut RefineCtxt, field: Field) -> &mut Node {
        if let Node::Ty(_) = self {
            self.split(genv, rcx);
        }
        match self {
            Node::Internal(NodeKind::Adt(..) | NodeKind::Uninit, children) => {
                let max = usize::max(field.as_usize() + 1, children.len());
                children.resize(max, Node::Ty(Ty::uninit()));
                &mut children[field.as_usize()]
            }
            _ => unreachable!(),
        }
    }

    fn downcast(&mut self, genv: &GlobalEnv, rcx: &mut RefineCtxt, variant_idx: VariantIdx) {
        match self {
            Node::Ty(ty) => {
                if let TyKind::Indexed(BaseTy::Adt(adt_def, substs), idxs) = ty.kind() {
                    let fields = genv
                        .downcast(adt_def.def_id(), variant_idx, substs, &idxs.to_exprs())
                        .into_iter()
                        .map(|ty| Node::Ty(rcx.unpack(&ty, false)))
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
        }
    }

    fn split(&mut self, genv: &GlobalEnv, rcx: &mut RefineCtxt) {
        let ty = self.expect_ty();
        match ty.kind() {
            TyKind::Tuple(tys) => {
                let children = tys.iter().cloned().map(Node::Ty).collect();
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
        *self = Node::Ty(Ty::uninit());
    }

    fn fold(&mut self, rcx: &mut RefineCtxt, gen: &mut ConstrGen) -> Ty {
        match self {
            Node::Ty(ty) => ty.clone(),
            Node::Internal(NodeKind::Tuple, children) => {
                let tys = children
                    .iter_mut()
                    .map(|node| node.fold(rcx, gen))
                    .collect_vec();
                let ty = Ty::tuple(tys);
                *self = Node::Ty(ty.clone());
                ty
            }
            Node::Internal(NodeKind::Adt(adt_def, variant_idx, substs), children) => {
                let fn_sig = gen.genv.variant_sig(adt_def.def_id(), *variant_idx);
                let actuals = children
                    .iter_mut()
                    .map(|node| node.fold(rcx, gen))
                    .collect_vec();
                let env = &mut FxHashMap::default();
                let output = gen
                    .check_fn_call(rcx, env, &fn_sig, substs, &actuals)
                    .unwrap();
                assert!(output.ensures.is_empty());
                *self = Node::Ty(output.ret.clone());
                output.ret
            }
            Node::Internal(NodeKind::Uninit, _) => {
                *self = Node::Ty(Ty::uninit());
                Ty::uninit()
            }
        }
    }

    fn fmap_mut(&mut self, f: &mut impl FnMut(&Ty) -> Ty) {
        match self {
            Node::Ty(ty) => *ty = f(ty),
            Node::Internal(.., fields) => {
                for field in fields {
                    field.fmap_mut(f);
                }
            }
        }
    }
}

enum PathsIter<'a> {
    Adt {
        stack: Vec<std::iter::Enumerate<std::slice::Iter<'a, Node>>>,
        loc: Loc,
        projection: Vec<Field>,
    },
    Ty(Option<(Loc, &'a Ty)>),
}

impl<'a> PathsIter<'a> {
    fn new(loc: Loc, root: &'a Node) -> Self {
        match root {
            Node::Ty(ty) => PathsIter::Ty(Some((loc, ty))),
            Node::Internal(.., fields) => {
                PathsIter::Adt { loc, projection: vec![], stack: vec![fields.iter().enumerate()] }
            }
        }
    }
}

impl<'a> Iterator for PathsIter<'a> {
    type Item = (Path, &'a Ty);

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
                            Node::Ty(ty) => {
                                projection.push(Field::from(i));
                                let path = Path::new(*loc, projection.as_slice());
                                projection.pop();
                                return Some((path, ty));
                            }
                        }
                    } else {
                        projection.pop();
                        stack.pop();
                    }
                }
                None
            }
            PathsIter::Ty(item) => item.take().map(|(loc, ty)| (Path::new(loc, vec![]), ty)),
        }
    }
}

mod pretty {
    use super::*;
    use itertools::Itertools;
    use liquid_rust_middle::pretty::*;
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
                    .format_with(", ", |(loc, ty), f| f(&format_args_cx!("{:?}: {:?}", loc, ty)))
            )
        }
    }
}
