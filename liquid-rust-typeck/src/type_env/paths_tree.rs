use std::hint::unreachable_unchecked;

use itertools::Itertools;
use liquid_rust_common::{index::IndexVec, iter::IterExt};
use liquid_rust_core::ir::{Field, Place, PlaceElem};
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;

use crate::{
    global_env::GlobalEnv,
    subst::Subst,
    ty::{BaseTy, Loc, Path, Ty, TyKind},
};

#[derive(Debug, Clone, Default, Eq, PartialEq)]
pub struct PathsTree {
    map: FxHashMap<Loc, Node>,
}

impl PathsTree {
    pub fn lookup_place<M, F, R>(&mut self, mode: M, genv: &GlobalEnv, place: &Place, f: F) -> R
    where
        M: LookupMode,
        F: for<'a> FnOnce(M::Result<'a>) -> R,
    {
        self.place_proj_iter(mode, genv, Loc::Local(place.local), &mut place.projection.iter(), f)
    }

    pub fn get(&self, path: &Path) -> Option<&Ty> {
        let mut node = self.map.get(&path.loc)?;
        for f in path.projection() {
            match node {
                Node::Ty(_) => return None,
                Node::Adt(_, fields) => node = &fields[*f],
            }
        }
        match node {
            Node::Ty(ty) => Some(ty),
            Node::Adt(_, _) => None,
        }
    }

    pub fn get_mut(&mut self, path: &Path) -> Option<&mut Ty> {
        let mut node = self.map.get_mut(&path.loc)?;
        for f in path.projection() {
            match node {
                Node::Ty(_) => return None,
                Node::Adt(_, fields) => node = &mut fields[*f],
            }
        }
        match node {
            Node::Ty(ty) => Some(ty),
            Node::Adt(_, _) => None,
        }
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

    pub fn iter_mut(&mut self) -> impl Iterator<Item = (Path, &mut Ty)> {
        self.map
            .iter_mut()
            .flat_map(|(loc, node)| PathsIterMut::new(*loc, node))
    }

    pub fn values_mut(&mut self) -> impl Iterator<Item = &mut Ty> {
        self.iter_mut().map(|(_, ty)| ty)
    }

    pub fn subst(self, subst: &Subst) -> Self {
        let map = self
            .map
            .into_iter()
            .map(|(loc, mut node)| {
                node.subst_mut(subst);
                (subst.subst_loc(loc), node)
            })
            .collect();
        PathsTree { map }
    }

    fn place_proj_iter<M, R, F>(
        &mut self,
        _mode: M,
        genv: &GlobalEnv,
        mut loc: Loc,
        proj: &mut std::slice::Iter<PlaceElem>,
        f: F,
    ) -> R
    where
        M: LookupMode,
        F: for<'a> FnOnce(M::Result<'a>) -> R,
    {
        loop {
            let mut node = self.map.get_mut(&loc).unwrap();
            for f in proj.map_take_while(|p| PlaceElem::as_field(p)) {
                node = &mut node.unfold(genv)[f];
            }
            let ty = node.fold(genv);

            match (proj.next(), ty.kind()) {
                (Some(PlaceElem::Deref), TyKind::StrgRef(ref_loc)) => loc = *ref_loc,
                (Some(PlaceElem::Deref), TyKind::ShrRef(ty) | TyKind::WeakRef(ty)) => {
                    let ty = ty.clone();
                    return f(M::place_proj_ty(self, genv, &ty, proj));
                }
                (Some(PlaceElem::Deref), _) => {
                    unreachable!("type cannot be dereferenced: `{ty:?}`")
                }
                (Some(_), _) => unreachable!("expected deref"),
                (None, _) => return f(M::to_result(ty)),
            }
        }
    }
}

impl<'a> std::ops::Index<&'a Path> for PathsTree {
    type Output = Ty;

    fn index(&self, path: &'a Path) -> &Self::Output {
        match self.get(path) {
            Some(ty) => ty,
            None => panic!("no entry found for path `{:?}`", path),
        }
    }
}

impl<'a> std::ops::IndexMut<&'a Path> for PathsTree {
    fn index_mut(&mut self, path: &'a Path) -> &mut Self::Output {
        match self.get_mut(path) {
            Some(ty) => ty,
            None => panic!("no entry found for path `{:?}`", path),
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
enum Node {
    Ty(Ty),
    Adt(DefId, IndexVec<Field, Node>),
}

impl Node {
    fn unfold(&mut self, genv: &GlobalEnv) -> &mut IndexVec<Field, Node> {
        match self {
            Node::Ty(ty) => {
                let (did, fields) = ty.unfold(genv);

                *self = Node::Adt(did, fields.into_iter().map(Node::Ty).collect());
                if let Node::Adt(_, fields) = self {
                    fields
                } else {
                    unsafe { unreachable_unchecked() }
                }
            }
            Node::Adt(_, fields) => fields,
        }
    }

    fn fold(&mut self, genv: &GlobalEnv) -> &mut Ty {
        match self {
            Node::Ty(ty) => ty,
            Node::Adt(did, fields) => {
                let adt_def = genv.adt_def(*did);
                let fields = fields
                    .iter_mut()
                    .map(|n| n.fold(genv).clone())
                    .collect_vec();
                let e = adt_def.fold(&fields);

                *self = Node::Ty(Ty::refine(BaseTy::adt(*did, []), e));
                if let Node::Ty(ty) = self {
                    ty
                } else {
                    unsafe { unreachable_unchecked() }
                }
            }
        }
    }

    pub fn subst_mut(&mut self, subst: &Subst) {
        match self {
            Node::Ty(ty) => *ty = subst.subst_ty(ty),
            Node::Adt(_, fields) => {
                for field in fields.iter_mut() {
                    field.subst_mut(subst);
                }
            }
        }
    }
}

pub trait LookupMode {
    type Result<'a>;

    fn to_result(ty: &mut Ty) -> Self::Result<'_>;

    fn place_proj_ty<'a>(
        paths: &'a mut PathsTree,
        genv: &GlobalEnv,
        ty: &Ty,
        proj: &mut std::slice::Iter<PlaceElem>,
    ) -> Self::Result<'a>;
}

pub struct Read;

pub struct Write;

impl LookupMode for Read {
    type Result<'a> = Ty;

    fn to_result(ty: &mut Ty) -> Ty {
        ty.clone()
    }

    fn place_proj_ty<'a>(
        paths: &'a mut PathsTree,
        genv: &GlobalEnv,
        ty: &Ty,
        proj: &mut std::slice::Iter<PlaceElem>,
    ) -> Ty {
        let mut ty = ty.clone();
        while let Some(elem) = proj.next() {
            match (elem, ty.kind()) {
                (PlaceElem::Deref, TyKind::ShrRef(ref_ty) | TyKind::WeakRef(ref_ty)) => {
                    ty = ref_ty.clone();
                }
                (PlaceElem::Deref, TyKind::StrgRef(loc)) => {
                    return paths.place_proj_iter(Read, genv, *loc, proj, |ty| ty);
                }
                (PlaceElem::Field(f), _) => {
                    let (_, fields) = ty.unfold(genv);
                    ty = fields[*f].clone()
                }
                _ => unreachable!(),
            }
        }
        ty
    }
}

impl LookupMode for Write {
    type Result<'a> = &'a mut Ty;

    fn to_result(ty: &mut Ty) -> &mut Ty {
        ty
    }

    fn place_proj_ty<'a>(
        _paths: &'a mut PathsTree,
        _genv: &GlobalEnv,
        _ty: &Ty,
        _proj: &mut std::slice::Iter<PlaceElem>,
    ) -> &'a mut Ty {
        panic!()
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
            Node::Adt(_, fields) => {
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
                            Node::Adt(_, fields) => {
                                projection.push(Field::from(i));
                                stack.push(fields.iter().enumerate());
                            }
                            Node::Ty(ty) => {
                                projection.push(Field::from(i));
                                let path = Path::new(*loc, projection);
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
            PathsIter::Ty(item) => item.take().map(|(loc, ty)| (Path::new(loc, &[]), ty)),
        }
    }
}

enum PathsIterMut<'a> {
    Adt {
        stack: Vec<std::iter::Enumerate<std::slice::IterMut<'a, Node>>>,
        loc: Loc,
        projection: Vec<Field>,
    },
    Ty(Option<(Loc, &'a mut Ty)>),
}

impl<'a> PathsIterMut<'a> {
    fn new(loc: Loc, root: &'a mut Node) -> Self {
        match root {
            Node::Ty(ty) => PathsIterMut::Ty(Some((loc, ty))),
            Node::Adt(_, fields) => {
                PathsIterMut::Adt {
                    loc,
                    projection: vec![],
                    stack: vec![fields.iter_mut().enumerate()],
                }
            }
        }
    }
}

impl<'a> Iterator for PathsIterMut<'a> {
    type Item = (Path, &'a mut Ty);

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            PathsIterMut::Adt { stack, loc, projection } => {
                while let Some(top) = stack.last_mut() {
                    if let Some((i, node)) = top.next() {
                        match node {
                            Node::Adt(_, fields) => {
                                projection.push(Field::from(i));
                                stack.push(fields.iter_mut().enumerate());
                            }
                            Node::Ty(ty) => {
                                projection.push(Field::from(i));
                                let path = Path::new(*loc, projection);
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
            PathsIterMut::Ty(item) => item.take().map(|(loc, ty)| (Path::new(loc, &[]), ty)),
        }
    }
}
