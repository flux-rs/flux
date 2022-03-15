use std::{hint::unreachable_unchecked, iter};

use itertools::Itertools;
use liquid_rust_common::{index::IndexVec, iter::IterExt};
use liquid_rust_core::ir::{Field, Place, PlaceElem};
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;

use crate::{
    global_env::GlobalEnv,
    pure_ctxt::PureCtxt,
    subst::Subst,
    ty::{AdtDef, BaseTy, Expr, ExprKind, Loc, Name, Path, Ty, TyKind, Var},
};

#[derive(Debug, Clone, Default, Eq, PartialEq)]
pub struct PathsTree {
    map: FxHashMap<Loc, Node>,
}

pub enum LookupResult<'a> {
    Strg(&'a mut Ty),
    Shr(Ty),
    Weak(Ty),
}

impl LookupResult<'_> {
    pub fn ty(&self) -> Ty {
        match self {
            LookupResult::Strg(ty) => (*ty).clone(),
            LookupResult::Shr(ty) | LookupResult::Weak(ty) => ty.clone(),
        }
    }
}

impl PathsTree {
    pub fn lookup_place<F, R>(
        &mut self,
        genv: &GlobalEnv,
        pcx: &mut PureCtxt,
        place: &Place,
        f: F,
    ) -> R
    where
        F: for<'a> FnOnce(&mut PureCtxt, Path, LookupResult<'a>) -> R,
    {
        self.lookup_place_iter(
            genv,
            pcx,
            Loc::Local(place.local),
            &mut vec![],
            &mut place.projection.iter(),
            f,
        )
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

    pub fn unfold_with(&mut self, genv: &GlobalEnv, other: &mut PathsTree) {
        for (loc, node1) in &mut self.map {
            if let Some(node2) = other.map.get_mut(loc) {
                node1.unfold_with(genv, node2);
            }
        }
    }

    pub fn fold_unfold_to_match(
        &mut self,
        genv: &GlobalEnv,
        pcx: &mut PureCtxt,
        other: &PathsTree,
    ) {
        for (loc, node1) in &mut self.map {
            if let Some(node2) = other.map.get(loc) {
                node1.fold_unfold_to_match(genv, pcx, node2);
            }
        }
    }

    fn lookup_place_iter<R, F>(
        &mut self,
        genv: &GlobalEnv,
        pcx: &mut PureCtxt,
        mut loc: Loc,
        path: &mut Vec<Field>,
        proj: &mut std::slice::Iter<PlaceElem>,
        f: F,
    ) -> R
    where
        F: for<'a> FnOnce(&mut PureCtxt, Path, LookupResult<'a>) -> R,
    {
        loop {
            let mut node = self.map.get_mut(&loc).unwrap();
            for f in proj.map_take_while(|p| PlaceElem::as_field(p)) {
                path.push(f);
                node = &mut node.unfold(genv)[f];
            }
            let ty = node.fold(genv, pcx);

            match proj.next() {
                Some(PlaceElem::Deref) => {
                    path.clear();
                    match ty.kind() {
                        TyKind::StrgRef(ref_loc) => loc = *ref_loc,
                        TyKind::ShrRef(ty) => {
                            let ty = ty.clone();
                            let (path, result) =
                                self.place_proj_ty(genv, pcx, false, &ty, loc, path, proj);
                            return f(pcx, path, result);
                        }
                        TyKind::WeakRef(ty) => {
                            let ty = ty.clone();
                            let (path, result) =
                                self.place_proj_ty(genv, pcx, true, &ty, loc, path, proj);
                            return f(pcx, path, result);
                        }
                        _ => unreachable!("type cannot be dereferenced `{ty:?}`"),
                    }
                }
                Some(_) => unreachable!("expected deref"),
                None => return f(pcx, Path::new(loc, &path[..]), LookupResult::Strg(ty)),
            }
        }
    }

    fn place_proj_ty<'a>(
        &mut self,
        genv: &GlobalEnv,
        pcx: &mut PureCtxt,
        mut weak: bool,
        ty: &Ty,
        loc: Loc,
        path: &mut Vec<Field>,
        proj: &mut std::slice::Iter<PlaceElem>,
    ) -> (Path, LookupResult<'a>) {
        let mut ty = ty.clone();
        while let Some(elem) = proj.next() {
            match (elem, ty.kind()) {
                (PlaceElem::Deref, TyKind::ShrRef(ref_ty)) => {
                    weak = false;
                    path.clear();
                    ty = ref_ty.clone();
                }
                (PlaceElem::Deref, TyKind::WeakRef(ref_ty)) => {
                    path.clear();
                    ty = ref_ty.clone();
                }
                (PlaceElem::Deref, TyKind::StrgRef(loc)) => {
                    path.clear();
                    return self.lookup_place_iter(
                        genv,
                        pcx,
                        *loc,
                        path,
                        proj,
                        |_, path, lookup| {
                            let ty = match lookup {
                                LookupResult::Strg(ty) => ty.clone(),
                                LookupResult::Shr(ty) | LookupResult::Weak(ty) => ty,
                            };
                            if weak {
                                (path, LookupResult::Weak(ty))
                            } else {
                                (path, LookupResult::Shr(ty))
                            }
                        },
                    );
                }
                (PlaceElem::Field(f), _) => {
                    path.push(*f);
                    let (_, fields) = ty.unfold(genv);
                    ty = fields[*f].clone();
                }
                _ => unreachable!(),
            }
        }
        if weak {
            (Path::new(loc, &path[..]), LookupResult::Weak(ty))
        } else {
            (Path::new(loc, &path[..]), LookupResult::Shr(ty))
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
    fn unfold_with(&mut self, genv: &GlobalEnv, other: &mut Node) {
        let (fields1, fields2) = match (&mut *self, &mut *other) {
            (Node::Ty(_), Node::Ty(_)) => return,
            (Node::Ty(_), Node::Adt(_, fields2)) => (self.unfold(genv), fields2),
            (Node::Adt(_, fields1), Node::Ty(_)) => (fields1, other.unfold(genv)),
            (Node::Adt(_, fields1), Node::Adt(_, fields2)) => (fields1, fields2),
        };
        debug_assert_eq!(fields1.len(), fields2.len());
        for (field1, field2) in fields1.iter_mut().zip(fields2.iter_mut()) {
            field1.unfold_with(genv, field2);
        }
    }

    fn fold_unfold_to_match(&mut self, genv: &GlobalEnv, pcx: &mut PureCtxt, other: &Node) {
        let (fields1, fields2) = match (&mut *self, other) {
            (Node::Ty(_), Node::Ty(_)) => return,
            (Node::Adt(_, _), Node::Ty(_)) => {
                self.fold(genv, pcx);
                return;
            }
            (Node::Ty(_), Node::Adt(_, fields2)) => (self.unfold(genv), fields2),
            (Node::Adt(_, fields1), Node::Adt(_, fields2)) => (fields1, fields2),
        };
        debug_assert_eq!(fields1.len(), fields2.len());
        for (field1, field2) in fields1.iter_mut().zip(fields2) {
            field1.fold_unfold_to_match(genv, pcx, field2);
        }
    }

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

    fn fold(&mut self, genv: &GlobalEnv, pcx: &mut PureCtxt) -> &mut Ty {
        match self {
            Node::Ty(ty) => ty,
            Node::Adt(did, fields) => {
                let fields = fields
                    .iter_mut()
                    .map(|n| n.fold(genv, pcx).clone())
                    .collect_vec();
                let adt_def = genv.adt_def(*did);
                let exprs = fold(genv, pcx, adt_def, &fields[..]);
                let adt = BaseTy::adt(*did, vec![]);
                let ty = Ty::refine(adt, exprs);
                *self = Node::Ty(ty);
                if let Node::Ty(ty) = self {
                    ty
                } else {
                    unsafe { unreachable_unchecked() }
                }
            }
        }
    }

    fn subst_mut(&mut self, subst: &Subst) {
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

type ParamInst = FxHashMap<Name, Expr>;

fn fold(genv: &GlobalEnv, pcx: &mut PureCtxt, adt_def: &AdtDef, tys: &[Ty]) -> Vec<Expr> {
    match adt_def {
        AdtDef::Transparent { refined_by, fields } => {
            let mut params = FxHashMap::default();
            for (ty1, ty2) in iter::zip(tys, fields) {
                ty_infer_folding(genv, pcx, &mut params, ty1, ty2);
            }
            refined_by
                .iter()
                .map(|param| params.remove(&param.name).unwrap())
                .collect()
        }
        AdtDef::Opaque { .. } => panic!("folding opaque adt"),
    }
}

fn ty_infer_folding(
    genv: &GlobalEnv,
    pcx: &mut PureCtxt,
    params: &mut ParamInst,
    ty1: &Ty,
    ty2: &Ty,
) {
    match (ty1.kind(), ty2.kind()) {
        (TyKind::Refine(bty1, exprs1), TyKind::Refine(bty2, exprs2)) => {
            bty_infer_folding(genv, pcx, params, bty1, bty2);
            for (e1, e2) in iter::zip(exprs1, exprs2) {
                expr_infer_folding(params, e1, e2);
            }
        }
        (TyKind::Exists(bty1, p), TyKind::Refine(bty2, exprs2)) => {
            bty_infer_folding(genv, pcx, params, bty1, bty2);
            let sorts = genv.sorts(bty1);
            let exprs1 = pcx.push_bindings(&sorts, p);
            for (e1, e2) in iter::zip(exprs1, exprs2) {
                expr_infer_folding(params, &e1, e2)
            }
        }
        (TyKind::Exists(..), TyKind::Exists(..)) => todo!(),
        (TyKind::Refine(..), TyKind::Exists(..)) => todo!(),
        (TyKind::StrgRef(_), TyKind::StrgRef(Loc::Abstract(_))) => {
            todo!()
        }
        (TyKind::ShrRef(ty1), TyKind::ShrRef(ty2)) => {
            ty_infer_folding(genv, pcx, params, ty1, ty2);
        }
        _ => {}
    }
}

fn bty_infer_folding(
    genv: &GlobalEnv,
    pcx: &mut PureCtxt,
    params: &mut ParamInst,
    bty1: &BaseTy,
    bty2: &BaseTy,
) {
    if let (BaseTy::Adt(did1, substs1), BaseTy::Adt(did2, substs2)) = (bty1, bty2) {
        debug_assert_eq!(did1, did2);
        debug_assert_eq!(substs1.len(), substs2.len());
        for (ty1, ty2) in iter::zip(substs1, substs2) {
            ty_infer_folding(genv, pcx, params, ty1, ty2);
        }
    }
}

fn expr_infer_folding(params: &mut ParamInst, e1: &Expr, e2: &Expr) {
    match (e1.kind(), e2.kind()) {
        (_, ExprKind::Var(Var::Free(name))) => {
            match params.insert(*name, e1.clone()) {
                Some(old_e) => {
                    if &old_e != e2 {
                        todo!(
                            "ambiguous instantiation for parameter: {:?} -> [{:?}, {:?}]",
                            *name,
                            old_e,
                            e1
                        )
                    }
                }
                None => {}
            }
        }
        (ExprKind::Tuple(exprs1), ExprKind::Tuple(exprs2)) => {
            debug_assert_eq!(exprs1.len(), exprs2.len());
            for (e1, e2) in exprs1.iter().zip(exprs2) {
                expr_infer_folding(params, e1, e2);
            }
        }
        _ => {}
    }
}

pub trait LookupMode {
    type Result<'a>;

    fn to_result(ty: &mut Ty) -> Self::Result<'_>;

    fn place_proj_ty<'a>(
        paths: &'a mut PathsTree,
        genv: &GlobalEnv,
        pcx: &mut PureCtxt,
        ty: &Ty,
        loc: Loc,
        path: &mut Vec<Field>,
        proj: &mut std::slice::Iter<PlaceElem>,
    ) -> (Path, Self::Result<'a>);
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
            PathsIterMut::Ty(item) => item.take().map(|(loc, ty)| (Path::new(loc, vec![]), ty)),
        }
    }
}
