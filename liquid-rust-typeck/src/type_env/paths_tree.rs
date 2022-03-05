use std::hint::unreachable_unchecked;

use itertools::Itertools;
use liquid_rust_common::{index::IndexVec, iter::IterExt};
use liquid_rust_core::ir::{Field, Place, PlaceElem};
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;

use crate::{
    global_env::GlobalEnv,
    ty::{BaseTy, Loc, Ty, TyKind},
};

pub struct PathsTree {
    map: FxHashMap<Loc, Node>,
}

impl PathsTree {
    pub fn lookup_place(&mut self, genv: &GlobalEnv, place: &Place) -> Ty {
        self.place_proj(Read, genv, Loc::Local(place.local), &mut place.projection.iter(), |ty| ty)
    }

    pub fn update_place(&mut self, genv: &GlobalEnv, place: &Place, new_ty: Ty) {
        self.place_proj(Write, genv, Loc::Local(place.local), &mut place.projection.iter(), |ty| {
            *ty = new_ty
        });
    }

    fn path_proj<'a>(
        &'a mut self,
        genv: &GlobalEnv,
        loc: Loc,
        proj: impl IntoIterator<Item = Field>,
    ) -> &'a mut Ty {
        let mut node = self.map.get_mut(&loc).unwrap();
        for f in proj {
            node = &mut node.unfold(genv)[f];
        }
        node.fold(genv)
    }

    fn place_proj<M, R, F>(
        &mut self,
        _mode: M,
        genv: &GlobalEnv,
        mut loc: Loc,
        proj: &mut std::slice::Iter<PlaceElem>,
        f: F,
    ) -> R
    where
        M: ProjMode,
        F: for<'a> FnOnce(M::Result<'a>) -> R,
    {
        loop {
            let ty = self.path_proj(genv, loc, proj.map_take_while(|p| PlaceElem::as_field(p)));

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
}

trait ProjMode {
    type Result<'a>;

    fn to_result<'a>(ty: &'a mut Ty) -> Self::Result<'a>;

    fn place_proj_ty<'a>(
        paths: &'a mut PathsTree,
        genv: &GlobalEnv,
        ty: &Ty,
        proj: &mut std::slice::Iter<PlaceElem>,
    ) -> Self::Result<'a>;
}

struct Read;

struct Write;

impl ProjMode for Read {
    type Result<'a> = Ty;

    fn to_result<'a>(ty: &'a mut Ty) -> Ty {
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
                    return paths.place_proj(Read, genv, *loc, proj, |ty| ty);
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

impl ProjMode for Write {
    type Result<'a> = &'a mut Ty;

    fn to_result<'a>(ty: &'a mut Ty) -> &'a mut Ty {
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
