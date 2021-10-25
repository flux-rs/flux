use crate::{
    constraint_builder::Cursor,
    subst::Subst,
    ty::{ExprKind, Region, Ty, TyKind, Var},
};
use liquid_rust_common::index::IndexGen;
use liquid_rust_core::ir::{self, Local};
use rustc_hash::FxHashMap;

#[derive(Clone)]
pub struct TyEnv<'a> {
    locals: FxHashMap<Local, Ty>,
    name_gen: &'a IndexGen<Var>,
}

impl TyEnv<'_> {
    pub fn new(name_gen: &IndexGen<Var>) -> TyEnv {
        TyEnv {
            name_gen,
            locals: FxHashMap::default(),
        }
    }

    pub fn insert_local(&mut self, local: Local, ty: Ty) {
        self.locals.insert(local, ty);
    }

    pub fn lookup_local(&mut self, cursor: &mut Cursor, local: Local) -> Ty {
        let mut ty = self.locals.get(&local).cloned().unwrap();
        if let TyKind::Exists(bty, evar, e) = ty.kind() {
            let fresh = self.name_gen.fresh();
            let var = ExprKind::Var(fresh).intern();
            cursor.push_forall(
                fresh,
                bty.sort(),
                Subst::new([(*evar, var.clone())]).subst_expr(e.clone()),
            );
            ty = TyKind::Refine(*bty, var).intern();
            self.insert_local(local, ty.clone());
        }
        ty
    }

    pub fn lookup_place(&mut self, cursor: &mut Cursor, place: &ir::Place) -> Ty {
        let mut ty = self.lookup_local(cursor, place.local);
        for elem in &place.projection {
            match (elem, ty.kind()) {
                (ir::PlaceElem::Deref, TyKind::MutRef(Region::Concrete(local))) => {
                    ty = self.lookup_local(cursor, *local);
                }
                _ => {
                    unreachable!("invalid place for lookup: `{:?}`", place);
                }
            }
        }
        ty
    }

    pub fn move_place(&mut self, cursor: &mut Cursor, place: &ir::Place) -> Ty {
        let mut ty = self.lookup_local(cursor, place.local);
        self.insert_local(place.local, TyKind::Uninit(ty.layout()).intern());
        for elem in &place.projection {
            match (elem, ty.kind()) {
                (ir::PlaceElem::Deref, TyKind::MutRef(Region::Concrete(local))) => {
                    self.insert_local(*local, TyKind::Uninit(ty.layout()).intern());
                    ty = self.lookup_local(cursor, *local);
                }
                _ => {
                    unreachable!("invalid place for lookup: `{:?}`", place);
                }
            }
        }
        ty
    }

    pub fn write_place(&mut self, cursor: &mut Cursor, place: &ir::Place, new_ty: Ty) {
        let mut ty = self.lookup_local(cursor, place.local);
        let mut local = place.local;
        for elem in &place.projection {
            match (elem, ty.kind()) {
                (ir::PlaceElem::Deref, TyKind::MutRef(Region::Concrete(l))) => {
                    local = *l;
                    ty = self.lookup_local(cursor, *l);
                }
                _ => {
                    unreachable!("invalid place for write: `{:?}`", place);
                }
            }
        }
        self.insert_local(local, new_ty);
    }
}
