use std::{collections::HashMap, fmt};

use liquid_rust_common::index::IndexGen;
use liquid_rust_lrir::{
    mir::{Local, PlaceElem, PlaceRef},
    ty::{subst::Subst, GhostVar, Path, Pred, Ty, TyCtxt, TyKind, Var},
};

use crate::{bblock_env::BBlockEnv, binding_tree::BindingTree};

pub struct LocalEnv<'tcx> {
    tcx: &'tcx TyCtxt,
    pub bindings: BindingTree,
    locals: Vec<HashMap<Local, GhostVar>>,
    pub var_gen: IndexGen,
}

impl<'tcx> LocalEnv<'tcx> {
    pub fn new(tcx: &'tcx TyCtxt) -> Self {
        Self {
            tcx,
            bindings: BindingTree::new(),
            locals: vec![HashMap::new()],
            var_gen: IndexGen::new(),
        }
    }

    pub fn fresh_ghost(&mut self) -> GhostVar {
        self.var_gen.fresh()
    }

    /// Add a new `local` to the environment with current type `ty`.
    ///
    /// Returns the freshly generated [GhostVar] assigned to `local`.
    pub fn alloc(&mut self, local: Local, ty: Ty) -> GhostVar {
        let fresh_gv = self.fresh_ghost();
        self.insert_local(local, fresh_gv);
        self.push_binding(fresh_gv, ty);
        fresh_gv
    }

    /// Lookup the current type of a place (following references).
    ///
    /// This function panics if `place` is not valid.
    pub fn lookup(&self, place: PlaceRef) -> Ty {
        let mut ty = self.lookup_var(self.lookup_local(place.local));
        for elem in place.projection {
            match (ty.kind(), elem) {
                (TyKind::Tuple(tuple), &PlaceElem::Field(n)) => {
                    ty = tuple.ty_at(n);
                }
                (TyKind::Ref(.., gv), PlaceElem::Deref) => {
                    ty = self.lookup_var(gv);
                }
                _ => unreachable!("{} {} {:?}", ty, place, elem),
            }
        }
        ty.clone()
    }

    /// Marks place as uninitialized memory and returns its current type.
    pub fn move_place(&mut self, place: PlaceRef) -> Ty {
        let ty = self.lookup(place);
        self.update(place, self.tcx.uninitialize(&ty));
        ty
    }

    /// Update the type of `place` to be `ty` creating new ghost variables for the
    /// [base](liquid_rust_lrir::Place::base) of place and every updated reference.
    ///
    /// Returns the freshly generated [GhostVar] assigned to the [base](liquid_rust_lrir::Place::base)
    /// of `place`.
    pub fn update(&mut self, place: PlaceRef, ty: Ty) -> GhostVar {
        let gv = self.lookup_local(place.local);
        let root = self.tcx.selfify(self.lookup_var(gv), Path::from(gv));
        let fresh_gv = self.fresh_ghost();
        let ty = self.update_rec(&root, place.projection, ty);
        self.insert_local(place.local, fresh_gv);
        self.push_binding(fresh_gv, ty);
        fresh_gv
    }

    fn update_rec(&mut self, root: &Ty, projs: &[PlaceElem], ty: Ty) -> Ty {
        let tcx = self.tcx;
        match (root.kind(), projs) {
            (_, []) => ty,
            (TyKind::Tuple(tup), &[PlaceElem::Field(n), ..]) => {
                let ty = self.update_rec(tup.ty_at(n), &projs[1..], ty);
                tcx.mk_tuple(tup.map_ty_at(n, |_| ty))
            }
            (TyKind::Ref(bk, r, gv), [PlaceElem::Deref, ..]) => {
                let root = tcx.selfify(self.lookup_var(gv), Path::from(*gv));
                let fresh_gv = self.fresh_ghost();
                let ty = self.update_rec(&root, &projs[1..], ty);
                self.push_binding(fresh_gv, ty);
                tcx.mk_ref(*bk, r.clone(), fresh_gv)
            }
            _ => unreachable!("{} {:?}", root, projs),
        }
    }

    /// "Borrow" `place` copying a selfified version of its type and assigning it a fresh [GhostVar].
    pub fn borrow(&mut self, place: PlaceRef) -> GhostVar {
        let ty = self
            .tcx
            .selfify(&self.lookup(place), self.current_path(place));
        let fresh_gv = self.fresh_ghost();
        self.push_binding(fresh_gv, ty);
        fresh_gv
    }

    /// Get the current [Path] corresponding to `place`.
    pub fn current_path(&self, place: PlaceRef) -> Path {
        let mut base = self.lookup_local(place.local);
        let mut ty = self.lookup_var(base);
        let mut projs = Vec::new();
        for proj in place.projection {
            match (ty.kind(), proj) {
                (TyKind::Tuple(tup), &PlaceElem::Field(n)) => {
                    ty = tup.ty_at(n);
                    projs.push(n);
                }
                (TyKind::Ref(.., gv), PlaceElem::Deref) => {
                    projs.clear();
                    base = *gv;
                    ty = self.lookup_var(base);
                }
                _ => unreachable!("{} {} {:?}", ty, place, proj),
            }
        }
        Path::new(base.into(), projs)
    }

    /// Infer substitution required to jump to `bb_env`.
    pub fn infer_subst(&self, bb_env: &BBlockEnv) -> Subst {
        let mut subst = Subst::new();
        for (local, gv2) in &bb_env.locals {
            let gv1 = &self.lookup_local(*local);
            subst.add_ghost_var_subst(*gv2, *gv1);
            let ty1 = self.lookup_var(gv1);
            let ty2 = &bb_env.ghost_vars[gv2];
            self.infer_subst_rec(ty1, ty2, bb_env, &mut subst);
        }
        subst
    }

    fn infer_subst_rec(&self, ty1: &Ty, ty2: &Ty, bb_env: &BBlockEnv, subst: &mut Subst) {
        match (ty1.kind(), ty2.kind()) {
            (TyKind::Ref(_, _, gv1), TyKind::Ref(_, _, gv2)) => {
                subst.add_ghost_var_subst(*gv2, *gv1);
                let ty1 = self.lookup_var(gv1);
                let ty2 = &bb_env.ghost_vars[gv2];
                self.infer_subst_rec(ty1, ty2, bb_env, subst);
            }
            (TyKind::Tuple(tup1), TyKind::Tuple(tup2)) if tup1.len() == tup2.len() => {
                for ((fld1, ty1), (fld2, ty2)) in tup1.iter().zip(tup2.iter()) {
                    subst.add_field_subst(*fld2, *fld1);
                    self.infer_subst_rec(ty1, ty2, bb_env, subst);
                }
            }
            _ => {}
        }
    }

    pub fn subtyping(&mut self, ty1: &Ty, ty2: &Ty) {
        match (ty1.kind(), ty2.kind()) {
            (TyKind::Tuple(tup1), TyKind::Tuple(tup2)) if tup1.len() == tup2.len() => {
                let depth = self.bindings.curr_depth();
                for ((fld, ty1), ty2) in tup1.iter().zip(tup2.types()) {
                    self.subtyping(ty1, ty2);
                    self.push_binding(*fld, ty1.clone());
                }
                self.bindings.pop_to(depth);
            }
            (TyKind::Refined(bty1, refine1), TyKind::Refined(bty2, refine2)) if bty1 == bty2 => {
                self.bindings
                    .push_constraint(ty1.clone(), refine2.clone());
            }
            (TyKind::Refined(..) | TyKind::Uninit(..), TyKind::Uninit(size))
                if ty1.size() == *size => {}
            (TyKind::Ref(..), TyKind::Ref(..)) => todo!(),
            _ => unreachable!("{} {}", ty1, ty2),
        }
    }

    pub fn enter_basic_block(&mut self, bb_env: &BBlockEnv, f: impl FnOnce(&mut Self)) {
        let depth = self.bindings.curr_depth();
        let mut subst = Subst::new();
        for (gv, ty) in bb_env.ghost_vars.iter() {
            let fresh_gv = self.fresh_ghost();
            self.push_binding(fresh_gv, subst.apply(ty, self.tcx));
            subst.add_ghost_var_subst(*gv, fresh_gv);
        }
        self.locals.push(
            bb_env
                .locals
                .iter()
                .map(|(local, gv)| (*local, subst.apply(gv, self.tcx)))
                .collect(),
        );
        f(self);
        self.locals.pop();
        self.bindings.pop_to(depth);
    }

    pub fn with_guard(&mut self, guard: Pred, f: impl FnOnce(&mut Self)) {
        let depth = self.bindings.curr_depth();
        self.bindings.push_guard(guard);
        f(self);
        self.bindings.pop_to(depth);
    }

    pub fn push_binding<V: Into<Var>>(&mut self, var: V, ty: Ty) {
        self.bindings.push_binding(var, ty);
    }

    pub fn insert_local(&mut self, local: Local, gv: GhostVar) {
        self.locals.last_mut().unwrap().insert(local, gv);
    }

    fn lookup_var<V: Into<Var>>(&self, var: V) -> &Ty {
        self.bindings.lookup(var)
    }

    fn lookup_local(&self, local: Local) -> GhostVar {
        self.locals.last().unwrap()[&local]
    }
}

impl fmt::Display for LocalEnv<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let locals = self
            .locals
            .last()
            .iter()
            .copied()
            .flatten()
            .map(|(local, gv)| format!("{}: {}", local, gv))
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "{}\n[{}]", self.bindings, locals)
    }
}
