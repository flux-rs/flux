use std::{collections::HashMap, fmt};

use liquid_rust_common::ordered_hash_map::OrderedHashMap;
use liquid_rust_lrir::{
    ty::{GhostVar, Path, Ty, TyCtxt, TyKind},
    Local, PlaceRef, Proj,
};

pub struct LocalEnv<'tcx> {
    tcx: &'tcx TyCtxt,
    ghost_vars: OrderedHashMap<GhostVar, Ty>,
    locals: HashMap<Local, GhostVar>,
}

impl<'tcx> LocalEnv<'tcx> {
    pub fn new(tcx: &'tcx TyCtxt) -> Self {
        Self {
            tcx,
            ghost_vars: OrderedHashMap::new(),
            locals: HashMap::new(),
        }
    }

    /// Add a new `local` to the environment with current type `ty`.
    ///
    /// Returns the freshly generated [GhostVar] assigned to `local`.
    pub fn alloc(&mut self, local: Local, ty: Ty) -> GhostVar {
        let fresh_gv = self.tcx.fresh_ghost();
        self.locals.insert(local, fresh_gv);
        self.ghost_vars.insert(fresh_gv, ty);
        fresh_gv
    }

    /// Lookup the current type of a place (following references).
    pub fn lookup(&self, place: PlaceRef) -> &Ty {
        let mut ty = &self.ghost_vars[&self.locals[&place.base]];
        for proj in place.projs {
            match (ty.kind(), proj) {
                (TyKind::Tuple(tuple), &Proj::Field(n)) => {
                    ty = tuple.ty_at(n);
                }
                (TyKind::Ref(.., gv), Proj::Deref) => {
                    ty = &self.ghost_vars[gv];
                }
                _ => unreachable!("{} {} {:?}", ty, place, proj),
            }
        }
        ty
    }

    /// Update the type of `place` to be `ty` creating new ghost variables for the
    /// [base](liquid_rust_lrir::Place::base) of place and every updated reference.
    ///
    /// Returns the freshly generated [GhostVar] assigned to the [base](liquid_rust_lrir::Place::base)
    /// of `place`.
    pub fn update(&mut self, place: PlaceRef, ty: Ty) -> GhostVar {
        let gv = self.locals[&place.base];
        let root = self.tcx.selfify(&self.ghost_vars[&gv], Path::from(gv));
        let fresh_gv = self.tcx.fresh_ghost();
        let ty = self.update_rec(&root, place.projs, ty);
        self.locals.insert(place.base, fresh_gv);
        self.ghost_vars.insert(fresh_gv, ty);
        fresh_gv
    }

    fn update_rec(&mut self, root: &Ty, projs: &[Proj], ty: Ty) -> Ty {
        let tcx = self.tcx;
        match (root.kind(), projs) {
            (_, []) => ty,
            (TyKind::Tuple(tup), &[Proj::Field(n), ..]) => {
                let ty = self.update_rec(tup.ty_at(n), &projs[1..], ty);
                tcx.mk_tuple(tup.map_ty_at(n, |_| ty))
            }
            (TyKind::Ref(bk, r, gv), [Proj::Deref, ..]) => {
                let root = tcx.selfify(&self.ghost_vars[gv], Path::from(*gv));
                let fresh_gv = tcx.fresh_ghost();
                let ty = self.update_rec(&root, &projs[1..], ty);
                self.ghost_vars.insert(fresh_gv, ty);
                tcx.mk_ref(*bk, r.clone(), fresh_gv)
            }
            _ => unreachable!("{} {:?}", root, projs),
        }
    }

    /// "Borrow" `place` copying a selfified version of its type and assigning it a fresh [GhostVar].
    pub fn borrow(&mut self, place: PlaceRef) -> GhostVar {
        let ty = self
            .tcx
            .selfify(self.lookup(place), self.current_path(place));
        let fresh_gv = self.tcx.fresh_ghost();
        self.ghost_vars.insert(fresh_gv, ty);
        fresh_gv
    }

    /// Get the current [Path] corresponding to `place`.
    pub fn current_path(&self, place: PlaceRef) -> Path {
        let mut base = self.locals[&place.base];
        let mut ty = &self.ghost_vars[&base];
        let mut projs = Vec::new();
        for proj in place.projs {
            match (ty.kind(), proj) {
                (TyKind::Tuple(tup), &Proj::Field(n)) => {
                    ty = tup.ty_at(n);
                    projs.push(n);
                }
                (TyKind::Ref(.., gv), Proj::Deref) => {
                    projs.clear();
                    base = *gv;
                    ty = &self.ghost_vars[&base];
                }
                _ => unreachable!("{} {} {:?}", ty, place, proj),
            }
        }
        Path::new(base.into(), projs)
    }
}

impl fmt::Display for LocalEnv<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let ghost_vars = self
            .ghost_vars
            .iter()
            .map(|(gv, ty)| format!("{}: {}", gv, ty))
            .collect::<Vec<_>>()
            .join(", ");
        let locals = self
            .locals
            .iter()
            .map(|(local, gv)| format!("{}: {}", local, gv))
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "[{}]\n[{}]", ghost_vars, locals)
    }
}
