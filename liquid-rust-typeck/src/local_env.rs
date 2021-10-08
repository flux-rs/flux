use std::{collections::HashMap, fmt};

use liquid_rust_common::index::IndexGen;
use liquid_rust_lrir::{
    mir::{Local, PlaceElem, PlaceRef},
    ty::{subst::Subst, FnSig, GhostVar, GhostVarMap, Path, Pred, Refine, Ty, TyCtxt, TyKind, Var},
};

use crate::{bblock_env::BBlockEnv, binding_tree::BindingTree};

pub mod pretty;

pub struct LocalEnv<'tcx> {
    tcx: &'tcx TyCtxt,
    pub bindings: BindingTree,
    locals: Vec<HashMap<Local, GhostVar>>,
    ghost_gen: &'tcx IndexGen<GhostVar>,
}

impl<'tcx> LocalEnv<'tcx> {
    pub fn new(tcx: &'tcx TyCtxt, ghost_gen: &'tcx IndexGen<GhostVar>) -> Self {
        Self {
            tcx,
            bindings: BindingTree::new(),
            locals: vec![HashMap::new()],
            ghost_gen,
        }
    }

    pub fn fresh_ghost(&mut self) -> GhostVar {
        self.ghost_gen.fresh()
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

    /// Marks place as uninitialized memory and returns its current type.
    pub fn move_place(&mut self, place: PlaceRef) -> Ty {
        let ty = self.lookup(place);
        self.update(place, self.tcx.uninitialize(&ty));
        ty
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

    /// Update the type of `place` to be `ty` creating new ghost variables for the
    /// [local](liquid_rust_lrir::Place::local) of `place` and every updated reference.
    ///
    /// Returns the freshly generated [GhostVar] assigned to the [local](liquid_rust_lrir::Place::local)
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

    pub fn extend(&mut self, ghost_vars: Vec<(GhostVar, Ty)>) {
        for (gv, ty) in ghost_vars {
            self.bindings.push_binding(gv, ty);
        }
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

    pub fn open_fn_sig(
        &self,
        fn_sig: &FnSig,
        args: &[Local],
    ) -> (BBlockEnv, Vec<(GhostVar, Ty)>, Ty) {
        let tcx = self.tcx;
        let mut subst = self.infer_call_subst(fn_sig, args);
        let input_env = BBlockEnv {
            ghost_vars: subst.apply(&fn_sig.requires, tcx),
            locals: args
                .iter()
                .zip(&fn_sig.inputs)
                .map(|(local, gv)| (*local, subst.apply(gv, tcx)))
                .collect(),
        };
        let mut ret = None;
        let mut out_env = vec![];
        for (gv, ty) in &fn_sig.ensures {
            let fresh_gv = self.ghost_gen.fresh();
            let ty = subst.apply(ty, tcx);
            out_env.push((fresh_gv, ty.clone()));
            if *gv == fn_sig.output {
                ret = Some(ty)
            }
            subst.add_ghost_var_subst(*gv, fresh_gv);
        }
        (input_env, out_env, ret.unwrap())
    }

    pub fn infer_call_subst(&self, fn_sig: &FnSig, args: &[Local]) -> Subst {
        let mut subst = Subst::new();
        for (local, gv2) in args.iter().zip(&fn_sig.inputs) {
            let gv1 = self.lookup_local(*local);
            subst.add_ghost_var_subst(*gv2, gv1);
            let ty1 = self.lookup_var(&gv1);
            let ty2 = &fn_sig.requires[&gv2];
            subst.infer(self, ty1, &fn_sig.requires, ty2);
        }
        subst
    }

    pub fn infer_jump_subst(&self, env: &BBlockEnv) -> Subst {
        let mut subst = Subst::new();
        for (local, gv2) in &env.locals {
            let gv1 = self.lookup_local(*local);
            subst.add_ghost_var_subst(*gv2, gv1);
            let ty1 = self.lookup_var(&gv1);
            let ty2 = &env.ghost_vars[gv2];
            subst.infer(self, ty1, env, ty2);
        }
        subst
    }

    pub fn env_subtyping(&mut self, env: &BBlockEnv) {
        for &(local, gv) in &env.locals {
            let ty1 = &self
                .tcx
                .selfify(&self.lookup(PlaceRef::from(local)), Path::from(gv));
            let ty2 = &env.ghost_vars[&gv];
            self.subtyping(ty1, ty2);
        }
    }

    pub fn subtyping(&mut self, ty1: &Ty, ty2: &Ty) {
        let depth = self.bindings.curr_depth();
        match (ty1.kind(), ty2.kind()) {
            (TyKind::Tuple(tup1), TyKind::Tuple(tup2)) if tup1.len() == tup2.len() => {
                for ((fld, ty1), ty2) in tup1.iter().zip(tup2.types()) {
                    self.subtyping(ty1, ty2);
                    self.push_binding(*fld, ty1.clone());
                }
            }
            (TyKind::Refined(bty1, _), TyKind::Refined(bty2, refine2)) if bty1 == bty2 => {
                self.bindings.push_binding(Var::Nu, ty1.clone());
                self.bindings.push_pred(refine2.clone());
            }
            (TyKind::Refined(..) | TyKind::Uninit(..), TyKind::Uninit(size))
                if ty1.size() == *size => {}
            (TyKind::Ref(..), TyKind::Ref(..)) => todo!(),
            _ => unreachable!("{} {}", ty1, ty2),
        }
        self.bindings.pop_to(depth);
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
        self.bindings.push_guard(Refine::Pred(guard));
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
            .map(|(local, gv)| format!("{:?}: {}", local, gv))
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "{}\n[{}]", self.bindings, locals)
    }
}

impl GhostVarMap for LocalEnv<'_> {
    fn lookup(&self, gv: &GhostVar) -> &Ty {
        self.lookup_var(gv)
    }
}
