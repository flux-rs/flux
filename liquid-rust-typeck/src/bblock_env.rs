use liquid_rust_common::ordered_hash_map::OrderedHashMap;
use liquid_rust_lrir::{
    mir::Local,
    ty::{
        subst::{ApplySubst, Subst},
        GhostVar, Ty, TyCtxt,
    },
};

pub struct BBlockEnv {
    pub ghost_vars: OrderedHashMap<GhostVar, Ty>,
    pub locals: Vec<(Local, GhostVar)>,
}

impl ApplySubst for BBlockEnv {
    fn apply_subst(&self, tcx: &TyCtxt, subst: &Subst) -> Self {
        Self {
            ghost_vars: self
                .ghost_vars
                .iter()
                .map(|(gv, ty)| (subst.apply(gv, tcx), subst.apply(ty, tcx)))
                .collect(),
            locals: self
                .locals
                .iter()
                .map(|(local, gv)| (*local, subst.apply(gv, tcx)))
                .collect(),
        }
    }
}
