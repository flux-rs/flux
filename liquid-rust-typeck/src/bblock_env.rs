use std::fmt;

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

impl fmt::Display for BBlockEnv {
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

impl fmt::Debug for BBlockEnv {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}
