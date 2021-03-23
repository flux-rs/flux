use std::fmt;

use liquid_rust_common::{
    index::{IndexGen, IndexVec},
    ordered_map::OrderedMap,
};
use liquid_rust_lrir::{
    mir::{Local, LocalDecl},
    ty::{
        refiner::Refiner,
        subst::{ApplySubst, Subst},
        GhostVar, Ty, TyCtxt, Var,
    },
};

pub struct BBlockEnv {
    pub ghost_vars: OrderedMap<GhostVar, Ty>,
    pub locals: Vec<(Local, GhostVar)>,
}

impl BBlockEnv {
    pub fn new<'tcx>(
        local_decls: &IndexVec<Local, LocalDecl<'tcx>>,
        mut refiner: Refiner<'_, 'tcx>,
        vars_in_scope: &mut Vec<Var>,
        ghost_gen: &IndexGen<GhostVar>,
    ) -> Self {
        let mut ghost_vars = OrderedMap::new();
        let mut locals = vec![];
        for (local, local_decl) in local_decls.iter_enumerated() {
            let fresh_gv = ghost_gen.fresh();
            let ty = refiner.maybe_uninit(local_decl.ty, local, vars_in_scope);
            ghost_vars.insert(fresh_gv, ty);
            vars_in_scope.push(Var::from(fresh_gv));
            locals.push((local, fresh_gv));
        }
        vars_in_scope.truncate(vars_in_scope.len() - local_decls.len());
        BBlockEnv { ghost_vars, locals }
    }
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
            .map(|(local, gv)| format!("{:?}: {}", local, gv))
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
