use std::collections::HashMap;

use super::*;

#[derive(Debug, Default)]
pub struct Subst {
    ghost_vars: HashMap<GhostVar, GhostVar>,
    fields: HashMap<Field, Field>,
}

impl Subst {
    pub fn new() -> Self {
        Subst {
            ghost_vars: HashMap::new(),
            fields: HashMap::new(),
        }
    }

    pub fn apply<T: ApplySubst>(&self, e: &T, tcx: &TyCtxt) -> T {
        e.apply_subst(tcx, self)
    }

    pub fn add_field_subst(&mut self, fld1: Field, fld2: Field) {
        self.fields.insert(fld1, fld2);
    }

    pub fn add_ghost_var_subst(&mut self, l1: GhostVar, l2: GhostVar) {
        self.ghost_vars.insert(l1, l2);
    }

    fn get_field(&self, fld: Field) -> Option<Field> {
        self.fields.get(&fld).copied()
    }

    fn get_ghost_var(&self, l: GhostVar) -> Option<GhostVar> {
        self.ghost_vars.get(&l).copied()
    }
}

pub trait ApplySubst {
    fn apply_subst(&self, tcx: &TyCtxt, subst: &Subst) -> Self;
}

impl ApplySubst for Ty {
    fn apply_subst(&self, tcx: &TyCtxt, subst: &Subst) -> Self {
        match self.kind() {
            TyKind::Ref(bk, r, gv) => tcx.mk_ref(*bk, r.clone(), subst.apply(gv, tcx)),
            TyKind::Tuple(tup) => {
                let tup = tup.map(|_, fld, ty| (subst.apply(fld, tcx), subst.apply(ty, tcx)));
                tcx.mk_tuple(tup)
            }
            TyKind::Uninit(_) => self.clone(),
            TyKind::Refined(bty, refine) => tcx.mk_refine(*bty, subst.apply(refine, tcx)),
        }
    }
}

impl ApplySubst for Refine {
    fn apply_subst(&self, tcx: &TyCtxt, subst: &Subst) -> Self {
        match self {
            Refine::Pred(pred) => Refine::Pred(subst.apply(pred, tcx)),
            Refine::Infer(kvar) => Refine::Infer(subst.apply(kvar, tcx)),
        }
    }
}

impl ApplySubst for Kvar {
    fn apply_subst(&self, tcx: &TyCtxt, subst: &Subst) -> Self {
        Kvar {
            id: self.id,
            vars: self.vars.iter().map(|var| subst.apply(var, tcx)).collect(),
        }
    }
}

impl ApplySubst for Pred {
    fn apply_subst(&self, tcx: &TyCtxt, subst: &Subst) -> Self {
        match self.kind() {
            PredKind::Const(_) => self.clone(),
            PredKind::Path(path) => tcx.mk_path(subst.apply(path, tcx)),
            PredKind::BinaryOp(bin_op, op1, op2) => {
                tcx.mk_bin_op(*bin_op, subst.apply(op1, tcx), subst.apply(op2, tcx))
            }
            PredKind::UnaryOp(un_op, op) => tcx.mk_un_op(*un_op, subst.apply(op, tcx)),
        }
    }
}

impl ApplySubst for Path {
    fn apply_subst(&self, tcx: &TyCtxt, subst: &Subst) -> Self {
        Self {
            base: subst.apply(&self.base, tcx),
            projs: self.projs.clone(),
        }
    }
}

impl ApplySubst for Var {
    fn apply_subst(&self, tcx: &TyCtxt, subst: &Subst) -> Self {
        match self {
            Var::Nu => Var::Nu,
            Var::Ghost(gv) => Var::Ghost(subst.apply(gv, tcx)),
            Var::Field(fld) => Var::Field(subst.apply(fld, tcx)),
        }
    }
}

impl ApplySubst for GhostVar {
    fn apply_subst(&self, _tcx: &TyCtxt, subst: &Subst) -> Self {
        subst.get_ghost_var(*self).unwrap_or(*self)
    }
}

impl ApplySubst for Field {
    fn apply_subst(&self, _tcx: &TyCtxt, subst: &Subst) -> Self {
        subst.get_field(*self).unwrap_or(*self)
    }
}
