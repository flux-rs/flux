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

    pub fn infer<E1, E2>(&mut self, env1: &E1, ty1: &Ty, env2: &E2, ty2: &Ty)
    where
        E1: GhostVarMap,
        E2: GhostVarMap,
    {
        match (ty1.kind(), ty2.kind()) {
            (TyKind::Ref(_, _, gv1), TyKind::Ref(_, _, gv2)) => {
                self.add_ghost_var_subst(*gv2, *gv1);
                let ty1 = env1.lookup(gv1);
                let ty2 = env2.lookup(gv2);
                self.infer(env1, ty1, env2, ty2);
            }
            (TyKind::Tuple(tup1), TyKind::Tuple(tup2)) if tup1.len() == tup2.len() => {
                for ((fld1, ty1), (fld2, ty2)) in tup1.iter().zip(tup2.iter()) {
                    self.add_field_subst(*fld2, *fld1);
                    self.infer(env1, ty1, env2, ty2);
                }
            }
            _ => {}
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
            var: subst.apply(&self.var, tcx),
            projection: self.projection.clone(),
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

impl<K, V> ApplySubst for OrderedMap<K, V>
where
    K: ApplySubst + Eq + std::hash::Hash,
    V: ApplySubst,
{
    fn apply_subst(&self, tcx: &TyCtxt, subst: &Subst) -> Self {
        self.iter()
            .map(|(gv, ty)| (gv.apply_subst(tcx, subst), ty.apply_subst(tcx, subst)))
            .collect()
    }
}
