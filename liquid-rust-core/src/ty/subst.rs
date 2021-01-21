use std::collections::HashMap;

use super::*;

#[derive(Debug, Default)]
pub struct Subst(HashMap<SubstKey, usize>);

#[derive(Debug, PartialEq, Eq, Hash)]
enum SubstKey {
    Field(Field),
    Location(Location),
}

impl Subst {
    pub fn new() -> Self {
        Subst(HashMap::new())
    }

    pub fn apply<T: ApplySubst>(&self, tcx: &TyCtxt, e: &T) -> T {
        e.apply_subst(tcx, self)
    }

    pub fn add_field_subst(&mut self, fld1: Field, fld2: Field) {
        self.0.insert(SubstKey::Field(fld1), fld2.0);
    }

    pub fn add_location_subst(&mut self, l1: Location, l2: Location) {
        self.0.insert(SubstKey::Location(l1), l2.0);
    }

    fn get_field(&self, fld: Field) -> Option<Field> {
        self.0.get(&SubstKey::Field(fld)).map(|&n| Field(n))
    }

    fn get_location(&self, l: Location) -> Option<Location> {
        self.0.get(&SubstKey::Location(l)).map(|&n| Location(n))
    }
}

pub trait ApplySubst {
    fn apply_subst(&self, tcx: &TyCtxt, subst: &Subst) -> Self;
}

impl ApplySubst for Ty {
    fn apply_subst(&self, tcx: &TyCtxt, subst: &Subst) -> Self {
        match self.kind() {
            TyKind::Fn(fn_ty) => tcx.mk_fn_ty(fn_ty.apply_subst(tcx, subst)),
            TyKind::OwnRef(l) => tcx.mk_own_ref(l.apply_subst(tcx, subst)),
            TyKind::Ref(bk, r, l) => tcx.mk_ref(*bk, r.clone(), l.apply_subst(tcx, subst)),
            TyKind::Tuple(tup) => {
                let tup =
                    tup.map(|_, fld, ty| (fld.apply_subst(tcx, subst), ty.apply_subst(tcx, subst)));
                tcx.mk_tuple(tup)
            }
            TyKind::Uninit(_) => self.clone(),
            TyKind::Refine(bty, refine) => tcx.mk_refine(*bty, refine.apply_subst(tcx, subst)),
        }
    }
}

impl ApplySubst for FnTy {
    fn apply_subst(&self, tcx: &TyCtxt, subst: &Subst) -> Self {
        FnTy {
            in_heap: self.in_heap.apply_subst(tcx, subst),
            inputs: self
                .inputs
                .iter()
                .map(|l| l.apply_subst(tcx, subst))
                .collect(),
            out_heap: self.out_heap.apply_subst(tcx, subst),
            output: self.output.apply_subst(tcx, subst),
        }
    }
}

impl ApplySubst for Heap {
    fn apply_subst(&self, tcx: &TyCtxt, subst: &Subst) -> Self {
        self.iter()
            .map(|(l, ty)| (l.apply_subst(tcx, subst), ty.apply_subst(tcx, subst)))
            .collect()
    }
}

impl ApplySubst for LocalsMap {
    fn apply_subst(&self, tcx: &TyCtxt, subst: &Subst) -> Self {
        self.iter()
            .map(|(x, l)| (*x, l.apply_subst(tcx, subst)))
            .collect()
    }
}

impl ApplySubst for Refine {
    fn apply_subst(&self, tcx: &TyCtxt, subst: &Subst) -> Self {
        match self {
            Refine::Pred(pred) => Refine::Pred(pred.apply_subst(tcx, subst)),
            Refine::Infer(kvar) => Refine::Infer(kvar.apply_subst(tcx, subst)),
        }
    }
}

impl ApplySubst for Kvar {
    fn apply_subst(&self, tcx: &TyCtxt, subst: &Subst) -> Self {
        let Kvar(kvid, vars) = self;
        let vars = vars.iter().map(|var| var.apply_subst(tcx, subst)).collect();
        Kvar(*kvid, vars)
    }
}

impl ApplySubst for Location {
    fn apply_subst(&self, _tcx: &TyCtxt, subst: &Subst) -> Self {
        subst.get_location(*self).unwrap_or(*self)
    }
}

impl ApplySubst for Field {
    fn apply_subst(&self, _tcx: &TyCtxt, subst: &Subst) -> Self {
        subst.get_field(*self).unwrap_or(*self)
    }
}

impl ApplySubst for Var {
    fn apply_subst(&self, _tcx: &TyCtxt, subst: &Subst) -> Self {
        let var = match self {
            Var::Nu => Some(Var::Nu),
            Var::Location(l) => subst.get_location(*l).map(Var::Location),
            Var::Field(fld) => subst.get_field(*fld).map(Var::Field),
        };
        var.unwrap_or(*self)
    }
}

impl ApplySubst for Pred {
    fn apply_subst(&self, tcx: &TyCtxt, subst: &Subst) -> Self {
        match self.kind() {
            PredKind::Constant(_) => self.clone(),
            PredKind::Place(place) => tcx.mk_pred_place(place.apply_subst(tcx, subst)),
            PredKind::BinaryOp(bin_op, op1, op2) => tcx.mk_bin_op(
                *bin_op,
                op1.apply_subst(tcx, subst),
                op2.apply_subst(tcx, subst),
            ),
            PredKind::UnaryOp(un_op, op) => tcx.mk_un_op(*un_op, op.apply_subst(tcx, subst)),
        }
    }
}

impl ApplySubst for pred::Place {
    fn apply_subst(&self, tcx: &TyCtxt, subst: &Subst) -> Self {
        Self {
            base: self.base.apply_subst(tcx, subst),
            projs: self.projs.clone(),
        }
    }
}
