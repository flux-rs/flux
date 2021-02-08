use std::collections::HashMap;

use super::*;

#[derive(Debug, Default)]
pub struct Subst {
    locations: HashMap<Location, Location>,
    fields: HashMap<Field, Field>,
    regions: HashMap<Region, Region>,
}

impl Subst {
    pub fn new() -> Self {
        Subst {
            locations: HashMap::new(),
            fields: HashMap::new(),
            regions: HashMap::new(),
        }
    }

    pub fn infer(heap1: &Heap, locals1: &LocalsMap, heap2: &Heap, locals2: &LocalsMap) -> Self {
        let mut subst = Subst::new();
        for (x, l2) in locals2 {
            let l1 = &locals1[x];
            let ty1 = &heap1[l1];
            let ty2 = &heap2[l2];
            subst.add_location_subst(*l2, *l1);
            infer_subst_ty(&mut subst, heap1, ty1, heap2, ty2);
        }
        subst
    }

    pub fn apply<T: ApplySubst>(&self, tcx: &TyCtxt, e: &T) -> T {
        e.apply_subst(tcx, self)
    }

    pub fn add_field_subst(&mut self, fld1: Field, fld2: Field) {
        self.fields.insert(fld1, fld2);
    }

    pub fn add_location_subst(&mut self, l1: Location, l2: Location) {
        self.locations.insert(l1, l2);
    }

    pub fn add_region_subst(&mut self, r1: Region, r2: Region) {
        self.regions.insert(r1, r2);
    }

    fn get_field(&self, fld: Field) -> Option<Field> {
        self.fields.get(&fld).copied()
    }

    fn get_location(&self, l: Location) -> Option<Location> {
        self.locations.get(&l).copied()
    }

    fn get_region(&self, r: &Region) -> Option<&Region> {
        self.regions.get(r)
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
            TyKind::Ref(bk, r, l) => {
                tcx.mk_ref(*bk, r.apply_subst(tcx, subst), l.apply_subst(tcx, subst))
            }
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
            regions: self.regions.clone(),
            in_heap: self.in_heap.apply_subst(tcx, subst),
            inputs: self.inputs.apply_subst(tcx, subst),
            out_heap: self.out_heap.apply_subst(tcx, subst),
            outputs: self.outputs.apply_subst(tcx, subst),
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

impl ApplySubst for Region {
    fn apply_subst(&self, _tcx: &TyCtxt, subst: &Subst) -> Self {
        subst
            .get_region(self)
            .cloned()
            .unwrap_or_else(|| self.clone())
    }
}

fn infer_subst_ty(subst: &mut Subst, heap1: &Heap, ty1: &Ty, heap2: &Heap, ty2: &Ty) {
    match (ty1.kind(), ty2.kind()) {
        (TyKind::Ref(_, r1, l1), TyKind::Ref(_, r2, l2)) => {
            subst.add_region_subst(r2.clone(), r1.clone());
            subst.add_location_subst(*l2, *l1);
            infer_subst_ty(subst, heap1, &heap1[l1], heap2, &heap2[l2]);
        }
        (TyKind::OwnRef(l1), TyKind::OwnRef(l2)) => {
            subst.add_location_subst(*l2, *l1);
            infer_subst_ty(subst, heap1, &heap1[l1], heap2, &heap2[l2]);
        }
        (TyKind::Tuple(tup1), TyKind::Tuple(tup2)) if tup1.len() == tup2.len() => {
            for ((fld1, ty1), (fld2, ty2)) in tup1.iter().zip(tup2) {
                subst.add_field_subst(*fld2, *fld1);
                infer_subst_ty(subst, heap1, ty1, heap2, ty2);
            }
        }
        _ => {}
    }
}
