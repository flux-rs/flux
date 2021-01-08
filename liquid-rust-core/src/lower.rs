use std::collections::HashMap;

use crate::ast::{
    self,
    visitor::{self as vis, Visitor},
    LocalsMap,
};
use crate::names::ContId;
use crate::ty::{self, TyCtxt};

pub struct ContTyLowerer<'a> {
    map: HashMap<ty::ContId, ty::ContTy>,
    tcx: &'a TyCtxt,
}

impl<'a> ContTyLowerer<'a> {
    pub fn new(tcx: &'a TyCtxt) -> Self {
        ContTyLowerer {
            map: HashMap::new(),
            tcx,
        }
    }
}

impl ContTyLowerer<'_> {
    pub fn lower<I>(mut self, func: &ast::FnDef<I>) -> HashMap<ContId, ty::ContTy> {
        self.visit_fn_body(&func.body);
        let ret_cont_ty = ty::ContTy::new(
            func.ty.out_heap.lower(&self.tcx),
            LocalsMap::empty(),
            vec![func.ty.output],
        );
        self.map.insert(func.ret, ret_cont_ty);
        self.map
    }
}

impl<I> Visitor<I> for ContTyLowerer<'_> {
    fn visit_cont_def(&mut self, def: &ast::ContDef<I>) {
        self.map.insert(def.name, def.ty.lower(self.tcx));
        vis::walk_cont_def(self, def);
    }
}

impl ast::Ty {
    fn lower(&self, tcx: &TyCtxt) -> ty::Ty {
        match self {
            ast::Ty::Fn(fn_ty) => tcx.mk_fn_ty(fn_ty.lower(tcx)),
            ast::Ty::OwnRef(location) => tcx.mk_own_ref(*location),
            ast::Ty::Ref(bk, region, location) => tcx.mk_ref(*bk, region.lower(tcx), *location),
            ast::Ty::Tuple(tup) => tcx.mk_tuple(ty::Tuple::from(
                tup.iter().map(|(f, ty)| (*f, ty.lower(tcx))),
            )),
            ast::Ty::Uninit(n) => tcx.mk_uninit(*n),
            ast::Ty::Refine { bty: ty, refine } => tcx.mk_refine(*ty, refine.lower(tcx)),
        }
    }
}

impl ast::ContTy {
    pub fn lower(&self, tcx: &TyCtxt) -> ty::ContTy {
        ty::ContTy::new(
            self.heap.lower(tcx),
            self.locals.clone(),
            self.inputs.clone(),
        )
    }
}

impl ast::FnTy {
    pub fn lower(&self, tcx: &TyCtxt) -> ty::FnTy {
        ty::FnTy {
            in_heap: self.in_heap.lower(tcx),
            inputs: self.inputs.clone(),
            out_heap: self.out_heap.lower(tcx),
            output: self.output.clone(),
        }
    }
}

impl ast::Heap {
    fn lower(&self, tcx: &TyCtxt) -> ty::Heap {
        ty::Heap::from(
            self.into_iter()
                .map(|(location, ty)| (*location, ty.lower(tcx))),
        )
    }
}

impl ast::Region {
    fn lower(&self, tcx: &TyCtxt) -> ty::Region {
        match self {
            ast::Region::Concrete(places) => ty::Region::Concrete(places.clone()),
            ast::Region::Infer => ty::Region::Infer(tcx.fresh_region_vid()),
        }
    }
}

impl ast::Refine {
    fn lower(&self, tcx: &TyCtxt) -> ty::Refine {
        match self {
            ast::Refine::Pred(pred) => ty::Refine::Pred(pred.lower(tcx)),
            ast::Refine::Infer => ty::Refine::Infer(tcx.fresh_kvar()),
        }
    }
}

impl ast::Pred {
    fn lower(&self, tcx: &TyCtxt) -> ty::Pred {
        match self {
            ast::Pred::Constant(c) => tcx.mk_constant(*c),
            ast::Pred::Place(place) => tcx.mk_pred_place(place.clone()),
            ast::Pred::BinaryOp(op, lhs, rhs) => tcx.mk_bin_op(*op, lhs.lower(tcx), rhs.lower(tcx)),
            ast::Pred::UnaryOp(op, operand) => tcx.mk_un_op(*op, operand.lower(tcx)),
        }
    }
}
