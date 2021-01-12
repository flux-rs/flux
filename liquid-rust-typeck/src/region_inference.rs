use std::collections::{HashMap, HashSet};

use crate::env::Env;
use ast::{FnDef, Place, StatementKind};
use liquid_rust_core::{
    ast::{
        self,
        visitor::{self as vis, Visitor},
        FnBody, Statement,
    },
    names::{ContId, Field},
    ty::{self, BaseTy, ContTy, Heap, Ty, TyCtxt, TyS},
};
use ty::FnTy;

pub fn infer_regions<I>(
    tcx: &TyCtxt,
    func: &FnDef<I>,
    conts: HashMap<ContId, ContTy>,
    fn_ty: FnTy,
) -> (HashMap<ContId, ContTy>, FnTy) {
    let regions = RegionInferer::new(tcx, &conts).infer(func, &fn_ty);
    fix_regions(tcx, fn_ty, conts, regions)
}

// Infer Regions

struct RegionInferer<'a> {
    conts: &'a HashMap<ContId, ContTy>,
    tcx: &'a TyCtxt,
    env: Env<'a>,
    constraints: Constraints,
}

impl<'a> RegionInferer<'a> {
    pub fn new(tcx: &'a TyCtxt, conts: &'a HashMap<ContId, ContTy>) -> Self {
        RegionInferer {
            conts,
            tcx,
            env: Env::new(tcx),
            constraints: Constraints::new(),
        }
    }

    pub fn infer<I>(
        mut self,
        func: &ast::FnDef<I>,
        fn_ty: &FnTy,
    ) -> HashMap<ty::RegionVid, Vec<Place>> {
        self.env.insert_locals(fn_ty.locals(&func.params));
        self.env.extend_heap(&fn_ty.in_heap);
        self.visit_fn_body(&func.body);
        self.constraints.solve()
    }
}

impl<I> Visitor<I> for RegionInferer<'_> {
    fn visit_fn_body(&mut self, body: &FnBody<I>) {
        match body {
            FnBody::Jump { target, args } => {
                let cont_ty = &self.conts[target];
                for (x, l) in cont_ty.locals(args) {
                    let ty1 = self.env.lookup(&Place::from(x));
                    let ty2 = &cont_ty.heap[&l];
                    subtyping(
                        &mut self.constraints,
                        self.env.heap(),
                        ty1,
                        &cont_ty.heap,
                        ty2,
                    );
                }
            }
            FnBody::Ite { then, else_, .. } => {
                let snapshot = self.env.snapshot();
                self.visit_fn_body(then);
                self.env.rollback_to(snapshot);
                self.visit_fn_body(else_);
            }
            FnBody::LetCont(defs, rest) => {
                for def in defs {
                    let cont_ty = &self.conts[&def.name];
                    let snapshot = self.env.snapshot_without_locals();
                    let locals = cont_ty.locals(&def.params);
                    self.env.insert_locals(locals);
                    self.env.extend_heap(&cont_ty.heap);
                    self.visit_cont_def(def);
                    self.env.rollback_to(snapshot);
                }
                self.visit_fn_body(rest);
            }
            _ => vis::walk_fn_body(self, body),
        }
    }

    fn visit_stmnt(&mut self, stmnt: &Statement<I>) {
        match &stmnt.kind {
            StatementKind::Let(local, layout) => {
                let ty = self.tcx.mk_ty_for_layout(layout);
                self.env.alloc(*local, ty);
            }
            StatementKind::Assign(place, rvalue) => {
                let ty = synth(rvalue, self.tcx, &mut self.env);
                self.env.update(place, ty);
            }
            StatementKind::Drop(place) => {
                self.env.drop(place);
            }
            StatementKind::Nop => {}
        }
    }
}

// Synth

fn synth(rvalue: &ast::Rvalue, tcx: &TyCtxt, env: &mut Env) -> Ty {
    match rvalue {
        ast::Rvalue::Use(op @ ast::Operand::Constant(c)) => {
            let pred = env.resolve_operand(op);
            tcx.mk_refine(
                c.base_ty(),
                tcx.mk_bin_op(ty::BinOp::Eq, tcx.preds.nu(), pred),
            )
        }
        ast::Rvalue::Use(ast::Operand::Use(place)) => {
            let ty = env.lookup(place);
            tcx.selfify(ty, env.resolve_place(place))
        }
        ast::Rvalue::Ref(bk, place) => {
            let l = env.borrow(place);
            tcx.mk_ref(*bk, ty::Region::from(place.clone()), l)
        }
        ast::Rvalue::BinaryOp(bin_op, ..) => ty_for_bin_op(bin_op, tcx),
        ast::Rvalue::CheckedBinaryOp(bin_op, ..) => {
            let ty = ty_for_bin_op(bin_op, tcx);
            tcx.mk_tuple(tup!(Field(0) => ty, Field(1) => tcx.types.bool()))
        }
        ast::Rvalue::UnaryOp(un_op, op) => match un_op {
            ast::UnOp::Not => {
                let pred = env.resolve_operand(op);
                tcx.mk_refine(BaseTy::Bool, pred)
            }
        },
    }
}

fn ty_for_bin_op(bin_op: &ast::BinOp, tcx: &TyCtxt) -> Ty {
    use ast::BinOp as ast;
    let bty = match bin_op {
        ast::Add | ast::Sub => BaseTy::Int,
        ast::Eq | ast::Lt | ast::Le | ast::Ge | ast::Gt => BaseTy::Bool,
    };
    tcx.mk_refine(bty, tcx.preds.tt())
}

fn subtyping(
    constraints: &mut Constraints,
    heap1: &ty::Heap,
    ty1: &TyS,
    heap2: &ty::Heap,
    ty2: &TyS,
) {
    match (ty1.kind(), ty2.kind()) {
        (ty::TyKind::Fn(..), ty::TyKind::Fn(..)) => todo!(),
        (ty::TyKind::Tuple(tup1), ty::TyKind::Tuple(tup2)) if tup1.len() == tup2.len() => {
            for (ty1, ty2) in tup1.types().zip(tup2.types()) {
                subtyping(constraints, heap1, ty1, heap2, ty2);
            }
        }
        (ty::TyKind::Ref(bk1, r1, l1), ty::TyKind::Ref(bk2, r2, l2)) if bk1 >= bk2 => {
            constraints.add(r1.clone(), r2.clone());
            subtyping(constraints, heap1, &heap1[l1], heap2, &heap2[l2]);
        }
        (ty::TyKind::OwnRef(l1), ty::TyKind::OwnRef(l2)) => {
            subtyping(constraints, heap1, &heap1[l1], heap2, &heap2[l2]);
        }
        (ty::TyKind::Refine(bty1, ..), ty::TyKind::Refine(bty2, ..)) if bty1 == bty2 => {}
        (_, ty::TyKind::Uninit(n)) if ty1.size() == *n => {}
        _ => bug!("{} {}", ty1, ty2),
    }
}

// Constraints

struct Constraints(Vec<(ty::Region, ty::Region)>);

impl Constraints {
    fn new() -> Self {
        Constraints(Vec::new())
    }

    fn add(&mut self, r1: ty::Region, r2: ty::Region) {
        self.0.push((r1, r2))
    }

    fn solve(self) -> HashMap<ty::RegionVid, Vec<Place>> {
        let mut map: HashMap<_, HashSet<_>> = HashMap::new();
        for (r1, r2) in self.0 {
            match (r1, r2) {
                (ty::Region::Concrete(places), ty::Region::Infer(id)) => {
                    map.entry(id).or_default().extend(places)
                }
                (ty::Region::Infer(..), _) => bug!(),
                _ => {}
            }
        }
        map.into_iter()
            .map(|(id, places)| (id, places.into_iter().collect()))
            .collect()
    }
}

// Fix Regions

fn fix_regions(
    tcx: &TyCtxt,
    fn_ty: FnTy,
    conts: HashMap<ContId, ContTy>,
    mut regions: HashMap<ty::RegionVid, Vec<Place>>,
) -> (HashMap<ContId, ContTy>, FnTy) {
    let conts = conts
        .into_iter()
        .map(|(id, cont_ty)| (id, fix_regions_cont_ty(tcx, cont_ty, &mut regions)))
        .collect();
    let fn_ty = fix_regions_fn_ty(tcx, fn_ty, &mut regions);
    (conts, fn_ty)
}

fn fix_regions_cont_ty(
    tcx: &TyCtxt,
    cont_ty: ContTy,
    regions: &mut HashMap<ty::RegionVid, Vec<Place>>,
) -> ContTy {
    ContTy {
        heap: fix_regions_heap(tcx, cont_ty.heap, regions),
        locals: cont_ty.locals,
        inputs: cont_ty.inputs,
    }
}

fn fix_regions_fn_ty(
    tcx: &TyCtxt,
    fn_ty: FnTy,
    regions: &mut HashMap<ty::RegionVid, Vec<Place>>,
) -> FnTy {
    FnTy {
        in_heap: fix_regions_heap(tcx, fn_ty.in_heap, regions),
        inputs: fn_ty.inputs,
        out_heap: fix_regions_heap(tcx, fn_ty.out_heap, regions),
        output: fn_ty.output,
    }
}

fn fix_regions_heap(
    tcx: &TyCtxt,
    heap: Heap,
    regions: &mut HashMap<ty::RegionVid, Vec<Place>>,
) -> Heap {
    heap.into_iter()
        .map(|(l, ty)| (l, fix_regions_ty(tcx, &ty, regions)))
        .collect()
}

fn fix_regions_ty(tcx: &TyCtxt, ty: &Ty, regions: &mut HashMap<ty::RegionVid, Vec<Place>>) -> Ty {
    match ty.kind() {
        ty::TyKind::Tuple(tup) => {
            let tup = tup.map(|_, fld, ty| (*fld, fix_regions_ty(tcx, ty, regions)));
            tcx.mk_tuple(tup)
        }
        ty::TyKind::Ref(bk, r, l) => match r {
            ty::Region::Concrete(_) => ty.clone(),
            ty::Region::Infer(kvid) => {
                tcx.mk_ref(*bk, ty::Region::Concrete(regions.remove(kvid).unwrap()), *l)
            }
        },
        _ => ty.clone(),
    }
}
