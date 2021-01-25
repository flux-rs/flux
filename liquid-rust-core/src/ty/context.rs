use std::cell::{Cell, RefCell};

use hashconsing::{HConsign, HashConsign};

use crate::{
    ast::TypeLayout,
    names::{Local, Location},
    ty::{self, pred, *},
};

pub struct TyCtxt {
    interner: RefCell<CtxtInterner>,
    pub preds: CommonPreds,
    pub types: CommonTypes,
    next_fresh: Cell<usize>,
}

impl Default for TyCtxt {
    fn default() -> Self {
        TyCtxt::new()
    }
}

impl TyCtxt {
    pub fn new() -> Self {
        let mut interner = CtxtInterner::new();
        let preds = CommonPreds::new(&mut interner);
        let types = CommonTypes::new(&mut interner, &preds);
        TyCtxt {
            interner: RefCell::new(interner),
            preds,
            types,
            next_fresh: Cell::new(0),
        }
    }

    pub fn mk_ty(&self, ty: TyKind) -> Ty {
        self.interner.borrow_mut().intern_ty(ty)
    }

    pub fn mk_pred(&self, kind: PredKind) -> Pred {
        self.interner.borrow_mut().intern_pred(kind)
    }

    pub fn fresh(&self) -> usize {
        self.next_fresh.set(self.next_fresh.get() + 1);
        self.next_fresh.get() - 1
    }

    pub fn fresh_kvar(&self) -> KVid {
        KVid(self.fresh())
    }

    pub fn fresh_local(&self) -> Local {
        Local(self.fresh())
    }

    pub fn fresh_location(&self) -> Location {
        Location(self.fresh())
    }

    pub fn fresh_region_vid(&self) -> RegionVid {
        RegionVid(self.fresh())
    }

    pub fn fresh_field(&self) -> Field {
        Field(self.fresh())
    }

    // Types

    pub fn mk_fn_ty(&self, fn_ty: FnTy) -> Ty {
        self.mk_ty(TyKind::Fn(fn_ty))
    }

    pub fn mk_own_ref(&self, location: Location) -> Ty {
        self.mk_ty(TyKind::OwnRef(location))
    }

    pub fn mk_tuple(&self, tup: Tuple) -> Ty {
        self.mk_ty(TyKind::Tuple(tup))
    }

    pub fn mk_uninit(&self, n: usize) -> Ty {
        self.mk_ty(TyKind::Uninit(n))
    }

    pub fn mk_refine<R: Into<Refine>>(&self, bty: BaseTy, refine: R) -> Ty {
        self.mk_ty(TyKind::Refine(bty, refine.into()))
    }

    pub fn mk_ref<R: Into<Region>>(&self, bk: BorrowKind, region: R, location: Location) -> Ty {
        self.mk_ty(TyKind::Ref(bk, region.into(), location))
    }

    pub fn mk_ty_for_layout(&self, layout: &TypeLayout) -> Ty {
        match layout {
            TypeLayout::Tuple(tup) => {
                let tup = tup
                    .iter()
                    .map(|layout| (self.fresh_field(), self.mk_ty_for_layout(layout)))
                    .collect();
                self.mk_ty(TyKind::Tuple(tup))
            }
            TypeLayout::Block(size) => self.mk_ty(TyKind::Uninit(*size)),
        }
    }

    pub fn uninitialize(&self, ty: &Ty) -> Ty {
        match ty.kind() {
            TyKind::Tuple(tup) => {
                let tup = tup.map(|_, fld, ty| (*fld, self.uninitialize(ty)));
                self.mk_tuple(tup)
            }
            TyKind::Fn(..)
            | TyKind::OwnRef(..)
            | TyKind::Ref(..)
            | TyKind::Uninit(_)
            | TyKind::Refine(..) => self.mk_uninit(ty.size()),
        }
    }

    pub fn selfify(&self, ty: &Ty, place: pred::Place) -> Ty {
        match ty.kind() {
            TyKind::Refine(bty, _) => {
                let pred = self.mk_bin_op(BinOp::Eq, self.preds.nu(), self.mk_pred_place(place));
                self.mk_refine(*bty, pred)
            }
            TyKind::Tuple(tup) => {
                let tup = tup.map(|i, fld, ty| (*fld, self.selfify(ty, place.extend_path(i))));
                self.mk_tuple(tup)
            }
            _ => ty.clone(),
        }
    }

    pub fn replace_with_fresh_vars(&self, ty: &Ty, vars_in_scope: &[Var]) -> Ty {
        match ty.kind() {
            TyKind::Fn(fn_ty) => {
                let fn_ty = FnTy {
                    in_heap: fn_ty
                        .in_heap
                        .map_ty(|ty| self.replace_with_fresh_vars(ty, vars_in_scope)),
                    inputs: fn_ty.inputs.clone(),
                    out_heap: fn_ty
                        .out_heap
                        .map_ty(|ty| self.replace_with_fresh_vars(ty, vars_in_scope)),
                    output: fn_ty.output,
                };
                self.mk_fn_ty(fn_ty)
            }
            TyKind::Tuple(tup) => {
                let tup =
                    tup.map(|_, fld, ty| (*fld, self.replace_with_fresh_vars(ty, vars_in_scope)));
                self.mk_tuple(tup)
            }
            TyKind::Refine(bty, _) => {
                let mut vec = vec![Var::Nu];
                vec.extend(vars_in_scope);
                let kvar = ty::Kvar(self.fresh_kvar(), vec);
                self.mk_refine(*bty, kvar)
            }
            TyKind::Ref(bk, _, l) => self.mk_ref(*bk, self.fresh_region_vid(), *l),
            TyKind::Uninit(..) | TyKind::OwnRef(..) => ty.clone(),
        }
    }

    // Predicates

    pub fn mk_constant(&self, constant: pred::Constant) -> Pred {
        self.mk_pred(PredKind::Constant(constant))
    }

    pub fn mk_pred_place(&self, place: pred::Place) -> Pred {
        self.mk_pred(PredKind::Place(place))
    }

    pub fn mk_bin_op(&self, op: ty::BinOp, lhs: Pred, rhs: Pred) -> Pred {
        self.mk_pred(PredKind::BinaryOp(op, lhs, rhs))
    }

    pub fn mk_un_op(&self, op: ty::UnOp, operand: Pred) -> Pred {
        self.mk_pred(PredKind::UnaryOp(op, operand))
    }
}

pub struct CommonTypes {
    unit: Ty,
    int: Ty,
    bool: Ty,
}

impl CommonTypes {
    fn new(interner: &mut CtxtInterner, preds: &CommonPreds) -> Self {
        let mut intern = |typ| interner.intern_ty(typ);
        let mk_refine = |bty| TyKind::Refine(bty, Refine::Pred(preds.tt()));
        CommonTypes {
            unit: intern(mk_refine(BaseTy::Unit)),
            int: intern(mk_refine(BaseTy::Int)),
            bool: intern(mk_refine(BaseTy::Bool)),
        }
    }

    pub fn unit(&self) -> Ty {
        self.unit.clone()
    }

    pub fn int(&self) -> Ty {
        self.int.clone()
    }

    pub fn bool(&self) -> Ty {
        self.bool.clone()
    }
}

#[derive(Clone)]
pub struct CommonPreds {
    nu: Pred,
    tt: Pred,
    ff: Pred,
}

impl CommonPreds {
    fn new(interner: &mut CtxtInterner) -> Self {
        let mut intern = |pred| interner.intern_pred(pred);
        CommonPreds {
            nu: intern(PredKind::Place(pred::Place::from(Var::Nu))),
            tt: intern(PredKind::Constant(pred::Constant::Bool(true))),
            ff: intern(PredKind::Constant(pred::Constant::Bool(false))),
        }
    }

    pub fn tt(&self) -> Pred {
        self.tt.clone()
    }

    pub fn nu(&self) -> Pred {
        self.nu.clone()
    }
}

struct CtxtInterner {
    types: HConsign<TyS>,
    preds: HConsign<PredS>,
}

impl CtxtInterner {
    fn new() -> Self {
        CtxtInterner {
            types: HConsign::empty(),
            preds: HConsign::empty(),
        }
    }

    fn intern_ty(&mut self, kind: TyKind) -> Ty {
        self.types.mk(TyS { kind })
    }

    fn intern_pred(&mut self, kind: PredKind) -> Pred {
        self.preds.mk(PredS { kind })
    }
}
