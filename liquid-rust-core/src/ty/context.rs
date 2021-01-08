use std::cell::{Cell, RefCell};

use hashconsing::{HConsign, HashConsign};

use super::{
    pred::{self, Var},
    *,
};
use crate::{
    ast::TypeLayout,
    names::{Local, Location},
};

pub struct TyCtxt {
    interner: RefCell<CtxtInterner>,
    pub preds: CommonPreds,
    pub types: CommonTypes,
    next_fresh: Cell<usize>,
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

    pub fn mk_pred(&self, pred: PredS) -> Pred {
        self.interner.borrow_mut().intern_pred(pred)
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

    pub fn mk_refine(&self, bty: BaseType, refine: Refine) -> Ty {
        self.mk_ty(TyKind::Refine { bty, refine })
    }

    pub fn mk_unrefined(&self, ty: BaseType) -> Ty {
        self.mk_ty(TyKind::Refine {
            bty: ty,
            refine: Refine::Pred(self.preds.tt()),
        })
    }

    pub fn mk_ref(&self, bk: BorrowKind, region: Region, location: Location) -> Ty {
        self.mk_ty(TyKind::Ref(bk, region, location))
    }

    pub fn mk_ty_for_layout(&self, layout: &TypeLayout) -> Ty {
        match layout {
            TypeLayout::Tuple(tuple) => {
                let tuple = tuple
                    .iter()
                    .map(|layout| (self.fresh_field(), self.mk_ty_for_layout(layout)));
                self.mk_ty(TyKind::Tuple(tuple.into()))
            }
            TypeLayout::Block(size) => self.mk_ty(TyKind::Uninit(*size)),
        }
    }

    // Predicates

    pub fn mk_constant(&self, constant: pred::Constant) -> Pred {
        self.mk_pred(PredS::Constant(constant))
    }

    pub fn mk_pred_place(&self, place: pred::Place) -> Pred {
        self.mk_pred(PredS::Place(place))
    }

    pub fn mk_bin_op(&self, op: pred::BinOp, lhs: Pred, rhs: Pred) -> Pred {
        self.mk_pred(PredS::BinaryOp(op, lhs, rhs))
    }

    pub fn mk_un_op(&self, op: pred::UnOp, operand: Pred) -> Pred {
        self.mk_pred(PredS::UnaryOp(op, operand))
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
        let mk_refine = |ty| TyKind::Refine {
            bty: ty,
            refine: Refine::Pred(preds.tt()),
        };
        CommonTypes {
            unit: intern(mk_refine(BaseType::Unit)),
            int: intern(mk_refine(BaseType::Int)),
            bool: intern(mk_refine(BaseType::Bool)),
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
            nu: intern(PredS::Place(pred::Place {
                base: Var::Nu,
                projs: vec![],
            })),
            tt: intern(PredS::Constant(pred::Constant::Bool(true))),
            ff: intern(PredS::Constant(pred::Constant::Bool(false))),
        }
    }

    pub fn tt(&self) -> Pred {
        self.tt.clone()
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

    fn intern_pred(&mut self, pred: PredS) -> Pred {
        self.preds.mk(pred)
    }
}
