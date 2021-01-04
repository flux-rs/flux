use rustc_arena::TypedArena;
use rustc_data_structures::sharded::ShardedHashMap;

use super::ast::*;

#[derive(Default)]
pub struct Arena<'lr> {
    types: TypedArena<TyS<'lr>>,
    preds: TypedArena<PredS<'lr>>,
}

impl<'lr> Arena<'lr> {
    fn alloc_ty(&self, kind: TyS<'lr>) -> &mut TyS<'lr> {
        self.types.alloc(kind)
    }

    fn alloc_pred(&self, pred: PredS<'lr>) -> &mut PredS<'lr> {
        self.preds.alloc(pred)
    }
}

struct CtxtInterners<'lr> {
    arena: &'lr Arena<'lr>,
    types: ShardedHashMap<Ty<'lr>, ()>,
    preds: ShardedHashMap<Pred<'lr>, ()>,
}

impl<'lr> CtxtInterners<'lr> {
    fn new(arena: &'lr Arena<'lr>) -> Self {
        CtxtInterners {
            arena,
            types: ShardedHashMap::default(),
            preds: ShardedHashMap::default(),
        }
    }

    fn intern_ty(&self, ty: TyS<'lr>) -> Ty<'lr> {
        self.types.intern(ty, |ty| self.arena.alloc_ty(ty))
    }

    fn intern_pred(&self, pred: PredS<'lr>) -> Pred<'lr> {
        self.preds.intern(pred, |pred| self.arena.alloc_pred(pred))
    }
}

pub struct CommonPreds<'lr> {
    pub nu: Pred<'lr>,
    pub tt: Pred<'lr>,
    pub ff: Pred<'lr>,
}

impl<'lr> CommonPreds<'lr> {
    fn new(interners: &CtxtInterners<'lr>) -> Self {
        let mk = |pred| interners.intern_pred(pred);
        CommonPreds {
            nu: mk(PredS::Place {
                var: Var::Nu,
                projection: vec![],
            }),
            tt: mk(PredS::Constant(ConstantP::Bool(true))),
            ff: mk(PredS::Constant(ConstantP::Bool(false))),
        }
    }
}

pub struct CommonTypes<'lr> {
    pub unit: Ty<'lr>,
}

impl<'lr> CommonTypes<'lr> {
    fn new(interners: &CtxtInterners<'lr>) -> Self {
        let mk = |typ| interners.intern_ty(typ);
        CommonTypes {
            unit: mk(TyS::Tuple(vec![])),
        }
    }
}

pub struct LiquidRustCtxt<'lr> {
    interners: CtxtInterners<'lr>,
    pub preds: CommonPreds<'lr>,
    pub types: CommonTypes<'lr>,
}

impl<'lr> LiquidRustCtxt<'lr> {
    pub fn new(arena: &'lr Arena<'lr>) -> Self {
        let interners = CtxtInterners::new(arena);
        let preds = CommonPreds::new(&interners);
        let types = CommonTypes::new(&interners);
        LiquidRustCtxt {
            interners,
            preds,
            types,
        }
    }

    pub fn mk_ty(&'lr self, ty: TyS<'lr>) -> Ty<'lr> {
        self.interners.intern_ty(ty)
    }

    pub fn mk_own_ref(&'lr self, location: Location) -> Ty<'lr> {
        self.mk_ty(TyS::OwnRef(location))
    }

    pub fn mk_refine(&'lr self, ty: BasicType, pred: Pred<'lr>) -> Ty<'lr> {
        self.mk_ty(TyS::Refine { ty, pred })
    }

    pub fn mk_refine_hole(&'lr self, ty: BasicType) -> Ty<'lr> {
        self.mk_ty(TyS::RefineHole { ty })
    }

    pub fn mk_tuple(&'lr self, fields: &[(Field, Ty<'lr>)]) -> Ty<'lr> {
        self.mk_ty(TyS::Tuple(fields.into()))
    }

    pub fn mk_uninit(&'lr self, size: u32) -> Ty<'lr> {
        self.mk_ty(TyS::Uninit(size))
    }

    pub fn mk_ty_for_layout(&'lr self, layout: &TypeLayout) -> Ty<'lr> {
        match layout {
            TypeLayout::Tuple(fields) => {
                let fields = fields
                    .iter()
                    .enumerate()
                    .map(|(i, f)| (Field::nth(i as u32), self.mk_ty_for_layout(f)))
                    .collect();
                self.mk_ty(TyS::Tuple(fields))
            }
            TypeLayout::Block(size) => self.mk_ty(TyS::Uninit(*size)),
        }
    }

    pub fn mk_pred(&'lr self, pred: PredS<'lr>) -> Pred<'lr> {
        self.interners.intern_pred(pred)
    }

    pub fn mk_place(&'lr self, var: Var, projection: &[u32]) -> Pred<'lr> {
        self.mk_pred(PredS::Place {
            var,
            projection: projection.into(),
        })
    }

    pub fn mk_iff(&'lr self, lhs: Pred<'lr>, rhs: Pred<'lr>) -> Pred<'lr> {
        self.mk_pred(PredS::Iff(lhs, rhs))
    }

    pub fn mk_binop(&'lr self, op: BinOp, lhs: Pred<'lr>, rhs: Pred<'lr>) -> Pred<'lr> {
        self.mk_pred(PredS::BinaryOp(op, lhs, rhs))
    }

    pub fn mk_unop(&'lr self, op: UnOp, operand: Pred<'lr>) -> Pred<'lr> {
        self.mk_pred(PredS::UnaryOp(op, operand))
    }

    pub fn mk_const(&'lr self, c: ConstantP) -> Pred<'lr> {
        self.mk_pred(PredS::Constant(c))
    }
}
