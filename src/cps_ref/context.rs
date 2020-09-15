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

    fn intern_ty(&'lr self, ty: TyS<'lr>) -> Ty<'lr> {
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
                var: Var::nu(),
                projection: vec![],
            }),
            tt: mk(PredS::Constant(Constant::Bool(true))),
            ff: mk(PredS::Constant(Constant::Bool(false))),
        }
    }
}

pub struct LiquidRustCtxt<'lr> {
    interners: CtxtInterners<'lr>,
    pub preds: CommonPreds<'lr>,
}

impl<'lr> LiquidRustCtxt<'lr> {
    pub fn new(arena: &'lr Arena<'lr>) -> Self {
        let interners = CtxtInterners::new(arena);
        let preds = CommonPreds::new(&interners);
        LiquidRustCtxt { interners, preds }
    }

    pub fn mk_ty(&'lr self, ty: TyS<'lr>) -> Ty<'lr> {
        self.interners.intern_ty(ty)
    }

    pub fn mk_refine(&'lr self, bind: Var, ty: BasicType, pred: Pred<'lr>) -> Ty<'lr> {
        self.mk_ty(TyS::Refine { bind, ty, pred })
    }

    pub fn mk_tuple(&'lr self, fields: &[(Var, Ty<'lr>)]) -> Ty<'lr> {
        self.mk_ty(TyS::Tuple(fields.into()))
    }

    pub fn mk_pred(&'lr self, pred: PredS<'lr>) -> Pred<'lr> {
        self.interners.intern_pred(pred)
    }

    pub fn mk_pred_place(&'lr self, var: Var, projection: &[u32]) -> Pred<'lr> {
        self.mk_pred(PredS::Place {
            var,
            projection: projection.into(),
        })
    }

    pub fn mk_bin_op(&'lr self, op: BinOp, lhs: Pred<'lr>, rhs: Pred<'lr>) -> Pred<'lr> {
        self.mk_pred(PredS::BinaryOp(op, lhs, rhs))
    }

    pub fn mk_const(&'lr self, c: Constant) -> Pred<'lr> {
        self.mk_pred(PredS::Constant(c))
    }
}
