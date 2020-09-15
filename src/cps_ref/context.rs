use rustc_arena::TypedArena;
use rustc_data_structures::sharded::ShardedHashMap;

use super::ast::*;

#[derive(Default)]
struct Arena<'lr> {
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

#[derive(Default)]
struct CtxtInterners<'lr> {
    types: ShardedHashMap<Ty<'lr>, ()>,
    preds: ShardedHashMap<Pred<'lr>, ()>,
}

#[derive(Default)]
pub struct LiquidRustCtxt<'lr> {
    arena: Arena<'lr>,
    interners: CtxtInterners<'lr>,
}

impl<'lr> LiquidRustCtxt<'lr> {
    pub fn mk_ty(&'lr self, kind: TyS<'lr>) -> Ty<'lr> {
        self.interners
            .types
            .intern(kind, |kind| self.arena.alloc_ty(kind))
    }

    pub fn mk_pred(&'lr self, pred: PredS<'lr>) -> Pred<'lr> {
        self.interners
            .preds
            .intern(pred, |pred| self.arena.alloc_pred(pred))
    }
}
