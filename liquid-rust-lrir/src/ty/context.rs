use std::cell::RefCell;

use crate::{
    mir::Constant,
    ty::{
        BaseTy, BinOp, BorrowKind, GhostVar, Path, Pred, PredKind, PredS, Refine, Region, Tuple,
        Ty, TyKind, TyS, UnOp, Var,
    },
};

use liquid_rust_common::index::IndexGen;

use hashconsing::{HConsign, HashConsign};

/// Type context used to allocate types.
///
/// During type checking we create and pass around many types. To save on space we intern types using
/// [hashconsing]. [TyCtxt] is the main data structure used to allocate and work with types.
pub struct TyCtxt {
    interner: RefCell<Interner>,
    pub preds: CommonPreds,
    pub types: CommonTypes,
    indexgen: RefCell<IndexGen>,
}

impl TyCtxt {
    pub fn new() -> Self {
        let mut interner = Interner::new();
        let preds = CommonPreds::new(&mut interner);
        let types = CommonTypes::new(&mut interner, &preds);
        TyCtxt {
            interner: RefCell::new(interner),
            preds,
            types,
            indexgen: RefCell::new(IndexGen::new()),
        }
    }

    pub fn fresh_ghost(&self) -> GhostVar {
        self.indexgen.borrow_mut().fresh()
    }

    pub fn mk_ty(&self, ty: TyKind) -> Ty {
        self.interner.borrow_mut().intern_ty(ty)
    }

    pub fn mk_pred(&self, kind: PredKind) -> Pred {
        self.interner.borrow_mut().intern_pred(kind)
    }

    // Types

    pub fn mk_tuple(&self, tup: Tuple) -> Ty {
        self.mk_ty(TyKind::Tuple(tup))
    }

    pub fn mk_uninit(&self, n: usize) -> Ty {
        self.mk_ty(TyKind::Uninit(n))
    }

    pub fn mk_refine<R: Into<Refine>>(&self, bty: BaseTy, refine: R) -> Ty {
        self.mk_ty(TyKind::Refined(bty, refine.into()))
    }

    pub fn mk_ref<R: Into<Region>>(&self, bk: BorrowKind, region: R, gv: GhostVar) -> Ty {
        self.mk_ty(TyKind::Ref(bk, region.into(), gv))
    }

    pub fn selfify(&self, ty: &Ty, path: Path) -> Ty {
        match ty.kind() {
            TyKind::Refined(bty, _) => {
                let pred = self.mk_bin_op(BinOp::Eq(*bty), self.preds.nu(), self.mk_path(path));
                self.mk_refine(*bty, pred)
            }
            TyKind::Tuple(tup) => {
                let tup = tup.map(|i, fld, ty| (*fld, self.selfify(ty, path.extend(i))));
                self.mk_tuple(tup)
            }
            _ => ty.clone(),
        }
    }

    pub fn uninitialize(&self, ty: &Ty) -> Ty {
        match ty.kind() {
            TyKind::Tuple(tup) => {
                let tup = tup.map(|_, fld, ty| (*fld, self.uninitialize(ty)));
                self.mk_tuple(tup)
            }
            _ => self.mk_uninit(ty.size()),
        }
    }

    // Predicates

    pub fn mk_const(&self, c: Constant) -> Pred {
        self.mk_pred(PredKind::Const(c))
    }

    pub fn mk_path(&self, path: Path) -> Pred {
        self.mk_pred(PredKind::Path(path))
    }

    pub fn mk_bin_op(&self, bin_op: BinOp, op1: Pred, op2: Pred) -> Pred {
        self.mk_pred(PredKind::BinaryOp(bin_op, op1, op2))
    }

    pub fn mk_un_op(&self, un_op: UnOp, op: Pred) -> Pred {
        self.mk_pred(PredKind::UnaryOp(un_op, op))
    }
}

impl Default for TyCtxt {
    fn default() -> Self {
        Self::new()
    }
}

/// Common types
pub struct CommonTypes {
    int: Ty,
    bool: Ty,
}

impl CommonTypes {
    fn new(interner: &mut Interner, preds: &CommonPreds) -> Self {
        let mut intern = |typ| interner.intern_ty(typ);
        let mk_refine = |bty| TyKind::Refined(bty, Refine::Pred(preds.tt()));
        CommonTypes {
            int: intern(mk_refine(BaseTy::Int)),
            bool: intern(mk_refine(BaseTy::Bool)),
        }
    }

    pub fn int(&self) -> Ty {
        self.int.clone()
    }

    pub fn bool(&self) -> Ty {
        self.bool.clone()
    }
}

/// Common predicates
pub struct CommonPreds {
    /// PredKind::Path(Path { base: Var::Nu, projs: vec![] })
    nu: Pred,
    /// PredKind::Const(Const { bits: 1, ty: BaseTy::Bool })
    tt: Pred,
    /// PredKind::Const(Const { bits: 0, ty: BaseTy::Bool })
    ff: Pred,
}

impl CommonPreds {
    fn new(interner: &mut Interner) -> Self {
        let mut intern = |pred| interner.intern_pred(pred);
        Self {
            nu: intern(PredKind::Path(Path::from(Var::Nu))),
            tt: intern(PredKind::Const(Constant::from(true))),
            ff: intern(PredKind::Const(Constant::from(false))),
        }
    }

    pub fn nu(&self) -> Pred {
        self.nu.clone()
    }

    pub fn tt(&self) -> Pred {
        self.tt.clone()
    }

    pub fn ff(&self) -> Pred {
        self.ff.clone()
    }
}

struct Interner {
    types: HConsign<TyS>,
    preds: HConsign<PredS>,
}

impl Interner {
    fn new() -> Self {
        Interner {
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
