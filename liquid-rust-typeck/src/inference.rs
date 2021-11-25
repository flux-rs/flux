use std::{collections::hash_map::Entry, fmt};

use itertools::Itertools;
use liquid_rust_common::{
    disjoint_sets::DisjointSetsMap,
    index::{newtype_index, Idx, IndexGen},
};
use liquid_rust_core::{
    ir::{
        self, BasicBlock, Body, Local, Operand, Place, PlaceElem, Rvalue, Statement, StatementKind,
        Terminator, TerminatorKind, RETURN_PLACE, START_BLOCK,
    },
    ty::{self as core, FnSig, ParamTy},
};
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_index::bit_set::BitSet;

use crate::{
    global_env::GlobalEnv,
    intern::{impl_internable, Interned},
    ty::{IntTy, RVid, Region, UintTy},
};

pub type Ty = Interned<TyS>;

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum TyS {
    Refine(BaseTy, ExprIdx),
    Exists(BaseTy),
    Uninit,
    MutRef(Region),
    Param(ParamTy),
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum BaseTy {
    Int(IntTy),
    Uint(UintTy),
    Bool,
    Adt(DefId, Vec<Ty>),
}

pub struct InferCtxt<'a, 'tcx> {
    body: &'a Body<'tcx>,
    global_env: &'a GlobalEnv<'tcx>,
    expr_gen: &'a IndexGen<ExprIdx>,
    visited: BitSet<BasicBlock>,
    bb_envs: FxHashMap<BasicBlock, TypeEnv<'a>>,
}

newtype_index! {
    pub struct ExprIdx {
        DEBUG_FORMAT = "e{}"
    }
}

impl<'a, 'tcx> InferCtxt<'a, 'tcx> {
    pub fn infer(
        global_env: &GlobalEnv<'tcx>,
        body: &Body<'tcx>,
        fn_sig: &FnSig,
    ) -> FxHashMap<BasicBlock, DisjointSetsMap<RVid, Ty>> {
        let expr_gen = &IndexGen::new();
        let rvid_gen = &IndexGen::new();
        rvid_gen.skip(body.nlocals);

        let mut env = TypeEnv::new(expr_gen);

        let (requires, args, ret, ensures) = lower(fn_sig, expr_gen, rvid_gen);

        // Return place
        env.push_region(TyS::Uninit.intern());

        // Arguments
        for ty in args {
            env.push_region(ty.unpack(expr_gen));
        }

        // Vars and temps
        for _ in body.vars_and_temps_iter() {
            env.push_region(TyS::Uninit.intern());
        }

        for ty in requires {
            env.push_region(ty);
        }

        let mut cx = InferCtxt {
            body,
            global_env,
            expr_gen,
            visited: BitSet::new_empty(body.basic_blocks.len()),
            bb_envs: FxHashMap::default(),
        };

        cx.infer_goto(&mut env, START_BLOCK);
        for bb in body.reverse_postorder() {
            if !cx.visited.contains(bb) {
                let mut env = cx.bb_envs.get(&bb).unwrap().clone();
                env.unpack();
                cx.infer_basic_block(&mut env, bb);
            }
        }
        cx.bb_envs
            .into_iter()
            .map(|(bb, env)| (bb, env.types))
            .collect()
    }

    fn infer_basic_block(&mut self, env: &mut TypeEnv<'a>, bb: BasicBlock) {
        self.visited.insert(bb);

        let data = &self.body.basic_blocks[bb];
        for stmt in &data.statements {
            self.infer_statement(env, stmt);
        }
        if let Some(terminator) = &data.terminator {
            self.infer_terminator(env, terminator);
        }
    }

    fn infer_statement(&self, env: &mut TypeEnv, stmt: &Statement) {
        match &stmt.kind {
            StatementKind::Assign(p, rvalue) => {
                let ty = self.infer_rvalue(env, rvalue);
                // OWNERSHIP SAFETY CHECK
                env.write_place(p, ty);
            }
            StatementKind::Nop => {}
        }
    }

    fn infer_terminator(&mut self, env: &mut TypeEnv<'a>, terminator: &Terminator) {
        match &terminator.kind {
            TerminatorKind::Return => {}
            TerminatorKind::Call {
                func,
                substs,
                args,
                destination,
            } => {
                let fn_sig = self.global_env.lookup_fn_sig(*func);
                let actuals = args
                    .iter()
                    .map(|arg| self.infer_operand(env, arg))
                    .collect_vec();

                let mut subst = Subst::new(self.expr_gen, substs);
                subst.infer_from_fn_call(&actuals, &fn_sig.args);
                let (requires, args, ret, ensures) =
                    lower_with_subst(&fn_sig, self.expr_gen, &subst);

                for (region, updated_ty) in ensures {
                    env.update_region(region[0], updated_ty);
                }

                if let Some((place, target)) = destination {
                    env.write_place(place, ret.unpack(self.expr_gen));
                    self.infer_goto(env, *target);
                }
            }
            TerminatorKind::SwitchInt { discr: _, targets } => {
                for (_, target) in targets.iter() {
                    self.infer_goto(&mut env.clone(), target);
                }
                self.infer_goto(env, targets.otherwise());
            }
            TerminatorKind::Goto { target } => {
                self.infer_goto(env, *target);
            }
            TerminatorKind::Drop { place, target } => {
                let _ = env.move_place(place);
                self.infer_goto(env, *target);
            }
        }
    }

    fn infer_goto(&mut self, env: &mut TypeEnv<'a>, target: BasicBlock) {
        if self.body.is_join_point(target) {
            match self.bb_envs.entry(target) {
                Entry::Occupied(mut entry) => {
                    entry.get_mut().join_with(env);
                }
                Entry::Vacant(entry) => {
                    entry.insert(env.clone());
                }
            };
        } else {
            self.infer_basic_block(env, target)
        }
    }

    fn infer_rvalue(&self, env: &mut TypeEnv, rvalue: &Rvalue) -> Ty {
        match rvalue {
            Rvalue::Use(op) => self.infer_operand(env, op),
            Rvalue::MutRef(place) => TyS::MutRef(env.get_region(place)).intern(),
            Rvalue::BinaryOp(bin_op, op1, op2) => self.infer_binary_op(env, *bin_op, op1, op2),
            Rvalue::UnaryOp(un_op, op) => self.infer_unary_op(env, *un_op, op),
        }
    }

    fn infer_binary_op(
        &self,
        env: &mut TypeEnv,
        bin_op: ir::BinOp,
        op1: &Operand,
        op2: &Operand,
    ) -> Ty {
        let ty1 = self.infer_operand(env, op1);
        let ty2 = self.infer_operand(env, op2);
        match (bin_op, &*ty1, &*ty2) {
            (ir::BinOp::Add | ir::BinOp::Sub, TyS::Refine(bty1, _), TyS::Refine(bty2, _)) => {
                debug_assert_eq!(bty1, bty2);
                TyS::Refine(bty1.clone(), self.expr_gen.fresh()).intern()
            }
            (ir::BinOp::Gt | ir::BinOp::Lt, TyS::Refine(bty1, _), TyS::Refine(bty2, _)) => {
                debug_assert_eq!(bty1, bty2);
                TyS::Refine(BaseTy::Bool, self.expr_gen.fresh()).intern()
            }
            _ => {
                unreachable!("unexpected types: `{:?}` `{:?}`", ty1, ty2);
            }
        }
    }

    fn infer_unary_op(&self, env: &mut TypeEnv, un_op: ir::UnOp, op: &Operand) -> Ty {
        let ty = self.infer_operand(env, op);
        match (un_op, &*ty) {
            (ir::UnOp::Not, TyS::Refine(BaseTy::Bool, _)) => {
                TyS::Refine(BaseTy::Bool, self.expr_gen.fresh()).intern()
            }
            (ir::UnOp::Neg, TyS::Refine(bty, _)) => {
                TyS::Refine(bty.clone(), self.expr_gen.fresh()).intern()
            }
            _ => {
                unreachable!("unexpected type: `{:?}`", ty);
            }
        }
    }

    fn infer_operand(&self, env: &mut TypeEnv, op: &Operand) -> Ty {
        match op {
            Operand::Copy(place) => env.copy_place(place),
            Operand::Move(place) => env.move_place(place),
            Operand::Constant(c) => self.infer_constant(c),
        }
    }

    fn infer_constant(&self, c: &ir::Constant) -> Ty {
        match c {
            ir::Constant::Int(_, int_ty) => {
                TyS::Refine(BaseTy::Int(*int_ty), self.expr_gen.fresh()).intern()
            }
            ir::Constant::Uint(_, uint_ty) => {
                TyS::Refine(BaseTy::Uint(*uint_ty), self.expr_gen.fresh()).intern()
            }
            ir::Constant::Bool(_) => TyS::Refine(BaseTy::Bool, self.expr_gen.fresh()).intern(),
        }
    }
}

#[derive(Clone)]
struct TypeEnv<'a> {
    types: DisjointSetsMap<RVid, Ty>,
    expr_gen: &'a IndexGen<ExprIdx>,
}

impl TypeEnv<'_> {
    pub fn new(expr_gen: &IndexGen<ExprIdx>) -> TypeEnv {
        TypeEnv {
            types: DisjointSetsMap::new(),
            expr_gen,
        }
    }

    pub fn push_region(&mut self, ty: Ty) {
        self.types.push(ty);
    }

    pub fn update_region(&mut self, rvid: RVid, ty: Ty) {
        self.types.insert(rvid, ty);
    }

    pub fn write_place(&mut self, place: &Place, new_ty: Ty) {
        let (rvid, ty) = self.walk_place(place);

        match &*ty {
            TyS::Refine(..) | TyS::Uninit | TyS::Param(_) => {
                self.types.insert(rvid, new_ty);
            }
            TyS::MutRef(_) => {
                let ty = ty.join(&new_ty);
                self.types.insert(rvid, ty.clone());
                self.union_cascade(ty, true);
            }
            TyS::Exists(_) => {
                unreachable!("unpacked existential: `{:?}`", ty);
            }
        }
    }

    pub fn join_with(&mut self, other: &TypeEnv) {
        self.types
            .merge_with(&other.types, |ty1, ty2| ty1.join(&ty2));

        let mut sources = BitSet::new_filled(self.types.size());
        for ty in self.types.values() {
            match &**ty {
                TyS::MutRef(region) => {
                    for local in region.iter() {
                        sources.remove(local);
                    }
                }
                _ => {}
            }
        }
        let sources = sources
            .iter()
            .dedup_by(|a, b| self.types.same_set(*a, *b))
            .collect_vec();
        for source in sources {
            self.union_cascade(self.types[source].clone(), false);
        }
    }

    pub fn get_region(&self, place: &Place) -> Region {
        let (local, _) = self.walk_place(place);
        self.types.set(local).collect()
    }

    pub fn copy_place(&self, place: &Place) -> Ty {
        let (_, ty) = self.walk_place(place);
        ty
    }

    pub fn move_place(&mut self, place: &Place) -> Ty {
        let mut ty = self.types[RVid::new(place.local.as_usize())].clone();
        self.types[RVid::new(place.local.as_usize())] = TyS::Uninit.intern();
        for elem in &place.projection {
            match (elem, &*ty) {
                (PlaceElem::Deref, TyS::MutRef(region)) => {
                    self.types[region[0]] = TyS::Uninit.intern();
                    ty = self.types[region[0]].clone();
                }
                _ => unreachable!("unexpected type: {:?}", ty),
            }
        }
        ty
    }

    fn walk_place(&self, place: &Place) -> (RVid, Ty) {
        let mut rvid = RVid::new(place.local.as_usize());
        let mut ty = self.types[rvid].clone();
        for elem in &place.projection {
            match (elem, &*ty) {
                (PlaceElem::Deref, TyS::MutRef(region)) => {
                    rvid = region[0];
                    ty = self.types[rvid].clone();
                }
                _ => {
                    unreachable!("unexpected type: {:?}", ty);
                }
            }
        }
        (rvid, ty)
    }

    fn union_cascade(&mut self, ty: Ty, unpack: bool) {
        match &*ty {
            TyS::MutRef(region) => {
                self.types.multi_union(region.iter(), |ty1, ty2| {
                    if unpack {
                        ty1.join(&ty2).unpack(self.expr_gen)
                    } else {
                        ty1.join(&ty2)
                    }
                });
                let ty = self.types[region[0]].clone();
                self.union_cascade(ty, unpack);
            }
            _ => {}
        }
    }

    fn unpack(&mut self) {
        for ty in self.types.values_mut() {
            *ty = ty.unpack(self.expr_gen);
        }
    }
}

impl TyS {
    pub fn intern(self) -> Ty {
        Interned::new(self)
    }

    pub fn unpack(&self, gen: &IndexGen<ExprIdx>) -> Ty {
        match self {
            TyS::Exists(bty) => TyS::Refine(bty.clone(), gen.fresh()).intern(),
            TyS::Refine(bty, e) => TyS::Refine(bty.clone(), *e).intern(),
            TyS::Uninit => TyS::Uninit.intern(),
            TyS::MutRef(region) => TyS::MutRef(region.clone()).intern(),
            TyS::Param(param) => TyS::Param(*param).intern(),
        }
    }

    pub fn join(&self, other: &TyS) -> Ty {
        match (self, other) {
            (TyS::Refine(bty1, e1), TyS::Refine(bty2, e2)) if e1 == e2 => {
                debug_assert_eq!(bty1, bty2);
                TyS::Refine(bty1.clone(), *e1).intern()
            }
            (
                TyS::Refine(bty1, _) | TyS::Exists(bty1),
                TyS::Refine(bty2, _) | TyS::Exists(bty2),
            ) => {
                debug_assert_eq!(bty1, bty2);
                TyS::Exists(bty1.clone()).intern()
            }
            (TyS::MutRef(region1), TyS::MutRef(region2)) => TyS::MutRef(region1 + region2).intern(),
            (TyS::Uninit, _) | (_, TyS::Uninit) => TyS::Uninit.intern(),
            _ => {
                panic!(
                    "join between incompatible types: `{:?}` `{:?}`",
                    self, other
                )
            }
        }
    }
}

struct Subst {
    regions: FxHashMap<core::Name, Region>,
    types: Vec<Ty>,
}

fn lower(
    fn_sig: &FnSig,
    gen: &IndexGen<ExprIdx>,
    rvid_gen: &IndexGen<RVid>,
) -> (Vec<Ty>, Vec<Ty>, Ty, Vec<(Region, Ty)>) {
    let mut subst = Subst::empty();

    let requires = fn_sig
        .requires
        .iter()
        .map(|(name, ty)| {
            let rvid = rvid_gen.fresh();
            let ty = subst.lower_ty(gen, ty);
            subst.regions.insert(*name, Region::from(rvid));
            ty
        })
        .collect();

    let args = fn_sig
        .args
        .iter()
        .map(|arg| subst.lower_ty(gen, arg))
        .collect();

    let ret = subst.lower_ty(gen, &fn_sig.ret);

    let ensures = fn_sig
        .ensures
        .iter()
        .map(|(name, ty)| {
            let ty = subst.lower_ty(gen, ty);
            (subst.lower_region(*name), ty)
        })
        .collect();

    (requires, args, ret, ensures)
}

fn lower_with_subst(
    fn_sig: &FnSig,
    gen: &IndexGen<ExprIdx>,
    subst: &Subst,
) -> (Vec<(Region, Ty)>, Vec<Ty>, Ty, Vec<(Region, Ty)>) {
    let requires = fn_sig
        .requires
        .iter()
        .map(|(name, ty)| (subst.lower_region(*name), subst.lower_ty(gen, ty)))
        .collect();

    let args = fn_sig
        .args
        .iter()
        .map(|arg| subst.lower_ty(gen, arg))
        .collect();

    let ret = subst.lower_ty(gen, &fn_sig.ret);

    let ensures = fn_sig
        .ensures
        .iter()
        .map(|(name, ty)| (subst.lower_region(*name), subst.lower_ty(gen, ty)))
        .collect();

    (requires, args, ret, ensures)
}

impl fmt::Debug for TypeEnv<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.types, f)
    }
}

impl fmt::Debug for TyS {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Refine(bty, e) => write!(f, "{:?}@{:?}", bty, e),
            Self::Exists(bty) => write!(f, "{:?}{{v: _}}", bty,),
            Self::Uninit => write!(f, "uninit"),
            Self::MutRef(region) => write!(f, "ref<{:?}>", region),
            Self::Param(ParamTy { name, .. }) => write!(f, "{:?}", name),
        }
    }
}

impl Subst {
    fn new(gen: &IndexGen<ExprIdx>, types: &[core::Ty]) -> Subst {
        let mut empty = Subst::empty();
        let types = types.iter().map(|ty| empty.lower_ty(gen, ty)).collect();
        Subst {
            regions: FxHashMap::default(),
            types,
        }
    }

    fn empty() -> Subst {
        Subst {
            regions: FxHashMap::default(),
            types: vec![],
        }
    }

    fn lower_ty(&self, gen: &IndexGen<ExprIdx>, ty: &core::Ty) -> Ty {
        match ty {
            core::Ty::Refine(bty, _) => {
                TyS::Refine(self.lower_base_ty(gen, bty), gen.fresh()).intern()
            }
            core::Ty::Exists(bty, _) => TyS::Exists(self.lower_base_ty(gen, bty)).intern(),
            core::Ty::MutRef(region) => TyS::MutRef(self.regions[region].clone()).intern(),
            core::Ty::Param(param) => self
                .types
                .get(param.index as usize)
                .cloned()
                .unwrap_or_else(|| TyS::Param(*param).intern()),
        }
    }

    fn lower_base_ty(&self, gen: &IndexGen<ExprIdx>, bty: &core::BaseTy) -> BaseTy {
        match bty {
            core::BaseTy::Int(int_ty) => BaseTy::Int(*int_ty),
            core::BaseTy::Uint(uint_ty) => BaseTy::Uint(*uint_ty),
            core::BaseTy::Bool => BaseTy::Bool,
            core::BaseTy::Adt(did, substs) => {
                let substs = substs.iter().map(|ty| self.lower_ty(gen, ty)).collect();
                BaseTy::Adt(*did, substs)
            }
        }
    }

    fn lower_region(&self, region: core::Name) -> Region {
        self.regions[&region].clone()
    }

    fn infer_from_fn_call(&mut self, actuals: &[Ty], formals: &[core::Ty]) {
        assert!(actuals.len() == formals.len());

        for (actual, formal) in actuals.iter().zip(formals) {
            self.infer_from_tys(actual.clone(), formal);
        }
    }

    fn infer_from_tys(&mut self, ty1: Ty, ty2: &core::Ty) {
        match (&*ty1, ty2) {
            (TyS::MutRef(region1), core::Ty::MutRef(region2)) => {
                match self.regions.insert(*region2, region1.clone()) {
                    Some(old_region) if &old_region != region1 => {
                        todo!("report this error");
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }
}

impl fmt::Debug for BaseTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Int(int_ty) => write!(f, "{}", int_ty.name_str()),
            Self::Uint(uint_ty) => write!(f, "{}", uint_ty.name_str()),
            Self::Bool => write!(f, "bool"),
            Self::Adt(did, args) => {
                if args.is_empty() {
                    write!(f, "{:?}", did)
                } else {
                    write!(f, "{:?}<{:?}>", did, args.iter().format(", "))
                }
            }
        }
    }
}

impl_internable!(TyS);
