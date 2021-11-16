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
    ty::{self as core, BaseTy, FnSig},
};
use rustc_hash::FxHashMap;
use rustc_index::bit_set::BitSet;

use crate::{
    global_env::GlobalEnv,
    intern::{impl_internable, Interned},
    ty::{RVid, Region},
};

pub type Ty = Interned<TyS>;

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum TyS {
    Refine(BaseTy, ExprIdx),
    Exists(BaseTy),
    Uninit,
    MutRef(Region),
}

pub struct InferCtxt<'a, 'tcx> {
    body: &'a Body<'tcx>,
    global_env: &'a GlobalEnv,
    expr_gen: &'a IndexGen<ExprIdx>,
    visited: BitSet<BasicBlock>,
    bb_envs: FxHashMap<BasicBlock, TypeEnv<'a>>,
}

newtype_index! {
    pub struct ExprIdx {
        DEBUG_FORMAT = "e{}"
    }
}

impl<'a> InferCtxt<'a, '_> {
    pub fn infer(
        global_env: &GlobalEnv,
        body: &Body,
        fn_sig: &FnSig,
    ) -> FxHashMap<BasicBlock, DisjointSetsMap<RVid, Ty>> {
        let expr_gen = &IndexGen::new();
        let rvid_gen = &IndexGen::new();
        rvid_gen.skip(body.local_decls.len());

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
                args,
                destination,
            } => {
                let fn_sig = self.global_env.lookup_fn_sig(*func);
                let actuals = args
                    .iter()
                    .map(|arg| self.infer_operand(env, arg))
                    .collect_vec();

                let subst = infer_subst(&actuals, &fn_sig.args);
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
                TyS::Refine(*bty1, self.expr_gen.fresh()).intern()
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
                TyS::Refine(*bty, self.expr_gen.fresh()).intern()
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
        let (local, ty) = self.walk_place(place);

        match (&*ty, &*new_ty) {
            (TyS::Refine(..) | TyS::Uninit, TyS::Refine(..)) => {
                self.types.insert(local, new_ty);
            }
            (TyS::Uninit, TyS::MutRef(_)) => {
                self.types.insert(local, new_ty);
            }
            (TyS::MutRef(_), TyS::MutRef(_)) => {
                let ty = ty.join(&new_ty);
                self.types.insert(local, ty.clone());
                self.union_cascade(ty, true);
            }
            _ => unreachable!("unexpected types: `{:?}` `{:?}`", ty, new_ty),
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
            TyS::Exists(bty) => TyS::Refine(*bty, gen.fresh()).intern(),
            TyS::Refine(bty, e) => TyS::Refine(*bty, *e).intern(),
            TyS::Uninit => TyS::Uninit.intern(),
            TyS::MutRef(region) => TyS::MutRef(region.clone()).intern(),
        }
    }

    pub fn join(&self, other: &TyS) -> Ty {
        match (self, other) {
            (TyS::Refine(bty1, e1), TyS::Refine(bty2, e2)) if e1 == e2 => {
                debug_assert_eq!(bty1, bty2);
                TyS::Refine(*bty1, *e1).intern()
            }
            (
                TyS::Refine(bty1, _) | TyS::Exists(bty1),
                TyS::Refine(bty2, _) | TyS::Exists(bty2),
            ) => {
                debug_assert_eq!(bty1, bty2);
                TyS::Exists(*bty1).intern()
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

type RegionSubst = FxHashMap<core::Name, Region>;

fn infer_subst(actuals: &[Ty], formals: &[core::Ty]) -> RegionSubst {
    assert!(actuals.len() == formals.len());

    let mut subst = FxHashMap::default();
    for (actual, formal) in actuals.iter().zip(formals) {
        match (&**actual, formal) {
            (TyS::MutRef(region1), core::Ty::MutRef(region2)) => {
                match subst.insert(region2.name, region1.clone()) {
                    Some(old_region) if &old_region != region1 => {
                        todo!("report this error");
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }
    subst
}

fn lower(
    fn_sig: &FnSig,
    gen: &IndexGen<ExprIdx>,
    rvid_gen: &IndexGen<RVid>,
) -> (Vec<Ty>, Vec<Ty>, Ty, Vec<(Region, Ty)>) {
    let mut region_subst = FxHashMap::default();

    let requires = fn_sig
        .requires
        .iter()
        .map(|(name, ty)| {
            let rvid = rvid_gen.fresh();
            let ty = lower_ty(ty, gen, &region_subst);
            region_subst.insert(name.name, Region::from(rvid));
            ty
        })
        .collect();

    let args = fn_sig
        .args
        .iter()
        .map(|arg| lower_ty(arg, gen, &region_subst))
        .collect();

    let ret = lower_ty(&fn_sig.ret, gen, &region_subst);

    let ensures = fn_sig
        .ensures
        .iter()
        .map(|(name, ty)| {
            let ty = lower_ty(ty, gen, &region_subst);
            (region_subst[&name.name].clone(), ty)
        })
        .collect();

    (requires, args, ret, ensures)
}

fn lower_with_subst(
    fn_sig: &FnSig,
    gen: &IndexGen<ExprIdx>,
    region_subst: &RegionSubst,
) -> (Vec<(Region, Ty)>, Vec<Ty>, Ty, Vec<(Region, Ty)>) {
    let requires = fn_sig
        .requires
        .iter()
        .map(|(name, ty)| {
            (
                region_subst[&name.name].clone(),
                lower_ty(ty, gen, &region_subst),
            )
        })
        .collect();

    let args = fn_sig
        .args
        .iter()
        .map(|arg| lower_ty(arg, gen, &region_subst))
        .collect();

    let ret = lower_ty(&fn_sig.ret, gen, &region_subst);

    let ensures = fn_sig
        .ensures
        .iter()
        .map(|(name, ty)| {
            (
                region_subst[&name.name].clone(),
                lower_ty(ty, gen, &region_subst),
            )
        })
        .collect();

    (requires, args, ret, ensures)
}

fn lower_ty(ty: &core::Ty, gen: &IndexGen<ExprIdx>, region_subst: &RegionSubst) -> Ty {
    match ty {
        core::Ty::Refine(bty, _) => TyS::Refine(*bty, gen.fresh()).intern(),
        core::Ty::Exists(bty, _, _) => TyS::Exists(*bty).intern(),
        core::Ty::MutRef(region) => TyS::MutRef(region_subst[&region.name].clone()).intern(),
    }
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
            Self::Uninit => write!(f, "uninit"),
            Self::MutRef(region) => write!(f, "ref<{:?}>", region),
            TyS::Exists(bty) => write!(f, "{:?}{{k}}", bty),
        }
    }
}

impl_internable!(TyS);
