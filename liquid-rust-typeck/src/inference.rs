use std::{collections::hash_map::Entry, fmt};

use itertools::Itertools;
use liquid_rust_common::{
    disjoint_sets::DisjointSetsMap,
    index::{newtype_index, IndexGen},
};
use liquid_rust_core::ir::{
    BasicBlock, Body, Local, Operand, Place, PlaceElem, Rvalue, Statement, StatementKind,
    Terminator, TerminatorKind, RETURN_PLACE, START_BLOCK,
};
use rustc_hash::FxHashMap;
use rustc_index::bit_set::BitSet;

use crate::intern::{impl_internable, Interned};

type Ty = Interned<TyS>;

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum TyS {
    Refine(ExprIdx),
    Exists,
    Uninit,
    MutRef(Region),
}

pub type Region = Interned<RegionS>;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct RegionS(Vec<Local>);

pub struct InferCtxt<'a, 'tcx> {
    body: &'a Body<'tcx>,
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
    pub fn infer(body: &Body) -> FxHashMap<BasicBlock, DisjointSetsMap<Local, Ty>> {
        let expr_gen = &IndexGen::new();
        let mut env = TypeEnv::new(expr_gen, body.local_decls.len());

        // FIXME: Do not assume everything is a refined bty
        for local in body.args_iter() {
            env.define_local(local, TyS::Refine(expr_gen.fresh()).intern());
        }

        for local in body.vars_and_temps_iter() {
            env.define_local(local, TyS::Uninit.intern());
        }

        env.define_local(RETURN_PLACE, TyS::Uninit.intern());

        let mut cx = InferCtxt {
            body,
            expr_gen,
            visited: BitSet::new_empty(body.basic_blocks.len()),
            bb_envs: FxHashMap::default(),
        };

        // FIXME: Assumming START_BLOCK is not a join point;
        cx.infer_basic_block(&mut env, START_BLOCK);
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
                ..
                // func,
                // args,
                // destination,
            } => todo!(),
            TerminatorKind::SwitchInt { discr: _, targets } => {
                for target in targets.all_targets() {
                    if self.body.is_join_point(*target) {
                        match self.bb_envs.entry(*target) {
                            Entry::Occupied(mut entry) => {
                                entry.get_mut().join_with(env);
                            },
                            Entry::Vacant(entry) => {
                                entry.insert(env.clone());
                            },
                        };
                    } else {
                        self.infer_basic_block(&mut env.clone(), *target);
                    }
                }
            }
            TerminatorKind::Goto { target } => {
                if self.body.is_join_point(*target) {
                    match self.bb_envs.entry(*target) {
                        Entry::Occupied(mut entry) => {
                            entry.get_mut().join_with(env);
                        },
                        Entry::Vacant(entry) => {
                            entry.insert(env.clone());
                        },
                    };
                } else {
                    self.infer_basic_block(env, *target)
                }
            }
        }
    }

    fn infer_rvalue(&self, env: &mut TypeEnv, rvalue: &Rvalue) -> Ty {
        match rvalue {
            Rvalue::Use(op) => self.infer_op(env, op),
            Rvalue::MutRef(place) => TyS::MutRef(env.get_region(place)).intern(),
            Rvalue::BinaryOp(_, _, _) => TyS::Refine(self.expr_gen.fresh()).intern(),
            Rvalue::UnaryOp(_, _) => TyS::Refine(self.expr_gen.fresh()).intern(),
        }
    }

    fn infer_op(&self, env: &mut TypeEnv, op: &Operand) -> Ty {
        match op {
            Operand::Copy(place) => env.copy_place(place),
            Operand::Move(place) => env.move_place(place),
            Operand::Constant(_) => TyS::Refine(self.expr_gen.fresh()).intern(),
        }
    }
}

#[derive(Clone)]
struct TypeEnv<'a> {
    types: DisjointSetsMap<Local, Ty>,
    expr_gen: &'a IndexGen<ExprIdx>,
}

impl TypeEnv<'_> {
    pub fn new(expr_gen: &IndexGen<ExprIdx>, nlocals: usize) -> TypeEnv {
        TypeEnv {
            types: DisjointSetsMap::new(nlocals),
            expr_gen,
        }
    }

    pub fn define_local(&mut self, local: Local, intern: Ty) {
        self.types.insert(local, intern);
    }

    pub fn write_place(&mut self, place: &Place, new_ty: Ty) {
        let (local, ty) = self.walk_place(place);

        match (&*ty, &*new_ty) {
            (TyS::Refine(_) | TyS::Uninit, TyS::Refine(_)) => {
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

        let mut sources = BitSet::new_filled(self.types.len());
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
        self.types.iter_set(local).collect()
    }

    pub fn copy_place(&self, place: &Place) -> Ty {
        let (_, ty) = self.walk_place(place);
        ty
    }

    pub fn move_place(&mut self, place: &Place) -> Ty {
        let mut ty = self.types[place.local].clone();
        self.types[place.local] = TyS::Uninit.intern();
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

    fn walk_place(&self, place: &Place) -> (Local, Ty) {
        let mut local = place.local;
        let mut ty = self.types.get(place.local).unwrap().clone();
        for elem in &place.projection {
            match (elem, &*ty) {
                (PlaceElem::Deref, TyS::MutRef(region)) => {
                    local = region[0];
                    ty = self.types[local].clone();
                }
                _ => {
                    unreachable!("unexpected type: {:?}", ty);
                }
            }
        }
        (local, ty)
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
            TyS::Exists => TyS::Refine(gen.fresh()).intern(),
            TyS::Refine(e) => TyS::Refine(*e).intern(),
            TyS::Uninit => TyS::Uninit.intern(),
            TyS::MutRef(region) => TyS::MutRef(region.clone()).intern(),
        }
    }

    pub fn join(&self, other: &TyS) -> Ty {
        match (self, other) {
            (TyS::Refine(e1), TyS::Refine(e2)) if e1 == e2 => TyS::Refine(*e1).intern(),
            (TyS::Refine(_) | TyS::Exists, TyS::Refine(_) | TyS::Exists) => TyS::Exists.intern(),
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

impl Region {
    fn merge(&self, other: &Region) -> Region {
        RegionS(
            self.0
                .iter()
                .copied()
                .merge(other.0.iter().copied())
                .dedup()
                .collect(),
        )
        .intern()
    }

    fn iter(&self) -> impl Iterator<Item = Local> + '_ {
        self.0.iter().copied()
    }
}

impl RegionS {
    fn intern(self) -> Region {
        Interned::new(self)
    }
}

impl From<Local> for Region {
    fn from(local: Local) -> Self {
        RegionS(vec![local]).intern()
    }
}

impl FromIterator<Local> for Region {
    fn from_iter<T: IntoIterator<Item = Local>>(iter: T) -> Self {
        RegionS(iter.into_iter().collect()).intern()
    }
}

impl std::ops::Index<usize> for Region {
    type Output = Local;

    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl std::ops::Add<&'_ Region> for &'_ Region {
    type Output = Region;

    fn add(self, rhs: &Region) -> Self::Output {
        self.merge(rhs)
    }
}

impl_internable!(TyS, RegionS);

impl fmt::Debug for TypeEnv<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.types, f)
    }
}

impl fmt::Debug for TyS {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Refine(e) => write!(f, "refine({:?})", e),
            Self::Uninit => write!(f, "uninit"),
            Self::MutRef(region) => write!(f, "ref<{:?}>", region),
            TyS::Exists => write!(f, "exists"),
        }
    }
}

impl fmt::Debug for RegionS {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0.len() == 1 {
            write!(f, "{:?}", self.0[0])
        } else {
            write!(f, "{{{:?}}}", self.0.iter().format(","))
        }
    }
}
