use std::{cell::Cell, cmp::Ordering, collections::hash_map::Entry, fmt};

use itertools::Itertools;
use liquid_rust_common::index::{newtype_index, IndexGen, IndexVec};
use liquid_rust_core::ir::{
    BasicBlock, Body, Local, Operand, Place, PlaceElem, Rvalue, Statement, StatementKind,
    Terminator, TerminatorKind, RETURN_PLACE, START_BLOCK,
};
use rustc_hash::FxHashMap;
use rustc_index::bit_set::BitSet;

use crate::intern::{impl_internable, Interned};

type Ty = Interned<TyS>;

#[derive(Clone, PartialEq, Eq, Hash)]
enum TyS {
    Refine(ExprIdx),
    Exists,
    Uninit,
    MutRef(Region),
}

type Region = Interned<RegionS>;

#[derive(Clone, PartialEq, Eq, Hash)]
struct RegionS(Vec<Local>);

pub struct InferCtxt<'a, 'tcx> {
    body: &'a Body<'tcx>,
    expr_gen: &'a IndexGen<ExprIdx>,
    visited: BitSet<BasicBlock>,
    bb_envs: FxHashMap<BasicBlock, BasicBlockEnv>,
}

newtype_index! {
    struct ExprIdx {
        DEBUG_FORMAT = "e{}"
    }
}

impl InferCtxt<'_, '_> {
    pub fn infer(body: &Body) {
        let expr_gen = &IndexGen::new();
        let mut env = TypeEnv::new(expr_gen, body.local_decls.len());

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
                println!("------------------------------------");
                println!("{:?}", bb);
                println!("{:?}", cx.bb_envs[&bb]);
                // cx.infer_basic_block(&mut env, bb);
            }
        }
    }

    fn infer_basic_block(&mut self, env: &mut TypeEnv, bb: BasicBlock) {
        self.visited.insert(bb);
        println!("------------------------------------");
        println!("{:?}", bb);
        println!("{:?}", env);

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
                println!("{:?}", stmt);
                let ty = self.infer_rvalue(env, rvalue);
                // OWNERSHIP SAFETY CHECK
                env.write_place(p, ty);
                println!("{:?}", env);
            }
            StatementKind::Nop => {}
        }
    }

    fn infer_terminator(&mut self, env: &mut TypeEnv, terminator: &Terminator) {
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
                                entry.insert(BasicBlockEnv::from_env(env));
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
                            println!("===================================");
                            println!("joining");
                            println!("{:?}", entry.get());
                            println!("{:?}", env);
                            entry.get_mut().join_with(env);
                            println!("{:?}", entry.get());
                            println!("===================================");
                        },
                        Entry::Vacant(entry) => {
                            entry.insert(BasicBlockEnv::from_env(env));
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
            // Rvalue::MutRef(local) => TyS::MutRef(Region::from(*local)).intern(),
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
    types: FxHashMap<Local, Ty>,
    expr_gen: &'a IndexGen<ExprIdx>,
    // Union by rank
    parent: IndexVec<Local, Cell<Local>>,
    rank: IndexVec<Local, usize>,
    next: IndexVec<Local, Local>,
}

impl TypeEnv<'_> {
    pub fn new(expr_gen: &IndexGen<ExprIdx>, nlocals: usize) -> TypeEnv {
        TypeEnv {
            types: FxHashMap::default(),
            expr_gen,
            parent: IndexVec::from_fn_n(|local| Cell::new(local), nlocals),
            rank: IndexVec::from_elem_n(0, nlocals),
            next: IndexVec::from_fn_n(|local| local, nlocals),
        }
    }

    pub fn define_local(&mut self, local: Local, intern: Ty) {
        self.types.insert(local, intern);
    }

    pub fn write_place(&mut self, place: &Place, new_ty: Ty) {
        let (key, ty) = self.walk_place(place);

        match (&*ty, &*new_ty) {
            (TyS::Refine(_) | TyS::Uninit, TyS::Refine(_)) => {
                self.types.insert(key, new_ty);
            }
            (TyS::Uninit, TyS::MutRef(_)) => {
                self.types.insert(key, new_ty);
            }
            (TyS::MutRef(_), TyS::MutRef(_)) => {
                let new_ty = self.join(ty, new_ty);
                self.types.insert(key, new_ty);
            }
            _ => unreachable!("unexpected types: `{:?}` `{:?}`", ty, new_ty),
        }
    }

    pub fn get_region(&self, place: &Place) -> Region {
        let (root, _) = self.walk_place(place);
        let mut locals = vec![root];
        let mut current = root;
        while self.next[current] != root {
            current = self.next[current];
            locals.push(current);
        }
        locals.into_iter().collect()
    }

    pub fn copy_place(&self, place: &Place) -> Ty {
        let (_, ty) = self.walk_place(place);
        ty
    }

    pub fn move_place(&mut self, place: &Place) -> Ty {
        let mut ty = self.lookup(place.local);
        self.set(place.local, TyS::Uninit.intern());
        for elem in &place.projection {
            match (elem, &*ty) {
                (PlaceElem::Deref, TyS::MutRef(region)) => {
                    debug_assert!(region.iter().map(|local| self.find(local)).all_equal());
                    self.set(region[0], TyS::Uninit.intern());
                    ty = self.lookup(region[0]);
                }
                _ => unreachable!("unexpected type: {:?}", ty),
            }
        }
        ty
    }

    fn walk_place(&self, place: &Place) -> (Local, Ty) {
        let mut root = self.find(place.local);
        let mut ty = self.types[&root].clone();
        for elem in &place.projection {
            match (elem, &*ty) {
                (PlaceElem::Deref, TyS::MutRef(region)) => {
                    // The region in the reference should always be a subset of one of regions in the env.
                    debug_assert!(region.iter().map(|local| self.find(local)).all_equal());
                    root = self.find(region[0]);
                    ty = self.types[&root].clone();
                }
                _ => {
                    unreachable!("unexpected type: {:?}", ty);
                }
            }
        }
        (root, ty)
    }

    fn join(&mut self, ty1: Ty, ty2: Ty) -> Ty {
        match (&*ty1, &*ty2) {
            (TyS::Refine(e1), TyS::Refine(e2)) => {
                if e1 == e2 {
                    ty1
                } else {
                    TyS::Refine(self.expr_gen.fresh()).intern()
                }
            }
            (TyS::MutRef(region1), TyS::MutRef(region2)) => {
                debug_assert!(region1.iter().map(|local| self.find(local)).all_equal());
                debug_assert!(region2.iter().map(|local| self.find(local)).all_equal());
                self.union(region1[0], region2[0]);
                TyS::MutRef(region1 + region2).intern()
            }
            _ => {
                unreachable!("unexpected types: `{:?}` `{:?}`", ty1, ty2);
            }
        }
    }

    fn union(&mut self, local1: Local, local2: Local) {
        let root1 = self.find(local1);
        let root2 = self.find(local2);

        if root1 == root2 {
            return;
        }

        self.next.swap(root1, root2);

        let root = match Ord::cmp(&self.rank[root1], &self.rank[root2]) {
            Ordering::Less => {
                self.parent[root1].set(root2);
                root2
            }
            Ordering::Equal => {
                *self.parent[root1].get_mut() = root2;
                self.rank[root2] += 1;
                root2
            }
            Ordering::Greater => {
                self.parent[root2].set(root1);
                root1
            }
        };
        let ty1 = self.types.remove(&root1).unwrap();
        let ty2 = self.types.remove(&root2).unwrap();
        let ty = self.join(ty1, ty2);
        self.types.insert(root, ty);
    }

    fn find(&self, local: Local) -> Local {
        let parent = self.parent[local].get();
        if parent != local {
            self.parent[local].set(self.find(parent));
        }
        self.parent[local].get()
    }

    fn lookup(&self, local: Local) -> Ty {
        self.types[&self.find(local)].clone()
    }

    fn set(&mut self, local: Local, ty: Ty) {
        self.types.insert(self.find(local), ty);
    }
}

impl TyS {
    pub fn intern(self) -> Ty {
        Interned::new(self)
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
        write!(f, "[")?;
        for (root, group) in self
            .parent
            .indices()
            .into_group_map_by(|local| self.find(*local))
            .into_iter()
            .sorted()
        {
            if group.len() == 1 {
                write!(f, "{:?}: ", group[0])?;
            } else {
                write!(f, "{{{:?}}}: ", group.iter().sorted().format(", "),)?;
            }
            match self.types.get(&root) {
                Some(ty) => {
                    write!(f, "{:?}, ", ty)?;
                }
                None => {
                    write!(f, "unknown, ")?;
                }
            }
        }
        write!(f, "]")
    }
}

impl fmt::Debug for TyS {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Refine(e) => write!(f, "refine({:?})", e),
            Self::Uninit => write!(f, "uninit"),
            Self::MutRef(region) => write!(f, "ref<mut, {:?}>", region),
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

struct BasicBlockEnv {
    types: FxHashMap<Local, Ty>,
    parent: IndexVec<Local, Cell<Local>>,
    rank: IndexVec<Local, usize>,
}

impl BasicBlockEnv {
    fn from_env(env: &TypeEnv) -> BasicBlockEnv {
        BasicBlockEnv {
            types: env.types.clone(),
            parent: env.parent.clone(),
            rank: env.rank.clone(),
        }
    }

    fn join_with(&mut self, env: &TypeEnv) {
        debug_assert!(self.parent.len() == env.parent.len());

        for local in self.parent.indices() {
            let p = env.find(local);
            if p == local {
                let ty1 = env.lookup(local);
                let ty2 = self.lookup(local);
                self.set(local, ty1.join(&ty2));
            } else {
                self.union(local, p);
            }
        }
        let mut sources = BitSet::new_filled(self.parent.len());
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

        for source in sources.iter() {
            if self.find(source) != source {
                continue;
            }
            self.propagate(source);
        }
    }

    fn propagate(&mut self, root: Local) {
        let ty = self.types[&root].clone();
        match &*ty {
            TyS::MutRef(region) => {
                let first = region[0];
                for local in region.iter() {
                    self.union(first, local);
                }
                self.propagate(self.find(first));
            }
            _ => {}
        }
    }

    fn union(&mut self, local1: Local, local2: Local) {
        let root1 = self.find(local1);
        let root2 = self.find(local2);
        if root1 == root2 {
            return;
        }

        let root = match Ord::cmp(&self.rank[root1], &self.rank[root2]) {
            Ordering::Less => {
                self.parent[root1].set(root2);
                root2
            }
            Ordering::Equal => {
                *self.parent[root1].get_mut() = root2;
                self.rank[root2] += 1;
                root2
            }
            Ordering::Greater => {
                self.parent[root2].set(root1);
                root1
            }
        };
        let ty1 = self.types.remove(&root1).unwrap();
        let ty2 = self.types.remove(&root2).unwrap();
        self.types.insert(root, ty1.join(&ty2));
    }

    fn lookup(&self, local: Local) -> Ty {
        self.types[&self.find(local)].clone()
    }

    fn set(&mut self, local: Local, ty: Ty) {
        self.types.insert(self.find(local), ty);
    }

    fn find(&self, local: Local) -> Local {
        let parent = self.parent[local].get();
        if parent != local {
            self.parent[local].set(self.find(parent));
        }
        self.parent[local].get()
    }
}

impl fmt::Debug for BasicBlockEnv {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        for (root, group) in self
            .parent
            .indices()
            .into_group_map_by(|local| self.find(*local))
            .into_iter()
            .sorted()
        {
            if group.len() == 1 {
                write!(f, "{:?}: ", group[0])?;
            } else {
                write!(f, "{{{:?}}}: ", group.iter().sorted().format(", "),)?;
            }
            match self.types.get(&root) {
                Some(ty) => {
                    write!(f, "{:?}, ", ty)?;
                }
                None => {
                    write!(f, "unknown, ")?;
                }
            }
        }
        write!(f, "]")
    }
}
