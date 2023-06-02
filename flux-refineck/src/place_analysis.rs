use std::{collections::hash_map::Entry, fmt, iter};

use flux_common::tracked_span_bug;
use flux_middle::{
    global_env::GlobalEnv,
    pretty::{self, def_id_to_string},
    queries::QueryResult,
    rustc::{
        mir::{
            BasicBlock, Body, FieldIdx, Local, Operand, Place, PlaceElem, Rvalue, Statement,
            StatementKind, Terminator, TerminatorKind, VariantIdx, FIRST_VARIANT,
        },
        ty::{Substs, Ty, TyKind},
    },
};
use itertools::Itertools;
use rustc_data_structures::graph::dominators::Dominators;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_index::IndexVec;
use rustc_middle::mir::START_BLOCK;

use crate::queue::WorkQueue;

#[derive(Clone)]
struct Env {
    map: IndexVec<Local, PlaceNode>,
}

pub(crate) struct PlaceAnalysis<'a, 'tcx> {
    genv: &'a GlobalEnv<'a, 'tcx>,
    body: &'a Body<'tcx>,
    bb_envs: FxHashMap<BasicBlock, Env>,
    queue: WorkQueue<'a>,
}

#[derive(Clone)]
enum PlaceNode {
    Deref(Box<PlaceNode>),
    Downcast(DefId, Substs, VariantIdx, Vec<PlaceNode>),
    Closure(DefId, Substs, Vec<PlaceNode>),
    Tuple(Vec<PlaceNode>),
    Ty(Ty),
}

impl<'a, 'tcx> PlaceAnalysis<'a, 'tcx> {
    pub(crate) fn new(
        genv: &'a GlobalEnv<'a, 'tcx>,
        body: &'a Body<'tcx>,
        dominators: &'a Dominators<BasicBlock>,
    ) -> Self {
        Self {
            genv,
            body,
            bb_envs: FxHashMap::default(),
            queue: WorkQueue::empty(body.basic_blocks.len(), dominators),
        }
    }

    pub(crate) fn run(mut self) -> QueryResult {
        self.basic_block(START_BLOCK, &mut Env::new(self.body))?;
        while let Some(bb) = self.queue.pop() {
            let mut env = self.bb_envs[&bb].clone();
            self.basic_block(bb, &mut env)?;
        }
        Ok(())
    }

    fn basic_block(&mut self, bb: BasicBlock, env: &mut Env) -> QueryResult {
        let data = &self.body.basic_blocks[bb];
        for stmt in &data.statements {
            self.statement(stmt, env)?;
        }
        if let Some(terminator) = &data.terminator {
            let successors = self.terminator(terminator, env)?;
            for successor in successors {
                let env = env.clone();
                self.goto(successor, env)?;
            }
        }
        Ok(())
    }

    fn statement(&mut self, stmt: &Statement, env: &mut Env) -> QueryResult {
        match &stmt.kind {
            StatementKind::Assign(place, rvalue) => {
                self.rvalue(rvalue, env)?;
                env.unfold(self.genv, place)?;
            }
            StatementKind::SetDiscriminant(_, _)
            | StatementKind::FakeRead(_)
            | StatementKind::AscribeUserType(_, _)
            | StatementKind::PlaceMention(_)
            | StatementKind::Nop => {}
        }
        Ok(())
    }

    fn rvalue(&self, rvalue: &Rvalue, env: &mut Env) -> QueryResult {
        match rvalue {
            Rvalue::Use(op) | Rvalue::Cast(_, op, _) | Rvalue::UnaryOp(_, op) => {
                self.operand(op, env)?;
            }
            Rvalue::Ref(.., place) => {
                env.fold(self.genv, place)?;
            }
            Rvalue::CheckedBinaryOp(_, op1, op2) | Rvalue::BinaryOp(_, op1, op2) => {
                self.operand(op1, env)?;
                self.operand(op2, env)?;
            }
            Rvalue::Aggregate(_, args) => {
                for arg in args {
                    self.operand(arg, env)?;
                }
            }
            Rvalue::Len(place) | Rvalue::Discriminant(place) => {
                env.fold(self.genv, place)?;
            }
        }
        Ok(())
    }

    fn operand(&self, op: &Operand, env: &mut Env) -> QueryResult {
        match op {
            Operand::Copy(place) | Operand::Move(place) => {
                env.fold(self.genv, place)?;
            }
            Operand::Constant(_) => {}
        }
        Ok(())
    }

    fn terminator(
        &mut self,
        terminator: &Terminator,
        env: &mut Env,
    ) -> QueryResult<Vec<BasicBlock>> {
        let mut successors = vec![];
        match &terminator.kind {
            TerminatorKind::Return => {
                env.fold(self.genv, Place::RETURN)?;
            }
            TerminatorKind::Call { args, destination, target, .. } => {
                for arg in args {
                    self.operand(arg, env)?;
                }
                env.fold(self.genv, destination)?;
                if let Some(target) = target {
                    successors.push(*target);
                }
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                self.operand(discr, env)?;
                successors.extend(targets.all_targets());
            }
            TerminatorKind::Goto { target } => {
                successors.push(*target);
            }
            TerminatorKind::Drop { place, target, .. } => {
                env.fold(self.genv, place)?;
                successors.push(*target);
            }
            TerminatorKind::Assert { cond, target, .. } => {
                self.operand(cond, env)?;
                successors.push(*target);
            }
            TerminatorKind::FalseEdge { real_target, .. } => {
                successors.push(*real_target);
            }
            TerminatorKind::FalseUnwind { real_target, .. } => {
                successors.push(*real_target);
            }
            TerminatorKind::Unreachable | TerminatorKind::Resume => {}
        };
        Ok(successors)
    }

    fn goto(&mut self, target: BasicBlock, mut env: Env) -> QueryResult {
        if self.body.is_join_point(target) {
            let modified = match self.bb_envs.entry(target) {
                Entry::Occupied(mut entry) => entry.get_mut().join(self.genv, env)?,
                Entry::Vacant(entry) => {
                    entry.insert(env);
                    true
                }
            };
            if modified {
                self.queue.insert(target);
            }
            Ok(())
        } else {
            self.basic_block(target, &mut env)
        }
    }
}

impl Env {
    fn new(body: &Body) -> Self {
        Self {
            map: body
                .local_decls
                .iter()
                .map(|decl| PlaceNode::Ty(decl.ty.clone()))
                .collect(),
        }
    }

    fn join(&mut self, genv: &GlobalEnv, mut other: Env) -> QueryResult<bool> {
        let mut modified = false;
        for (local, node) in self.map.iter_enumerated_mut() {
            let (m, _) = node.join(genv, &mut other.map[local])?;
            modified |= m;
        }
        Ok(modified)
    }

    fn fold(&mut self, genv: &GlobalEnv, place: &Place) -> QueryResult {
        self.lookup(genv, place)?;
        Ok(())
    }

    fn unfold(&mut self, genv: &GlobalEnv, place: &Place) -> QueryResult {
        self.lookup(genv, place)?;
        Ok(())
    }

    fn lookup(&mut self, genv: &GlobalEnv, place: &Place) -> QueryResult<&mut PlaceNode> {
        let mut node = &mut self.map[place.local];
        for elem in &place.projection {
            match *elem {
                PlaceElem::Deref => node = node.deref(genv),
                PlaceElem::Field(f) => node = node.field(genv, f)?,
                PlaceElem::Downcast(variant) => node.downcast(genv, variant)?,
                PlaceElem::Index(_) => todo!(),
            }
        }
        Ok(node)
    }
}

impl PlaceNode {
    fn deref(&mut self, genv: &GlobalEnv) -> &mut PlaceNode {
        match self {
            PlaceNode::Deref(node) => node,
            PlaceNode::Ty(ty) => {
                *self = PlaceNode::Deref(Box::new(PlaceNode::Ty(ty.deref(genv))));
                let PlaceNode::Deref(node) = self else { unreachable!() };
                node
            }
            _ => tracked_span_bug!("deref of non-deref place: `{:?}`", self),
        }
    }

    fn downcast(&mut self, genv: &GlobalEnv, variant: VariantIdx) -> QueryResult {
        match self {
            PlaceNode::Downcast(_, _, variant2, _) => {
                debug_assert_eq!(variant, *variant2);
            }
            PlaceNode::Ty(ty) => {
                if let TyKind::Adt(def_id, substs) = ty.kind() {
                    let fields = downcast(genv, *def_id, substs, variant)?;
                    *self = PlaceNode::Downcast(*def_id, substs.clone(), variant, fields);
                } else {
                    tracked_span_bug!("invalid downcast `{self:?}`");
                }
            }
            _ => tracked_span_bug!("invalid downcast `{self:?}`"),
        }
        Ok(())
    }

    fn field(&mut self, genv: &GlobalEnv, f: FieldIdx) -> QueryResult<&mut PlaceNode> {
        Ok(&mut self.fields(genv)?.0[f.as_usize()])
    }

    fn fields(&mut self, genv: &GlobalEnv) -> QueryResult<(&mut Vec<PlaceNode>, bool)> {
        match self {
            PlaceNode::Ty(ty) => {
                let fields = match ty.kind() {
                    TyKind::Adt(def_id, substs) => {
                        let fields = downcast_struct(genv, *def_id, substs)?;
                        *self = PlaceNode::Downcast(*def_id, substs.clone(), FIRST_VARIANT, fields);
                        let PlaceNode::Downcast(.., fields) = self else { unreachable!() };
                        fields
                    }
                    TyKind::Closure(def_id, substs) => {
                        let fields = substs
                            .as_closure()
                            .upvar_tys()
                            .cloned()
                            .map(PlaceNode::Ty)
                            .collect_vec();
                        *self = PlaceNode::Closure(*def_id, substs.clone(), fields);
                        let PlaceNode::Closure(.., fields) = self else { unreachable!() };
                        fields
                    }
                    TyKind::Tuple(fields) => {
                        let fields = fields.iter().cloned().map(PlaceNode::Ty).collect();
                        *self = PlaceNode::Tuple(fields);
                        let PlaceNode::Tuple(fields) = self else { unreachable!() };
                        fields
                    }
                    _ => tracked_span_bug!("implicit downcast of non-struct: `{ty:?}`"),
                };
                Ok((fields, true))
            }
            PlaceNode::Downcast(.., fields)
            | PlaceNode::Tuple(fields)
            | PlaceNode::Closure(.., fields) => Ok((fields, false)),
            PlaceNode::Deref(_) => {
                tracked_span_bug!("projection field of non-adt non-tuple place: `{self:?}`")
            }
        }
    }

    fn join(&mut self, genv: &GlobalEnv, other: &mut PlaceNode) -> QueryResult<(bool, bool)> {
        let mut modified1 = false;
        let mut modified2 = false;

        let (fields1, fields2) = match (&mut *self, &mut *other) {
            (PlaceNode::Deref(node1), PlaceNode::Deref(node2)) => {
                return node1.join(genv, node2);
            }
            (PlaceNode::Tuple(fields1), PlaceNode::Tuple(fields2)) => (fields1, fields2),
            (PlaceNode::Closure(.., fields1), PlaceNode::Closure(.., fields2)) => {
                (fields1, fields2)
            }
            (
                PlaceNode::Downcast(did1, substs1, variant1, fields1),
                PlaceNode::Downcast(did2, substs2, variant2, fields2),
            ) => {
                debug_assert_eq!(did1, did2);
                if variant1 == variant2 {
                    (fields1, fields2)
                } else {
                    *self = PlaceNode::Ty(Ty::mk_adt(*did1, substs1.clone()));
                    *other = PlaceNode::Ty(Ty::mk_adt(*did2, substs2.clone()));
                    return Ok((true, true));
                }
            }
            (PlaceNode::Ty(_), PlaceNode::Ty(_)) => return Ok((false, false)),
            (PlaceNode::Ty(_), _) => {
                let (m1, m2) = other.join(genv, self)?;
                return Ok((m2, m1));
            }
            (PlaceNode::Deref(node1), _) => {
                return node1.join(genv, other.deref(genv));
            }
            (PlaceNode::Tuple(fields1), _) => {
                let (fields2, m) = other.fields(genv)?;
                modified2 |= m;
                (fields1, fields2)
            }
            (PlaceNode::Closure(.., fields1), _) => {
                let (fields2, m) = other.fields(genv)?;
                modified2 |= m;
                (fields1, fields2)
            }
            (PlaceNode::Downcast(did, substs, _, fields1), _) => {
                if genv.tcx.adt_def(*did).is_struct() {
                    let (fields2, m) = other.fields(genv)?;
                    modified2 |= m;
                    (fields1, fields2)
                } else {
                    *self = PlaceNode::Ty(Ty::mk_adt(*did, substs.clone()));
                    return Ok((true, false));
                }
            }
        };
        for (node1, node2) in iter::zip(fields1, fields2) {
            let (m1, m2) = node1.join(genv, node2)?;
            modified1 |= m1;
            modified2 |= m2;
        }
        Ok((modified1, modified2))
    }
}

fn downcast(
    genv: &GlobalEnv,
    def_id: DefId,
    substs: &Substs,
    variant: VariantIdx,
) -> QueryResult<Vec<PlaceNode>> {
    let adt_def = genv.tcx.adt_def(def_id);
    adt_def
        .variant(variant)
        .fields
        .iter()
        .map(|field| {
            let ty = genv.lower_type_of(field.did)?.subst(substs);
            QueryResult::Ok(PlaceNode::Ty(ty))
        })
        .try_collect()
}

fn downcast_struct(
    genv: &GlobalEnv,
    def_id: DefId,
    substs: &Substs,
) -> QueryResult<Vec<PlaceNode>> {
    let adt_def = genv.tcx.adt_def(def_id);
    adt_def
        .non_enum_variant()
        .fields
        .iter()
        .map(|field| {
            let ty = genv.lower_type_of(field.did)?.subst(substs);
            QueryResult::Ok(PlaceNode::Ty(ty))
        })
        .try_collect()
}

impl fmt::Debug for Env {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            self.map
                .iter_enumerated()
                .format_with(", ", |(local, node), f| f(&format_args!("{local:?}: {node:?}")))
        )
    }
}

impl fmt::Debug for PlaceNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PlaceNode::Deref(node) => write!(f, "*({:?})", node),
            PlaceNode::Downcast(did, substs, variant_idx, fields) => {
                write!(f, "{}", def_id_to_string(*did))?;
                if !substs.is_empty() {
                    write!(f, "<{:?}>", substs.iter().format(", "),)?;
                }
                write!(f, "::{}", pretty::variant_name(*did, *variant_idx))?;
                if !fields.is_empty() {
                    write!(f, "({:?})", fields.iter().format(", "),)?;
                }
                Ok(())
            }
            PlaceNode::Closure(did, substs, fields) => {
                write!(f, "{}", def_id_to_string(*did))?;
                if !substs.is_empty() {
                    write!(f, "<{:?}>", substs.iter().format(", "),)?;
                }
                if !fields.is_empty() {
                    write!(f, "({:?})", fields.iter().format(", "),)?;
                }
                Ok(())
            }
            PlaceNode::Tuple(tys) => write!(f, "({:?})", tys.iter().format(", ")),
            PlaceNode::Ty(ty) => write!(f, "•{ty:?}"),
        }
    }
}
