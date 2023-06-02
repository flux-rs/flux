use std::{collections::hash_map::Entry, fmt, iter};

use flux_common::tracked_span_bug;
use flux_middle::{
    global_env::GlobalEnv,
    intern::List,
    pretty::{self, def_id_to_string},
    queries::QueryResult,
    rustc::{
        mir::{
            BasicBlock, Body, FieldIdx, Local, Location, Operand, Place, PlaceElem, Rvalue,
            Statement, StatementKind, Terminator, TerminatorKind, VariantIdx, FIRST_VARIANT,
        },
        ty::{Substs, Ty, TyKind},
    },
};
use itertools::Itertools;
use rustc_data_structures::graph::dominators::Dominators;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_index::{Idx, IndexVec};
use rustc_middle::mir::START_BLOCK;
use rustc_span::Symbol;

use crate::queue::WorkQueue;

#[derive(Clone)]
pub(crate) struct Env {
    map: IndexVec<Local, PlaceNode>,
}

pub(crate) struct PlaceAnalysis<'a, 'tcx, M> {
    genv: &'a GlobalEnv<'a, 'tcx>,
    body: &'a Body<'tcx>,
    bb_envs: &'a mut FxHashMap<BasicBlock, Env>,
    queue: WorkQueue<'a>,
    location: Location,
    mode: M,
}

pub(crate) trait Mode: Sized {
    fn projection(analysis: &mut PlaceAnalysis<Self>, env: &mut Env, place: &Place) -> QueryResult;

    fn goto_join_point(
        analysis: &mut PlaceAnalysis<Self>,
        target: BasicBlock,
        env: Env,
    ) -> QueryResult<bool>;
}

struct Infer;

struct Elaboration<'a> {
    data: &'a mut FoldUnfolds,
}

#[derive(Debug, Default)]
struct FoldUnfolds {
    folds_at: FxHashMap<Location, Place>,
    unfolds_at: FxHashMap<Location, Place>,
}

struct FoldUnfoldsAt<'a> {
    data: &'a mut FoldUnfolds,
    location: Location,
}

enum FoldUnfold {
    None,
    Fold,
    Unfold,
}

impl Mode for Infer {
    fn projection(analysis: &mut PlaceAnalysis<Self>, env: &mut Env, place: &Place) -> QueryResult {
        env.projection(analysis.genv, place)?;
        Ok(())
    }

    fn goto_join_point(
        analysis: &mut PlaceAnalysis<Self>,
        target: BasicBlock,
        env: Env,
    ) -> QueryResult<bool> {
        let modified = match analysis.bb_envs.entry(target) {
            Entry::Occupied(mut entry) => entry.get_mut().join(analysis.genv, env)?,
            Entry::Vacant(entry) => {
                entry.insert(env);
                true
            }
        };
        Ok(modified)
    }
}

impl Mode for Elaboration<'_> {
    fn projection(analysis: &mut PlaceAnalysis<Self>, env: &mut Env, place: &Place) -> QueryResult {
        match env.projection(analysis.genv, place)? {
            FoldUnfold::None => {}
            FoldUnfold::Fold => {
                analysis
                    .mode
                    .data
                    .insert_fold(analysis.location, place.clone());
            }
            FoldUnfold::Unfold => {
                analysis
                    .mode
                    .data
                    .insert_unfold(analysis.location, place.clone());
            }
        }
        Ok(())
    }

    fn goto_join_point(
        analysis: &mut PlaceAnalysis<Self>,
        target: BasicBlock,
        env: Env,
    ) -> QueryResult<bool> {
        let mut fold_unfolds =
            FoldUnfoldsAt { location: analysis.location, data: analysis.mode.data };
        env.check(&analysis.bb_envs[&target], &mut fold_unfolds);
        Ok(false)
    }
}

#[derive(Clone)]
enum PlaceNode {
    Deref(Ty, Box<PlaceNode>),
    Downcast(DefId, Substs, Option<Symbol>, VariantIdx, Vec<PlaceNode>),
    Closure(DefId, Substs, Vec<PlaceNode>),
    Tuple(List<Ty>, Vec<PlaceNode>),
    Ty(Ty),
}

impl<'a, 'tcx, M> PlaceAnalysis<'a, 'tcx, M> {
    pub(crate) fn new(
        genv: &'a GlobalEnv<'a, 'tcx>,
        body: &'a Body<'tcx>,
        dominators: &'a Dominators<BasicBlock>,
        bb_envs: &'a mut FxHashMap<BasicBlock, Env>,
        mode: M,
    ) -> Self {
        Self {
            genv,
            body,
            bb_envs,
            location: Location::START,
            queue: WorkQueue::empty(body.basic_blocks.len(), dominators),
            mode,
        }
    }
}

impl<'a, 'tcx> PlaceAnalysis<'a, 'tcx, ()> {
    pub(crate) fn run(
        genv: &'a GlobalEnv<'a, 'tcx>,
        body: &'a Body<'tcx>,
        dominators: &'a Dominators<BasicBlock>,
    ) -> QueryResult {
        let mut bb_envs = FxHashMap::default();
        PlaceAnalysis::new(genv, body, dominators, &mut bb_envs, Infer).run()?;

        let mut fold_unfolds = FoldUnfolds::default();
        PlaceAnalysis::new(
            genv,
            body,
            dominators,
            &mut bb_envs,
            Elaboration { data: &mut fold_unfolds },
        )
        .run()?;

        println!("{fold_unfolds:#?}");

        Ok(())
    }
}

impl<'a, 'tcx, M: Mode> PlaceAnalysis<'a, 'tcx, M> {
    fn run(mut self) -> QueryResult {
        self.goto(START_BLOCK, Env::new(self.body))?;
        while let Some(bb) = self.queue.pop() {
            let mut env = self.bb_envs[&bb].clone();
            self.basic_block(bb, &mut env)?;
        }
        Ok(())
    }

    fn basic_block(&mut self, bb: BasicBlock, env: &mut Env) -> QueryResult {
        let data = &self.body.basic_blocks[bb];
        for (statement_index, stmt) in data.statements.iter().enumerate() {
            self.location = Location { block: bb, statement_index };
            self.statement(stmt, env)?;
        }
        if let Some(terminator) = &data.terminator {
            self.location = Location { block: bb, statement_index: data.statements.len() };
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
                M::projection(self, env, place)?;
            }
            StatementKind::SetDiscriminant(_, _)
            | StatementKind::FakeRead(_)
            | StatementKind::AscribeUserType(_, _)
            | StatementKind::PlaceMention(_)
            | StatementKind::Nop => {}
        }
        Ok(())
    }

    fn rvalue(&mut self, rvalue: &Rvalue, env: &mut Env) -> QueryResult {
        match rvalue {
            Rvalue::Use(op) | Rvalue::Cast(_, op, _) | Rvalue::UnaryOp(_, op) => {
                self.operand(op, env)?;
            }
            Rvalue::Ref(.., place) => {
                M::projection(self, env, place)?;
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
                M::projection(self, env, place)?;
            }
        }
        Ok(())
    }

    fn operand(&mut self, op: &Operand, env: &mut Env) -> QueryResult {
        match op {
            Operand::Copy(place) | Operand::Move(place) => {
                M::projection(self, env, place)?;
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
                M::projection(self, env, Place::RETURN)?;
            }
            TerminatorKind::Call { args, destination, target, .. } => {
                for arg in args {
                    self.operand(arg, env)?;
                }
                M::projection(self, env, destination)?;
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
                M::projection(self, env, place)?;
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
            if M::goto_join_point(self, target, env)? {
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

    fn projection(&mut self, genv: &GlobalEnv, place: &Place) -> QueryResult<FoldUnfold> {
        let mut node = &mut self.map[place.local];
        let mut unfolded = false;
        for elem in &place.projection {
            match *elem {
                PlaceElem::Deref => (node, unfolded) = node.deref(genv),
                PlaceElem::Field(f) => (node, unfolded) = node.field(genv, f)?,
                PlaceElem::Downcast(name, idx) => unfolded = node.downcast(genv, name, idx)?,
                PlaceElem::Index(_) => todo!(),
            }
        }
        if unfolded {
            Ok(FoldUnfold::Unfold)
        } else if node.fold() {
            Ok(FoldUnfold::Fold)
        } else {
            Ok(FoldUnfold::None)
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

    fn check(&self, other: &Env, fold_unfolds: &mut FoldUnfoldsAt) {
        for (local, node) in self.map.iter_enumerated() {
            node.collect_fold_unfolds(
                &other.map[local],
                &mut Place::new(local, vec![]),
                fold_unfolds,
            );
        }
    }
}

impl PlaceNode {
    fn deref(&mut self, genv: &GlobalEnv) -> (&mut PlaceNode, bool) {
        match self {
            PlaceNode::Deref(_, node) => (node, false),
            PlaceNode::Ty(ty) => {
                *self = PlaceNode::Deref(ty.clone(), Box::new(PlaceNode::Ty(ty.deref(genv))));
                let PlaceNode::Deref(_, node) = self else { unreachable!() };
                (node, true)
            }
            _ => tracked_span_bug!("deref of non-deref place: `{:?}`", self),
        }
    }

    fn downcast(
        &mut self,
        genv: &GlobalEnv,
        name: Option<Symbol>,
        idx: VariantIdx,
    ) -> QueryResult<bool> {
        match self {
            PlaceNode::Downcast(.., idx2, _) => {
                debug_assert_eq!(idx, *idx2);
                Ok(false)
            }
            PlaceNode::Ty(ty) => {
                if let TyKind::Adt(def_id, substs) = ty.kind() {
                    let fields = downcast(genv, *def_id, substs, idx)?;
                    *self = PlaceNode::Downcast(*def_id, substs.clone(), name, idx, fields);
                    Ok(true)
                } else {
                    tracked_span_bug!("invalid downcast `{self:?}`");
                }
            }
            _ => tracked_span_bug!("invalid downcast `{self:?}`"),
        }
    }

    fn field(&mut self, genv: &GlobalEnv, f: FieldIdx) -> QueryResult<(&mut PlaceNode, bool)> {
        let (fields, unfolded) = self.fields(genv)?;
        Ok((&mut fields[f.as_usize()], unfolded))
    }

    fn fields(&mut self, genv: &GlobalEnv) -> QueryResult<(&mut Vec<PlaceNode>, bool)> {
        match self {
            PlaceNode::Ty(ty) => {
                let fields = match ty.kind() {
                    TyKind::Adt(def_id, substs) => {
                        let fields = downcast_struct(genv, *def_id, substs)?;
                        *self = PlaceNode::Downcast(
                            *def_id,
                            substs.clone(),
                            None,
                            FIRST_VARIANT,
                            fields,
                        );
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
                        let node_fields = fields.iter().cloned().map(PlaceNode::Ty).collect();
                        *self = PlaceNode::Tuple(fields.clone(), node_fields);
                        let PlaceNode::Tuple(.., fields) = self else { unreachable!() };
                        fields
                    }
                    _ => tracked_span_bug!("implicit downcast of non-struct: `{ty:?}`"),
                };
                Ok((fields, true))
            }
            PlaceNode::Downcast(.., fields)
            | PlaceNode::Tuple(.., fields)
            | PlaceNode::Closure(.., fields) => Ok((fields, false)),
            PlaceNode::Deref(..) => {
                tracked_span_bug!("projection field of non-adt non-tuple place: `{self:?}`")
            }
        }
    }

    fn fold(&mut self) -> bool {
        match self {
            PlaceNode::Deref(ty, _) => {
                *self = PlaceNode::Ty(ty.clone());
                true
            }
            PlaceNode::Downcast(did, substs, ..) => {
                *self = PlaceNode::Ty(Ty::mk_adt(*did, substs.clone()));
                true
            }
            PlaceNode::Closure(did, substs, _) => {
                *self = PlaceNode::Ty(Ty::mk_closure(*did, substs.clone()));
                true
            }
            PlaceNode::Tuple(fields, ..) => {
                *self = PlaceNode::Ty(Ty::mk_tuple(fields.clone()));
                true
            }
            PlaceNode::Ty(_) => false,
        }
    }

    fn collect_fold_unfolds(
        &self,
        other: &PlaceNode,
        place: &mut Place,
        fold_unfolds: &mut FoldUnfoldsAt,
    ) {
        let (fields1, fields2) = match (self, other) {
            (PlaceNode::Deref(_, node1), PlaceNode::Deref(_, node2)) => {
                place.projection.push(PlaceElem::Deref);
                node1.collect_fold_unfolds(node2, place, fold_unfolds);
                place.projection.pop();
                return;
            }
            (PlaceNode::Tuple(_, fields1), PlaceNode::Tuple(_, fields2)) => (fields1, fields2),
            (PlaceNode::Closure(.., fields1), PlaceNode::Closure(.., fields2)) => {
                (fields1, fields2)
            }
            (
                PlaceNode::Downcast(did1, .., idx1, fields1),
                PlaceNode::Downcast(did2, .., idx2, fields2),
            ) => {
                debug_assert_eq!(did1, did2);
                if idx1 == idx2 {
                    (fields1, fields2)
                } else {
                    tracked_span_bug!();
                }
            }
            (PlaceNode::Ty(_), PlaceNode::Ty(_)) => return,
            (PlaceNode::Ty(_), _) => {
                other.collect_unfolds(place, fold_unfolds);
                return;
            }
            (_, PlaceNode::Ty(_)) => {
                fold_unfolds.insert_fold(place.clone());
                return;
            }
            _ => tracked_span_bug!("{self:?} {other:?}"),
        };
        for (i, (node1, node2)) in iter::zip(fields1, fields2).enumerate() {
            place.projection.push(PlaceElem::Field(FieldIdx::new(i)));
            node1.collect_fold_unfolds(node2, place, fold_unfolds);
            place.projection.pop();
        }
    }

    fn collect_unfolds(&self, place: &mut Place, fold_unfolds: &mut FoldUnfoldsAt) -> bool {
        let fields = match self {
            PlaceNode::Ty(_) => {
                return true;
            }
            PlaceNode::Deref(_, node) => {
                place.projection.push(PlaceElem::Deref);
                node.collect_unfolds(place, fold_unfolds);
                place.projection.pop();
                return false;
            }
            PlaceNode::Downcast(_, _, name, idx, fields) => {
                place.projection.push(PlaceElem::Downcast(*name, *idx));
                fields
            }
            PlaceNode::Closure(_, _, fields) => fields,
            PlaceNode::Tuple(_, fields) => fields,
        };
        let mut all_leafs = true;
        for (i, node) in fields.iter().enumerate() {
            place.projection.push(PlaceElem::Field(FieldIdx::new(i)));
            all_leafs &= node.collect_unfolds(place, fold_unfolds);
            place.projection.pop();
        }
        if all_leafs {
            fold_unfolds.insert_unfold(place.clone());
        }
        if let PlaceNode::Downcast(..) = self {
            place.projection.pop();
        }

        true
    }

    fn join(&mut self, genv: &GlobalEnv, other: &mut PlaceNode) -> QueryResult<(bool, bool)> {
        let mut modified1 = false;
        let mut modified2 = false;

        let (fields1, fields2) = match (&mut *self, &mut *other) {
            (PlaceNode::Deref(_, node1), PlaceNode::Deref(_, node2)) => {
                return node1.join(genv, node2);
            }
            (PlaceNode::Tuple(_, fields1), PlaceNode::Tuple(_, fields2)) => (fields1, fields2),
            (PlaceNode::Closure(.., fields1), PlaceNode::Closure(.., fields2)) => {
                (fields1, fields2)
            }
            (
                PlaceNode::Downcast(did1, substs1, _, idx1, fields1),
                PlaceNode::Downcast(did2, substs2, _, idx2, fields2),
            ) => {
                debug_assert_eq!(did1, did2);
                if idx1 == idx2 {
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
            (PlaceNode::Deref(_, node1), _) => {
                let (other, m) = other.deref(genv);
                let (m1, m2) = node1.join(genv, other)?;
                return Ok((m1, m2 | m));
            }
            (PlaceNode::Tuple(_, fields1), _) => {
                let (fields2, m) = other.fields(genv)?;
                modified2 |= m;
                (fields1, fields2)
            }
            (PlaceNode::Closure(.., fields1), _) => {
                let (fields2, m) = other.fields(genv)?;
                modified2 |= m;
                (fields1, fields2)
            }
            (PlaceNode::Downcast(did, substs, .., fields1), _) => {
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

impl FoldUnfolds {
    fn insert_fold(&mut self, location: Location, place: Place) {
        self.folds_at.insert(location, place);
    }

    fn insert_unfold(&mut self, location: Location, place: Place) {
        self.unfolds_at.insert(location, place);
    }
}

impl FoldUnfoldsAt<'_> {
    fn insert_fold(&mut self, place: Place) {
        self.data.insert_fold(self.location, place);
    }

    fn insert_unfold(&mut self, place: Place) {
        self.data.insert_unfold(self.location, place);
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
            PlaceNode::Deref(_, node) => write!(f, "*({:?})", node),
            PlaceNode::Downcast(did, substs, _, idx, fields) => {
                write!(f, "{}", def_id_to_string(*did))?;
                if !substs.is_empty() {
                    write!(f, "<{:?}>", substs.iter().format(", "),)?;
                }
                write!(f, "::{}", pretty::variant_name(*did, *idx))?;
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
            PlaceNode::Tuple(_, fields) => write!(f, "({:?})", fields.iter().format(", ")),
            PlaceNode::Ty(ty) => write!(f, "•{ty:?}"),
        }
    }
}
