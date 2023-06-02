use std::{collections::hash_map::Entry, fmt, iter};

use flux_common::tracked_span_bug;
use flux_middle::{
    global_env::GlobalEnv,
    intern::List,
    pretty::def_id_to_string,
    queries::QueryResult,
    rustc::{
        mir::{
            BasicBlock, Body, FieldIdx, Local, Location, Operand, Place, PlaceElem, Rvalue,
            Statement, StatementKind, Terminator, TerminatorKind, VariantIdx, FIRST_VARIANT,
        },
        ty::{AdtDef, Substs, Ty, TyKind},
    },
};
use itertools::Itertools;
use rustc_data_structures::graph::dominators::Dominators;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_index::{Idx, IndexVec};
use rustc_middle::mir::START_BLOCK;

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
    discriminants: FxHashMap<Place, Place>,
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
                let place = place.clone();
                analysis.mode.data.insert_fold(analysis.location, place);
            }
            FoldUnfold::Unfold => {
                let projection = place.projection[..place.projection.len() - 1].to_vec();
                let place = Place::new(place.local, projection);
                analysis.mode.data.insert_unfold(analysis.location, place);
            }
        }
        Ok(())
    }

    fn goto_join_point(
        analysis: &mut PlaceAnalysis<Self>,
        target: BasicBlock,
        env: Env,
    ) -> QueryResult<bool> {
        // Insert fold and unfolds after the terminator.
        let location = analysis.location.successor_within_block();
        let mut fold_unfolds = FoldUnfoldsAt { location, data: analysis.mode.data };
        env.collect_fold_unfolds(&analysis.bb_envs[&target], &mut fold_unfolds);
        Ok(false)
    }
}

#[derive(Clone)]
enum PlaceNode {
    Deref(Ty, Box<PlaceNode>),
    Downcast(AdtDef, Substs, VariantIdx, Vec<PlaceNode>),
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
            discriminants: FxHashMap::default(),
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

        Ok(())
    }
}

impl<'a, 'tcx, M: Mode> PlaceAnalysis<'a, 'tcx, M> {
    fn run(mut self) -> QueryResult {
        self.goto(START_BLOCK, Env::new(self.body))?;
        while let Some(bb) = self.queue.pop() {
            self.basic_block(bb, self.bb_envs[&bb].clone())?;
        }
        Ok(())
    }

    fn basic_block(&mut self, bb: BasicBlock, mut env: Env) -> QueryResult {
        let data = &self.body.basic_blocks[bb];
        for (statement_index, stmt) in data.statements.iter().enumerate() {
            self.location = Location { block: bb, statement_index };
            self.statement(stmt, &mut env)?;
        }
        if let Some(terminator) = &data.terminator {
            self.location = Location { block: bb, statement_index: data.statements.len() };
            self.terminator(terminator, env)?;
        }
        Ok(())
    }

    fn statement(&mut self, stmt: &Statement, env: &mut Env) -> QueryResult {
        match &stmt.kind {
            StatementKind::Assign(place, rvalue) => {
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
                    Rvalue::Len(place) => {
                        M::projection(self, env, place)?;
                    }
                    Rvalue::Discriminant(discr) => {
                        M::projection(self, env, discr)?;
                        self.discriminants.insert(place.clone(), discr.clone());
                    }
                }
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

    fn operand(&mut self, op: &Operand, env: &mut Env) -> QueryResult {
        match op {
            Operand::Copy(place) | Operand::Move(place) => {
                M::projection(self, env, place)?;
            }
            Operand::Constant(_) => {}
        }
        Ok(())
    }

    fn terminator(&mut self, terminator: &Terminator, mut env: Env) -> QueryResult {
        match &terminator.kind {
            TerminatorKind::Return => {
                M::projection(self, &mut env, Place::RETURN)?;
            }
            TerminatorKind::Call { args, destination, target, .. } => {
                for arg in args {
                    self.operand(arg, &mut env)?;
                }
                M::projection(self, &mut env, destination)?;
                if let Some(target) = target {
                    self.goto(*target, env)?;
                }
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                let is_match = match discr {
                    Operand::Copy(place) | Operand::Move(place) => {
                        M::projection(self, &mut env, place)?;
                        self.discriminants.remove(place)
                    }
                    Operand::Constant(_) => None,
                };
                if let Some(mut place) = is_match {
                    for (bits, target) in targets.iter() {
                        // We do not insert unfolds in match arms because they are explicit
                        // unfold points, but we still need to project the place to mutate
                        // env.
                        let mut env = env.clone();
                        let idx = VariantIdx::new(bits as usize);
                        place.projection.push(PlaceElem::Downcast(None, idx));
                        env.projection(self.genv, &place)?;
                        place.projection.pop();

                        self.goto(target, env)?;
                    }
                    self.goto(targets.otherwise(), env)?;
                } else {
                    for target in targets.all_targets() {
                        self.goto(*target, env.clone())?;
                    }
                }
            }
            TerminatorKind::Goto { target } => {
                self.goto(*target, env)?;
            }
            TerminatorKind::Drop { place, target, .. } => {
                M::projection(self, &mut env, place)?;
                self.goto(*target, env)?;
            }
            TerminatorKind::Assert { cond, target, .. } => {
                self.operand(cond, &mut env)?;
                self.goto(*target, env)?;
            }
            TerminatorKind::FalseEdge { real_target, .. } => {
                self.goto(*real_target, env)?;
            }
            TerminatorKind::FalseUnwind { real_target, .. } => {
                self.goto(*real_target, env)?;
            }
            TerminatorKind::Unreachable | TerminatorKind::Resume => {}
        }
        Ok(())
    }

    fn goto(&mut self, target: BasicBlock, env: Env) -> QueryResult {
        if self.body.is_join_point(target) {
            if M::goto_join_point(self, target, env)? {
                self.queue.insert(target);
            }
            Ok(())
        } else {
            self.basic_block(target, env)
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
                PlaceElem::Deref => (node, unfolded) = node.deref(),
                PlaceElem::Field(f) => (node, unfolded) = node.field(genv, f)?,
                PlaceElem::Downcast(_, idx) => unfolded = node.downcast(genv, idx)?,
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

    fn collect_fold_unfolds(&self, other: &Env, fold_unfolds: &mut FoldUnfoldsAt) {
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
    fn deref(&mut self) -> (&mut PlaceNode, bool) {
        match self {
            PlaceNode::Deref(_, node) => (node, false),
            PlaceNode::Ty(ty) => {
                *self = PlaceNode::Deref(ty.clone(), Box::new(PlaceNode::Ty(ty.deref())));
                let PlaceNode::Deref(_, node) = self else { unreachable!() };
                (node, true)
            }
            _ => tracked_span_bug!("deref of non-deref place: `{:?}`", self),
        }
    }

    fn downcast(&mut self, genv: &GlobalEnv, idx: VariantIdx) -> QueryResult<bool> {
        match self {
            PlaceNode::Downcast(.., idx2, _) => {
                debug_assert_eq!(idx, *idx2);
                Ok(false)
            }
            PlaceNode::Ty(ty) => {
                if let TyKind::Adt(adt_def, substs) = ty.kind() {
                    let fields = downcast(genv, adt_def, substs, idx)?;
                    *self = PlaceNode::Downcast(adt_def.clone(), substs.clone(), idx, fields);
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
                    TyKind::Adt(adt_def, substs) => {
                        let fields = downcast_struct(genv, adt_def, substs)?;
                        *self = PlaceNode::Downcast(
                            adt_def.clone(),
                            substs.clone(),
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
            PlaceNode::Downcast(adt, substs, ..) => {
                *self = PlaceNode::Ty(Ty::mk_adt(adt.clone(), substs.clone()));
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
                PlaceNode::Downcast(adt1, .., idx1, fields1),
                PlaceNode::Downcast(adt2, .., idx2, fields2),
            ) => {
                debug_assert_eq!(adt1.did(), adt2.did());
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
            PlaceNode::Downcast(adt, _, idx, fields) => {
                if adt.is_enum() {
                    place.projection.push(PlaceElem::Downcast(None, *idx));
                }
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
        if let PlaceNode::Downcast(adt, ..) = self && adt.is_enum() {
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
                PlaceNode::Downcast(adt1, substs1, variant1, fields1),
                PlaceNode::Downcast(adt2, substs2, variant2, fields2),
            ) => {
                debug_assert_eq!(adt1, adt2);
                if variant1 == variant2 {
                    (fields1, fields2)
                } else {
                    *self = PlaceNode::Ty(Ty::mk_adt(adt1.clone(), substs1.clone()));
                    *other = PlaceNode::Ty(Ty::mk_adt(adt2.clone(), substs2.clone()));
                    return Ok((true, true));
                }
            }
            (PlaceNode::Ty(_), PlaceNode::Ty(_)) => return Ok((false, false)),
            (PlaceNode::Ty(_), _) => {
                let (m1, m2) = other.join(genv, self)?;
                return Ok((m2, m1));
            }
            (PlaceNode::Deref(_, node1), _) => {
                let (other, m) = other.deref();
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
            (PlaceNode::Downcast(adt, substs, .., fields1), _) => {
                if adt.is_struct() {
                    let (fields2, m) = other.fields(genv)?;
                    modified2 |= m;
                    (fields1, fields2)
                } else {
                    *self = PlaceNode::Ty(Ty::mk_adt(adt.clone(), substs.clone()));
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
    adt_def: &AdtDef,
    substs: &Substs,
    variant: VariantIdx,
) -> QueryResult<Vec<PlaceNode>> {
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
    adt_def: &AdtDef,
    substs: &Substs,
) -> QueryResult<Vec<PlaceNode>> {
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
            PlaceNode::Downcast(adt, substs, variant, fields) => {
                write!(f, "{}", def_id_to_string(adt.did()))?;
                if !substs.is_empty() {
                    write!(f, "<{:?}>", substs.iter().format(", "),)?;
                }
                write!(f, "::{}", adt.variant(*variant).name)?;
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