use std::{collections::hash_map::Entry, fmt, iter};

use flux_common::{tracked_span_assert_eq, tracked_span_bug, tracked_span_dbg_assert_eq};
use flux_middle::{
    PlaceExt as _, def_id_to_string, global_env::GlobalEnv, queries::QueryResult, query_bug, rty,
};
use flux_rustc_bridge::{
    mir::{
        BasicBlock, Body, BorrowKind, FIRST_VARIANT, FieldIdx, Local, Location,
        NonDivergingIntrinsic, Operand, Place, PlaceElem, PlaceRef, Rvalue, Statement,
        StatementKind, Terminator, TerminatorKind, UnOp, VariantIdx,
    },
    ty::{AdtDef, GenericArgs, GenericArgsExt as _, List, Mutability, Ty, TyKind},
};
use itertools::{Itertools, repeat_n};
use rustc_data_structures::unord::UnordMap;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_index::{Idx, IndexVec, bit_set::DenseBitSet};
use rustc_middle::mir::START_BLOCK;

use super::{GhostStatements, StatementsAt};
use crate::{
    ghost_statements::{GhostStatement, Point},
    queue::WorkQueue,
};

pub(crate) fn add_ghost_statements<'tcx>(
    stmts: &mut GhostStatements,
    genv: GlobalEnv<'_, 'tcx>,
    body: &Body<'tcx>,
    fn_sig: Option<&rty::EarlyBinder<rty::PolyFnSig>>,
) -> QueryResult {
    let mut bb_envs = FxHashMap::default();
    FoldUnfoldAnalysis::new(genv, body, &mut bb_envs, Infer).run(fn_sig)?;

    FoldUnfoldAnalysis::new(genv, body, &mut bb_envs, Elaboration { stmts }).run(fn_sig)
}

#[derive(Clone)]
struct Env {
    map: IndexVec<Local, PlaceNode>,
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

    fn projection<'a>(&mut self, genv: GlobalEnv, place: &'a Place) -> QueryResult<ProjResult<'a>> {
        let (node, place, modified) = self.ensure_unfolded(genv, place)?;
        if modified {
            Ok(ProjResult::Unfold(place))
        } else if node.ensure_folded() {
            Ok(ProjResult::Fold(place))
        } else {
            Ok(ProjResult::None)
        }
    }

    fn downcast(&mut self, genv: GlobalEnv, place: &Place, variant_idx: VariantIdx) -> QueryResult {
        let (node, ..) = self.ensure_unfolded(genv, place)?;
        node.downcast(genv, variant_idx)?;
        Ok(())
    }

    fn ensure_unfolded<'a>(
        &mut self,
        genv: GlobalEnv,
        place: &'a Place,
    ) -> QueryResult<(&mut PlaceNode, PlaceRef<'a>, Modified)> {
        let mut node = &mut self.map[place.local];
        let mut modified = false;
        let mut i = 0;
        while i < place.projection.len() {
            let elem = place.projection[i];
            let (n, m) = match elem {
                PlaceElem::Deref => node.deref(),
                PlaceElem::Field(f) => node.field(genv, f)?,
                PlaceElem::Downcast(_, idx) => node.downcast(genv, idx)?,
                PlaceElem::Index(_) | PlaceElem::ConstantIndex { .. } => break,
            };
            node = n;
            modified |= m;
            i += 1;
        }
        Ok((node, place.as_ref().truncate(i), modified))
    }

    fn join(&mut self, genv: GlobalEnv, mut other: Env) -> QueryResult<Modified> {
        let mut modified = false;
        for (local, node) in self.map.iter_enumerated_mut() {
            let (m, _) = node.join(genv, &mut other.map[local], false)?;
            modified |= m;
        }
        Ok(modified)
    }

    fn collect_fold_unfolds_at_goto(&self, target: &Env, stmts: &mut StatementsAt) {
        for (local, node) in self.map.iter_enumerated() {
            node.collect_fold_unfolds(&target.map[local], &mut Place::new(local, vec![]), stmts);
        }
    }

    fn collect_folds_at_ret(&self, body: &Body, stmts: &mut StatementsAt) {
        for local in body.args_iter() {
            self.map[local].collect_folds_at_ret(&mut Place::new(local, vec![]), stmts);
        }
    }
}

type Modified = bool;

struct FoldUnfoldAnalysis<'a, 'genv, 'tcx, M> {
    genv: GlobalEnv<'genv, 'tcx>,
    body: &'a Body<'tcx>,
    bb_envs: &'a mut FxHashMap<BasicBlock, Env>,
    visited: DenseBitSet<BasicBlock>,
    queue: WorkQueue<'a>,
    discriminants: UnordMap<Place, Place>,
    point: Point,
    mode: M,
}

trait Mode: Sized {
    const NAME: &'static str;

    fn projection(
        analysis: &mut FoldUnfoldAnalysis<Self>,
        env: &mut Env,
        place: &Place,
    ) -> QueryResult;

    fn goto_join_point(
        analysis: &mut FoldUnfoldAnalysis<Self>,
        target: BasicBlock,
        env: Env,
    ) -> QueryResult<bool>;

    fn ret(analysis: &mut FoldUnfoldAnalysis<Self>, env: &Env);
}

struct Infer;

struct Elaboration<'a> {
    stmts: &'a mut GhostStatements,
}

impl Elaboration<'_> {
    fn insert_at(&mut self, point: Point, stmt: GhostStatement) {
        self.stmts.insert_at(point, stmt);
    }
}

#[derive(Debug)]
enum ProjResult<'a> {
    None,
    Fold(PlaceRef<'a>),
    Unfold(PlaceRef<'a>),
}

impl Mode for Infer {
    const NAME: &'static str = "infer";

    fn projection(
        analysis: &mut FoldUnfoldAnalysis<Self>,
        env: &mut Env,
        place: &Place,
    ) -> QueryResult {
        env.projection(analysis.genv, place)?;
        Ok(())
    }

    fn goto_join_point(
        analysis: &mut FoldUnfoldAnalysis<Self>,
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

    fn ret(_: &mut FoldUnfoldAnalysis<Self>, _: &Env) {}
}

impl Mode for Elaboration<'_> {
    const NAME: &'static str = "elaboration";

    fn projection(
        analysis: &mut FoldUnfoldAnalysis<Self>,
        env: &mut Env,
        place: &Place,
    ) -> QueryResult {
        match env.projection(analysis.genv, place)? {
            ProjResult::None => {}
            ProjResult::Fold(place_ref) => {
                tracked_span_assert_eq!(place_ref, place.as_ref());
                let place = place.clone();
                analysis
                    .mode
                    .insert_at(analysis.point, GhostStatement::Fold(place));
            }
            ProjResult::Unfold(place_ref) => {
                tracked_span_assert_eq!(place_ref, place.as_ref());
                match place_ref.last_projection() {
                    Some((base, PlaceElem::Deref | PlaceElem::Field(..))) => {
                        analysis
                            .mode
                            .insert_at(analysis.point, GhostStatement::Unfold(base.to_place()));
                    }
                    _ => Err(query_bug!("invalid projection for unfolding {place_ref:?}"))?,
                }
            }
        }
        Ok(())
    }

    fn goto_join_point(
        analysis: &mut FoldUnfoldAnalysis<Self>,
        target: BasicBlock,
        env: Env,
    ) -> QueryResult<bool> {
        env.collect_fold_unfolds_at_goto(
            &analysis.bb_envs[&target],
            &mut analysis.mode.stmts.at(analysis.point),
        );
        Ok(!analysis.visited.contains(target))
    }

    fn ret(analysis: &mut FoldUnfoldAnalysis<Self>, env: &Env) {
        env.collect_folds_at_ret(analysis.body, &mut analysis.mode.stmts.at(analysis.point));
    }
}

#[derive(Clone)]
enum PlaceNode {
    Deref(Ty, Box<PlaceNode>),
    Downcast(AdtDef, GenericArgs, VariantIdx, Vec<PlaceNode>),
    Closure(DefId, GenericArgs, Vec<PlaceNode>),
    Generator(DefId, GenericArgs, Vec<PlaceNode>),
    Tuple(List<Ty>, Vec<PlaceNode>),
    Ty(Ty),
}

impl<M: Mode> FoldUnfoldAnalysis<'_, '_, '_, M> {
    fn run(mut self, fn_sig: Option<&rty::EarlyBinder<rty::PolyFnSig>>) -> QueryResult {
        let mut env = Env::new(self.body);

        if let Some(fn_sig) = fn_sig {
            let fn_sig = fn_sig.as_ref().skip_binder().as_ref().skip_binder();
            for (local, ty) in iter::zip(self.body.args_iter(), fn_sig.inputs()) {
                if let rty::TyKind::StrgRef(..) | rty::Ref!(.., Mutability::Mut) = ty.kind() {
                    M::projection(&mut self, &mut env, &Place::new(local, vec![PlaceElem::Deref]))?;
                }
            }
        }
        self.goto(START_BLOCK, env)?;
        while let Some(bb) = self.queue.pop() {
            self.basic_block(bb, self.bb_envs[&bb].clone())?;
        }
        Ok(())
    }

    fn basic_block(&mut self, bb: BasicBlock, mut env: Env) -> QueryResult {
        self.visited.insert(bb);
        let data = &self.body.basic_blocks[bb];
        for (statement_index, stmt) in data.statements.iter().enumerate() {
            self.point = Point::BeforeLocation(Location { block: bb, statement_index });
            self.statement(stmt, &mut env)?;
        }
        if let Some(terminator) = &data.terminator {
            self.point = Point::BeforeLocation(self.body.terminator_loc(bb));
            let successors = self.terminator(terminator, env)?;
            for (env, target) in successors {
                self.point = Point::Edge(bb, target);
                self.goto(target, env)?;
            }
        }
        Ok(())
    }

    fn statement(&mut self, stmt: &Statement, env: &mut Env) -> QueryResult {
        match &stmt.kind {
            StatementKind::Assign(place, rvalue) => {
                match rvalue {
                    Rvalue::Len(place) => {
                        M::projection(self, env, place)?;
                    }
                    Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Copy(place))
                    | Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Move(place)) => {
                        let deref_place = place.deref();
                        M::projection(self, env, &deref_place)?
                    }

                    Rvalue::Use(op)
                    | Rvalue::Cast(_, op, _)
                    | Rvalue::UnaryOp(_, op)
                    | Rvalue::ShallowInitBox(op, _) => {
                        self.operand(op, env)?;
                    }
                    Rvalue::Ref(.., bk, place) => {
                        // Fake borrows should not cause the place to fold
                        if !matches!(bk, BorrowKind::Fake(_)) {
                            M::projection(self, env, place)?;
                        }
                    }
                    Rvalue::RawPtr(_, place) => {
                        M::projection(self, env, place)?;
                    }
                    Rvalue::BinaryOp(_, op1, op2) => {
                        self.operand(op1, env)?;
                        self.operand(op2, env)?;
                    }
                    Rvalue::Aggregate(_, args) => {
                        for arg in args {
                            self.operand(arg, env)?;
                        }
                    }

                    Rvalue::Discriminant(discr) => {
                        M::projection(self, env, discr)?;
                        self.discriminants.insert(place.clone(), discr.clone());
                    }
                    Rvalue::Repeat(op, _) => {
                        self.operand(op, env)?;
                    }
                    Rvalue::NullaryOp(_, _) => {}
                }
                M::projection(self, env, place)?;
            }
            StatementKind::Intrinsic(NonDivergingIntrinsic::Assume(op)) => {
                self.operand(op, env)?;
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

    fn terminator(
        &mut self,
        terminator: &Terminator,
        mut env: Env,
    ) -> QueryResult<Vec<(Env, BasicBlock)>> {
        let mut successors = vec![];
        match &terminator.kind {
            TerminatorKind::Return => {
                M::ret(self, &env);
            }
            TerminatorKind::Call { args, destination, target, .. } => {
                for arg in args {
                    self.operand(arg, &mut env)?;
                }
                M::projection(self, &mut env, destination)?;
                if let Some(target) = target {
                    successors.push((env, *target));
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
                if let Some(place) = is_match {
                    let discr_ty = place.ty(self.genv, &self.body.local_decls)?.ty;
                    let (adt, _) = discr_ty.expect_adt();

                    let mut remaining: FxHashMap<u128, VariantIdx> = adt
                        .discriminants()
                        .map(|(idx, discr)| (discr, idx))
                        .collect();
                    for (bits, target) in targets.iter() {
                        let variant_idx = remaining
                            .remove(&bits)
                            .expect("value doesn't correspond to any variant");

                        // We do not insert unfolds in match arms because they are explicit
                        // unfold points.
                        let mut env = env.clone();
                        env.downcast(self.genv, &place, variant_idx)?;
                        successors.push((env, target));
                    }
                    if remaining.len() == 1 {
                        let (_, variant_idx) = remaining
                            .into_iter()
                            .next()
                            .unwrap_or_else(|| tracked_span_bug!());
                        env.downcast(self.genv, &place, variant_idx)?;
                    }
                    successors.push((env, targets.otherwise()));
                } else {
                    let n = targets.all_targets().len();
                    for (env, target) in iter::zip(repeat_n(env, n), targets.all_targets()) {
                        successors.push((env, *target));
                    }
                }
            }
            TerminatorKind::Goto { target } => {
                successors.push((env, *target));
            }
            TerminatorKind::Yield { resume, resume_arg, .. } => {
                M::projection(self, &mut env, resume_arg)?;
                successors.push((env, *resume));
            }
            TerminatorKind::Drop { place, target, .. } => {
                M::projection(self, &mut env, place)?;
                successors.push((env, *target));
            }
            TerminatorKind::Assert { cond, target, .. } => {
                self.operand(cond, &mut env)?;
                successors.push((env, *target));
            }
            TerminatorKind::FalseEdge { real_target, .. } => {
                successors.push((env, *real_target));
            }
            TerminatorKind::FalseUnwind { real_target, .. } => {
                successors.push((env, *real_target));
            }
            TerminatorKind::Unreachable
            | TerminatorKind::UnwindResume
            | TerminatorKind::CoroutineDrop => {}
        }
        Ok(successors)
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

impl<'a, 'genv, 'tcx, M> FoldUnfoldAnalysis<'a, 'genv, 'tcx, M> {
    pub(crate) fn new(
        genv: GlobalEnv<'genv, 'tcx>,
        body: &'a Body<'tcx>,
        bb_envs: &'a mut FxHashMap<BasicBlock, Env>,
        mode: M,
    ) -> Self {
        Self {
            genv,
            body,
            bb_envs,
            discriminants: Default::default(),
            point: Point::FunEntry,
            visited: DenseBitSet::new_empty(body.basic_blocks.len()),
            queue: WorkQueue::empty(body.basic_blocks.len(), &body.dominator_order_rank),
            mode,
        }
    }
}

impl PlaceNode {
    fn deref(&mut self) -> (&mut PlaceNode, Modified) {
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

    fn downcast(
        &mut self,
        genv: GlobalEnv,
        idx: VariantIdx,
    ) -> QueryResult<(&mut PlaceNode, Modified)> {
        match self {
            PlaceNode::Downcast(.., idx2, _) => {
                debug_assert_eq!(idx, *idx2);
                Ok((self, false))
            }
            PlaceNode::Ty(ty) => {
                if let TyKind::Adt(adt_def, args) = ty.kind() {
                    let fields = downcast(genv, adt_def, args, idx)?;
                    *self = PlaceNode::Downcast(adt_def.clone(), args.clone(), idx, fields);
                    Ok((self, true))
                } else {
                    tracked_span_bug!("invalid downcast `{self:?}`");
                }
            }
            _ => tracked_span_bug!("invalid downcast `{self:?}`"),
        }
    }

    fn field(&mut self, genv: GlobalEnv, f: FieldIdx) -> QueryResult<(&mut PlaceNode, Modified)> {
        let (fields, unfolded) = self.fields(genv)?;
        Ok((&mut fields[f.as_usize()], unfolded))
    }

    fn fields(&mut self, genv: GlobalEnv) -> QueryResult<(&mut Vec<PlaceNode>, bool)> {
        match self {
            PlaceNode::Ty(ty) => {
                let fields = match ty.kind() {
                    TyKind::Adt(adt_def, args) => {
                        let fields = downcast_struct(genv, adt_def, args)?;
                        *self = PlaceNode::Downcast(
                            adt_def.clone(),
                            args.clone(),
                            FIRST_VARIANT,
                            fields,
                        );
                        let PlaceNode::Downcast(.., fields) = self else { unreachable!() };
                        fields
                    }
                    TyKind::Closure(def_id, args) => {
                        let fields = args
                            .as_closure()
                            .upvar_tys()
                            .iter()
                            .cloned()
                            .map(PlaceNode::Ty)
                            .collect_vec();
                        *self = PlaceNode::Closure(*def_id, args.clone(), fields);
                        let PlaceNode::Closure(.., fields) = self else { unreachable!() };
                        fields
                    }
                    TyKind::Tuple(fields) => {
                        let node_fields = fields.iter().cloned().map(PlaceNode::Ty).collect();
                        *self = PlaceNode::Tuple(fields.clone(), node_fields);
                        let PlaceNode::Tuple(.., fields) = self else { unreachable!() };
                        fields
                    }
                    TyKind::Coroutine(def_id, args) => {
                        let fields = args
                            .as_coroutine()
                            .upvar_tys()
                            .cloned()
                            .map(PlaceNode::Ty)
                            .collect_vec();
                        *self = PlaceNode::Generator(*def_id, args.clone(), fields);
                        let PlaceNode::Generator(.., fields) = self else { unreachable!() };
                        fields
                    }
                    _ => tracked_span_bug!("implicit downcast of non-struct: `{ty:?}`"),
                };
                Ok((fields, true))
            }
            PlaceNode::Downcast(.., fields)
            | PlaceNode::Tuple(.., fields)
            | PlaceNode::Closure(.., fields)
            | PlaceNode::Generator(.., fields) => Ok((fields, false)),
            PlaceNode::Deref(..) => {
                tracked_span_bug!("projection field of non-adt non-tuple place: `{self:?}`")
            }
        }
    }

    fn ensure_folded(&mut self) -> Modified {
        match self {
            PlaceNode::Deref(ty, _) => {
                *self = PlaceNode::Ty(ty.clone());
                true
            }
            PlaceNode::Downcast(adt, args, ..) => {
                *self = PlaceNode::Ty(Ty::mk_adt(adt.clone(), args.clone()));
                true
            }
            PlaceNode::Closure(did, args, _) => {
                *self = PlaceNode::Ty(Ty::mk_closure(*did, args.clone()));
                true
            }
            PlaceNode::Generator(did, args, _) => {
                *self = PlaceNode::Ty(Ty::mk_coroutine(*did, args.clone()));
                true
            }
            PlaceNode::Tuple(fields, ..) => {
                *self = PlaceNode::Ty(Ty::mk_tuple(fields.clone()));
                true
            }
            PlaceNode::Ty(_) => false,
        }
    }

    fn join(
        &mut self,
        genv: GlobalEnv,
        other: &mut PlaceNode,
        in_mut_ref: bool,
    ) -> QueryResult<(bool, bool)> {
        let mut modified1 = false;
        let mut modified2 = false;

        let (fields1, fields2) = match (&mut *self, &mut *other) {
            (PlaceNode::Deref(ty1, node1), PlaceNode::Deref(ty2, node2)) => {
                debug_assert_eq!(ty1, ty2);
                return node1.join(genv, node2, in_mut_ref || ty1.is_mut_ref());
            }
            (PlaceNode::Tuple(_, fields1), PlaceNode::Tuple(_, fields2)) => (fields1, fields2),
            (PlaceNode::Closure(.., fields1), PlaceNode::Closure(.., fields2)) => {
                (fields1, fields2)
            }
            (PlaceNode::Generator(.., fields1), PlaceNode::Generator(.., fields2)) => {
                (fields1, fields2)
            }
            (
                PlaceNode::Downcast(adt1, args1, variant1, fields1),
                PlaceNode::Downcast(adt2, args2, variant2, fields2),
            ) => {
                debug_assert_eq!(adt1, adt2);
                if variant1 == variant2 {
                    (fields1, fields2)
                } else {
                    *self = PlaceNode::Ty(Ty::mk_adt(adt1.clone(), args1.clone()));
                    *other = PlaceNode::Ty(Ty::mk_adt(adt2.clone(), args2.clone()));
                    return Ok((true, true));
                }
            }
            (PlaceNode::Ty(_), PlaceNode::Ty(_)) => return Ok((false, false)),
            (PlaceNode::Ty(_), _) => {
                let (m1, m2) = other.join(genv, self, in_mut_ref)?;
                return Ok((m2, m1));
            }
            (PlaceNode::Deref(ty, _), _) => {
                *self = PlaceNode::Ty(ty.clone());
                return Ok((true, false));
            }
            (PlaceNode::Tuple(_, fields1), _) => {
                let (fields2, m) = other.fields(genv)?;
                modified2 |= m;
                (fields1, fields2)
            }
            (PlaceNode::Closure(.., fields1), _) | (PlaceNode::Generator(.., fields1), _) => {
                let (fields2, m) = other.fields(genv)?;
                modified2 |= m;
                (fields1, fields2)
            }

            (PlaceNode::Downcast(adt, args, .., fields1), _) => {
                if adt.is_struct() && !in_mut_ref {
                    let (fields2, m) = other.fields(genv)?;
                    modified2 |= m;
                    (fields1, fields2)
                } else {
                    *self = PlaceNode::Ty(Ty::mk_adt(adt.clone(), args.clone()));
                    return Ok((true, false));
                }
            }
        };
        for (node1, node2) in iter::zip(fields1, fields2) {
            let (m1, m2) = node1.join(genv, node2, in_mut_ref)?;
            modified1 |= m1;
            modified2 |= m2;
        }
        Ok((modified1, modified2))
    }

    /// Collect necessary fold/unfold operations such that `self` is unfolded at the same level than `target`
    fn collect_fold_unfolds(
        &self,
        target: &PlaceNode,
        place: &mut Place,
        stmts: &mut StatementsAt,
    ) {
        let (fields1, fields2) = match (self, target) {
            (PlaceNode::Deref(_, node1), PlaceNode::Deref(_, node2)) => {
                place.projection.push(PlaceElem::Deref);
                node1.collect_fold_unfolds(node2, place, stmts);
                place.projection.pop();
                return;
            }
            (PlaceNode::Tuple(_, fields1), PlaceNode::Tuple(_, fields2)) => (fields1, fields2),
            (PlaceNode::Closure(.., fields1), PlaceNode::Closure(.., fields2))
            | (PlaceNode::Generator(.., fields1), PlaceNode::Generator(.., fields2)) => {
                (fields1, fields2)
            }
            (
                PlaceNode::Downcast(adt1, .., idx1, fields1),
                PlaceNode::Downcast(adt2, .., idx2, fields2),
            ) => {
                tracked_span_dbg_assert_eq!(adt1.did(), adt2.did());
                tracked_span_dbg_assert_eq!(idx1, idx2);
                (fields1, fields2)
            }
            (PlaceNode::Ty(_), PlaceNode::Ty(_)) => return,
            (PlaceNode::Ty(_), _) => {
                target.collect_unfolds(place, stmts);
                return;
            }
            (_, PlaceNode::Ty(_)) => {
                stmts.insert(GhostStatement::Fold(place.clone()));
                return;
            }
            _ => tracked_span_bug!("{self:?} {target:?}"),
        };
        for (i, (node1, node2)) in iter::zip(fields1, fields2).enumerate() {
            place.projection.push(PlaceElem::Field(FieldIdx::new(i)));
            node1.collect_fold_unfolds(node2, place, stmts);
            place.projection.pop();
        }
    }

    fn collect_unfolds(&self, place: &mut Place, stmts: &mut StatementsAt) {
        match self {
            PlaceNode::Ty(_) => {}
            PlaceNode::Deref(_, node) => {
                if node.is_ty() {
                    stmts.insert(GhostStatement::Unfold(place.clone()));
                } else {
                    place.projection.push(PlaceElem::Deref);
                    node.collect_unfolds(place, stmts);
                    place.projection.pop();
                }
            }
            PlaceNode::Downcast(.., fields)
            | PlaceNode::Closure(.., fields)
            | PlaceNode::Generator(.., fields)
            | PlaceNode::Tuple(.., fields) => {
                let all_leaves = fields.iter().all(PlaceNode::is_ty);
                if all_leaves {
                    stmts.insert(GhostStatement::Unfold(place.clone()));
                } else {
                    if let Some(idx) = self.enum_variant() {
                        place.projection.push(PlaceElem::Downcast(None, idx));
                    }
                    for (i, node) in fields.iter().enumerate() {
                        place.projection.push(PlaceElem::Field(FieldIdx::new(i)));
                        node.collect_unfolds(place, stmts);
                        place.projection.pop();
                    }
                    if self.enum_variant().is_some() {
                        place.projection.pop();
                    }
                }
            }
        }
    }

    fn collect_folds_at_ret(&self, place: &mut Place, stmts: &mut StatementsAt) {
        let fields = match self {
            PlaceNode::Deref(ty, deref_ty) => {
                place.projection.push(PlaceElem::Deref);
                if ty.is_mut_ref() {
                    stmts.insert(GhostStatement::Fold(place.clone()));
                } else if ty.is_box() {
                    deref_ty.collect_folds_at_ret(place, stmts);
                }
                place.projection.pop();
                return;
            }
            PlaceNode::Downcast(adt, _, idx, fields) => {
                if adt.is_enum() {
                    place.projection.push(PlaceElem::Downcast(None, *idx));
                }
                fields
            }
            PlaceNode::Closure(_, _, fields)
            | PlaceNode::Generator(_, _, fields)
            | PlaceNode::Tuple(_, fields) => fields,
            PlaceNode::Ty(_) => return,
        };
        for (i, node) in fields.iter().enumerate() {
            place.projection.push(PlaceElem::Field(FieldIdx::new(i)));
            node.collect_folds_at_ret(place, stmts);
            place.projection.pop();
        }
        if let PlaceNode::Downcast(adt, ..) = self
            && adt.is_enum()
        {
            place.projection.pop();
        }
    }

    fn enum_variant(&self) -> Option<VariantIdx> {
        if let PlaceNode::Downcast(adt, _, idx, _) = self
            && adt.is_enum()
        {
            Some(*idx)
        } else {
            None
        }
    }

    /// Returns `true` if the place node is [`Ty`].
    ///
    /// [`Ty`]: PlaceNode::Ty
    #[must_use]
    fn is_ty(&self) -> bool {
        matches!(self, Self::Ty(..))
    }
}

fn downcast(
    genv: GlobalEnv,
    adt_def: &AdtDef,
    args: &GenericArgs,
    variant: VariantIdx,
) -> QueryResult<Vec<PlaceNode>> {
    adt_def
        .variant(variant)
        .fields
        .iter()
        .map(|field| {
            let ty = genv.lower_type_of(field.did)?.subst(args);
            QueryResult::Ok(PlaceNode::Ty(ty))
        })
        .try_collect()
}

fn downcast_struct(
    genv: GlobalEnv,
    adt_def: &AdtDef,
    args: &GenericArgs,
) -> QueryResult<Vec<PlaceNode>> {
    adt_def
        .non_enum_variant()
        .fields
        .iter()
        .map(|field| {
            let ty = genv.lower_type_of(field.did)?.subst(args);
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
            PlaceNode::Deref(_, node) => write!(f, "*({node:?})"),
            PlaceNode::Downcast(adt, args, variant, fields) => {
                write!(f, "{}", def_id_to_string(adt.did()))?;
                if !args.is_empty() {
                    write!(f, "<{:?}>", args.iter().format(", "),)?;
                }
                write!(f, "::{}", adt.variant(*variant).name)?;
                if !fields.is_empty() {
                    write!(f, "({:?})", fields.iter().format(", "),)?;
                }
                Ok(())
            }
            PlaceNode::Closure(did, args, fields) => {
                write!(f, "Closure {}", def_id_to_string(*did))?;
                if !args.is_empty() {
                    write!(f, "<{:?}>", args.iter().format(", "),)?;
                }
                if !fields.is_empty() {
                    write!(f, "({:?})", fields.iter().format(", "),)?;
                }
                Ok(())
            }
            PlaceNode::Generator(did, args, fields) => {
                write!(f, "Generator {}", def_id_to_string(*did))?;
                if !args.is_empty() {
                    write!(f, "<{:?}>", args.iter().format(", "),)?;
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
