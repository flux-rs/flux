//! Storage liveness of locals, as ghost statements.
//!
//! The analysis is rustc's [`MaybeStorageDead`]. Its state is the set of locals that are
//! *storage-dead*, i.e., locals rustc has not given storage yet or has already taken it away.
//! Locals without storage annotations are live for the whole body; the rest start dead,
//! `StorageLive` takes a local out of the set, `StorageDead` puts it back, and blocks join by
//! union, so a local dead on *any* path into a block is dead at its entry.
//!
//! Each transition becomes a ghost statement. [`Init`](GhostStatement::Init) is where a local
//! enters scope: the checker gives it an uninitialized binding. [`Kill`](GhostStatement::Kill) is
//! where it leaves: the checker *removes* the binding instead of setting it to uninit, because a
//! storage-dead local has no location to speak of. Emitting on transitions, and only on
//! transitions, is what makes the domain of the checker's environment equal the set of live locals
//! at every program point.
//!
//! The union join means a local can die with no `StorageDead` to hang its kill on, so such kills go
//! on the cfg edge instead:
//!
//! ```text
//! bb1: {
//!     init(_3); StorageLive(_3);      // _3 enters scope here ...
//!     _3 = &mut _2;
//!     goto -> bb3;
//!     -> bb3 { kill(_3); }            // ... and leaves it on this edge
//! }
//!
//! bb2: { goto -> bb3; }               // _3 never lived on this path,
//!
//! bb3: { ... }                        // so it has no binding here, either way
//! ```
use flux_middle::queries::QueryResult;
use rustc_index::{IndexSlice, bit_set::DenseBitSet};
use rustc_middle::{
    mir::{self, BasicBlock, Local, traversal},
    ty::TyCtxt,
};
use rustc_mir_dataflow::{
    Analysis, ResultsVisitor,
    impls::{MaybeStorageDead, always_storage_live_locals},
    visit_results,
};

use super::GhostStatements;
use crate::ghost_statements::{GhostStatement, Point};

pub(crate) fn add_ghost_statements<'tcx>(
    stmts: &mut GhostStatements,
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
) -> QueryResult {
    let always_live_locals = always_storage_live_locals(body);
    let results = MaybeStorageDead::new(std::borrow::Cow::Owned(always_live_locals))
        .iterate_to_fixpoint(tcx, body, None);
    let mut visitor = CollectStorageEvents {
        stmts,
        entry_states: &results.entry_states,
        before: DenseBitSet::new_empty(body.local_decls.len()),
    };
    for (bb, _) in traversal::reachable(body) {
        visitor.before.clone_from(&results.entry_states[bb]);
        visit_results(body, [bb], &results, &mut visitor);
    }

    Ok(())
}

struct CollectStorageEvents<'a> {
    stmts: &'a mut GhostStatements,
    entry_states: &'a IndexSlice<BasicBlock, DenseBitSet<Local>>,
    /// The state before the effect of the statement being visited.
    before: DenseBitSet<Local>,
}

/// The successors the dataflow framework propagates along, which are the only ones whose entry
/// state means anything: a block the fixpoint never reaches keeps its `bottom_value`, and for
/// [`MaybeStorageDead`] bottom is the *empty* set, so it reads as "every local is live" instead of
/// as "no information".
///
/// [`mir::Terminator::successors`] is the wrong source because it includes one edge the framework
/// leaves out: the `drop:` edge of a `Drop`, taken when a coroutine is dropped part-way through
/// (rustc calls this the *dropline*). [`mir::TerminatorEdges`] omits it, with a FIXME about needing
/// a variant that carries target, unwind *and* dropline, so nothing propagates to `bb2` in an
/// `async fn` body like
///
/// ```text
/// bb0: { ... drop(_1) -> [return: bb1, unwind: bb3, drop: bb2]; }
/// bb2: { coroutine_drop; }
/// ```
///
/// and its entry state would claim a local is live right after the predecessor killed it. Skipping
/// the edge loses nothing: the bridge's `Drop` keeps only `place`, `target` and `unwind`, so the
/// checker never walks a `drop:` edge and a ghost statement placed on one would never run.
fn dataflow_successors<'tcx>(terminator: &mir::Terminator<'tcx>) -> Vec<BasicBlock> {
    use mir::TerminatorEdges;
    match terminator.edges() {
        TerminatorEdges::None => vec![],
        TerminatorEdges::Single(bb) => vec![bb],
        TerminatorEdges::Double(bb1, bb2) => vec![bb1, bb2],
        TerminatorEdges::AssignOnReturn { return_, cleanup, .. } => {
            return_.iter().copied().chain(cleanup).collect()
        }
        TerminatorEdges::SwitchInt { targets, .. } => targets.all_targets().to_vec(),
    }
}

/// Locals in `new` but not in `old`.
fn difference<'a>(
    new: &'a DenseBitSet<Local>,
    old: &'a DenseBitSet<Local>,
) -> impl Iterator<Item = Local> + 'a {
    new.iter().filter(|local| !old.contains(*local))
}

impl<'tcx> ResultsVisitor<'tcx, MaybeStorageDead<'_>> for CollectStorageEvents<'_> {
    fn visit_after_primary_statement_effect(
        &mut self,
        state: &DenseBitSet<Local>,
        _statement: &mir::Statement<'tcx>,
        location: mir::Location,
    ) {
        let point = Point::BeforeLocation(location);
        // The state is the set of *dead* locals, so a local entering the set is dying and a local
        // leaving it is coming into scope.
        for local in difference(state, &self.before) {
            self.stmts.insert_at(point, GhostStatement::Kill(local));
        }
        for local in difference(&self.before, state) {
            self.stmts.insert_at(point, GhostStatement::Init(local));
        }
        self.before.clone_from(state);
    }

    fn visit_after_primary_terminator_effect(
        &mut self,
        state: &DenseBitSet<Local>,
        terminator: &mir::Terminator<'tcx>,
        location: mir::Location,
    ) {
        let block = location.block;
        for target in dataflow_successors(terminator) {
            let target_state = &self.entry_states[target];
            // The join is a union, so a local live at the entry of `target` is live at the end of
            // every predecessor and there's never an `Init` to emit on an edge.
            debug_assert!(target_state.superset(state));
            let point = Point::Edge(block, target);
            for local in difference(target_state, state) {
                self.stmts.insert_at(point, GhostStatement::Kill(local));
            }
        }
    }
}
