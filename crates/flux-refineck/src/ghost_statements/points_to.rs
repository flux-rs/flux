use std::{collections::VecDeque, fmt, iter, ops::Range};

use flux_middle::{
    global_env::GlobalEnv,
    rty::{self, Loc},
    rustc::mir::FieldIdx,
};
use rustc_data_structures::stack::ensure_sufficient_stack;
use rustc_hash::FxHashMap;
use rustc_index::{bit_set::BitSet, IndexSlice, IndexVec};
use rustc_middle::{
    mir::{self, visit::Visitor, TerminatorEdges},
    ty,
};
use rustc_mir_dataflow::{
    fmt::DebugWithContext,
    lattice::{FlatSet, HasBottom, HasTop},
    Analysis, JoinSemiLattice,
};

pub(crate) struct PointsToAnalysis<'a, 'tcx> {
    genv: &'a GlobalEnv<'a, 'tcx>,
    fn_sig: rty::EarlyBinder<rty::PolyFnSig>,
    map: &'a Map,
}

impl<'a, 'tcx> PointsToAnalysis<'a, 'tcx> {
    pub(crate) fn new(
        genv: &'a GlobalEnv<'a, 'tcx>,
        map: &'a Map,
        fn_sig: rty::EarlyBinder<rty::PolyFnSig>,
    ) -> Self {
        PointsToAnalysis { genv, fn_sig, map }
    }

    pub(crate) fn iterate_to_fixpoint(self, body: &mir::Body<'tcx>) {
        let map = self.map;
        let tcx = self.genv.tcx;
        let mut cursor = self
            .into_engine(tcx, body)
            .iterate_to_fixpoint()
            .into_results_cursor(body);

        for (bb, bb_data) in mir::traversal::reachable(body) {
            cursor.seek_to_block_end(bb);
            let state = cursor.get();

            println!("{bb:?}: {state:?}");
            for target in bb_data.terminator().successors() {
                let target_state = cursor.results().entry_set_for_block(target);
                map.for_each_tracked_place(|place_idx, local, projection| {
                    target_state.get_idx(place_idx, map);
                });
            }
            println!();
        }

        // result.visit_with(body, blocks, vis)
    }
}

impl<'a, 'tcx> PointsToAnalysis<'a, 'tcx> {
    fn handle_statement(&self, statement: &mir::Statement<'tcx>, state: &mut State) {
        match &statement.kind {
            mir::StatementKind::Assign(box (target, rvalue)) => {
                self.handle_assign(*target, rvalue, state);
            }
            mir::StatementKind::StorageLive(local) | mir::StatementKind::StorageDead(local) => {
                // StorageLive leaves the local in an uninitialized state.
                // StorageDead makes it UB to access the local afterwards.
                state.flood_with(mir::Place::from(*local).as_ref(), self.map, FlatSet::BOTTOM);
            }
            mir::StatementKind::Deinit(box place) => {
                // Deinit makes the place uninitialized.
                state.flood_with(place.as_ref(), self.map, FlatSet::BOTTOM);
            }
            mir::StatementKind::Retag(..) => {
                // We don't track references.
            }
            mir::StatementKind::Intrinsic(..)
            | mir::StatementKind::SetDiscriminant { .. }
            | mir::StatementKind::ConstEvalCounter
            | mir::StatementKind::Nop
            | mir::StatementKind::FakeRead(..)
            | mir::StatementKind::PlaceMention(..)
            | mir::StatementKind::Coverage(..)
            | mir::StatementKind::AscribeUserType(..) => (),
        }
    }

    fn handle_assign(
        &self,
        target: mir::Place<'tcx>,
        rvalue: &mir::Rvalue<'tcx>,
        state: &mut State,
    ) {
        match rvalue {
            mir::Rvalue::Use(operand) => {
                let result = self
                    .handle_operand(operand)
                    .map_or(PlaceOrValue::TOP, PlaceOrValue::Place);
                state.assign(target.as_ref(), result, self.map);
            }
            mir::Rvalue::Ref(_, _, place) => {
                let result = match &place.projection[..] {
                    [] => {
                        let loc = FlatSet::Elem(Loc::Local(place.local));
                        PlaceOrValue::Value(loc)
                    }
                    [mir::PlaceElem::Deref] => {
                        let loc = state.get(place.local.into(), self.map);
                        PlaceOrValue::Value(loc)
                    }
                    _ => PlaceOrValue::TOP,
                };
                state.assign(target.as_ref(), result, self.map);
            }
            mir::Rvalue::Aggregate(box mir::AggregateKind::Tuple, operands) => {
                state.flood(target.as_ref(), self.map);
                let Some(target_idx) = self.map.find(target.as_ref()) else { return };
                for (elem, operand) in operands.iter_enumerated() {
                    let Some(rhs_idx) = self.handle_operand(operand) else { continue };
                    if let Some(field) = self.map.apply(target_idx, elem) {
                        state.insert_place_idx(field, rhs_idx, self.map);
                    }
                }
            }
            _ => {}
        }
    }

    fn handle_operand(&self, operand: &mir::Operand<'tcx>) -> Option<PlaceIndex> {
        match operand {
            mir::Operand::Constant(..) => None,
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                // On move, we would ideally flood the place with bottom. But with the current
                // framework this is not possible (similar to `InterpCx::eval_operand`).
                self.map.find(place.as_ref())
            }
        }
    }

    /// The effect of a successful function call return should not be
    /// applied here, see [`Analysis::apply_terminator_effect`].
    fn handle_terminator<'mir>(
        &self,
        terminator: &'mir mir::Terminator<'tcx>,
        state: &mut State,
    ) -> TerminatorEdges<'mir, 'tcx> {
        match &terminator.kind {
            mir::TerminatorKind::Call { .. } | mir::TerminatorKind::InlineAsm { .. } => {
                // Effect is applied by `handle_call_return`.
            }
            mir::TerminatorKind::Drop { place, .. } => {
                state.flood_with(place.as_ref(), self.map, FlatSet::BOTTOM);
            }
            mir::TerminatorKind::SwitchInt { .. }
            | mir::TerminatorKind::Yield { .. }
            | mir::TerminatorKind::Goto { .. }
            | mir::TerminatorKind::UnwindResume
            | mir::TerminatorKind::UnwindTerminate(_)
            | mir::TerminatorKind::Return
            | mir::TerminatorKind::Unreachable
            | mir::TerminatorKind::Assert { .. }
            | mir::TerminatorKind::GeneratorDrop
            | mir::TerminatorKind::FalseEdge { .. }
            | mir::TerminatorKind::FalseUnwind { .. } => {
                // These terminators have no effect on the analysis.
            }
        }
        terminator.edges()
    }

    fn handle_call_return(
        &self,
        return_places: mir::CallReturnPlaces<'_, 'tcx>,
        state: &mut State,
    ) {
        return_places.for_each(|place| {
            state.flood(place.as_ref(), self.map);
        });
    }
}

impl<'a, 'tcx> rustc_mir_dataflow::AnalysisDomain<'tcx> for PointsToAnalysis<'a, 'tcx> {
    type Domain = State;

    type Direction = rustc_mir_dataflow::Forward;

    const NAME: &'static str = "PointsToAnalysis";

    fn bottom_value(&self, _body: &mir::Body<'tcx>) -> Self::Domain {
        State(StateData::Unreachable)
    }

    fn initialize_start_block(&self, body: &mir::Body<'tcx>, state: &mut Self::Domain) {
        // The initial state maps all tracked places of argument projections to ⊤ and the rest to ⊥.
        assert!(matches!(state.0, StateData::Unreachable));

        // Since we are skipping the early binder, we are using the early bound variables as locs instead
        // of fresh names. This is fine because the loc is just used as a unique value for the analysis.
        // We never have late bounds locs.
        let fn_sig = self.fn_sig.as_ref().skip_binder().as_ref().skip_binder();

        let values = IndexVec::from_elem_n(FlatSet::BOTTOM, self.map.value_count);
        *state = State(StateData::Reachable(values));
        for (local, ty) in iter::zip(body.args_iter(), fn_sig.args()) {
            if let rty::TyKind::Ptr(_, path) = ty.kind() {
                let loc = FlatSet::Elem(path.to_loc().unwrap());
                state.flood_with(mir::PlaceRef { local, projection: &[] }, self.map, loc);
            } else {
                state.flood(mir::PlaceRef { local, projection: &[] }, self.map);
            }
        }
    }
}

impl<'tcx> rustc_mir_dataflow::Analysis<'tcx> for PointsToAnalysis<'_, 'tcx> {
    fn apply_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &mir::Statement<'tcx>,
        _location: mir::Location,
    ) {
        if state.is_reachable() {
            self.handle_statement(statement, state);
        }
    }

    fn apply_terminator_effect<'mir>(
        &mut self,
        state: &mut Self::Domain,
        terminator: &'mir mir::Terminator<'tcx>,
        _location: mir::Location,
    ) -> mir::TerminatorEdges<'mir, 'tcx> {
        if state.is_reachable() {
            self.handle_terminator(terminator, state)
        } else {
            TerminatorEdges::None
        }
    }

    fn apply_call_return_effect(
        &mut self,
        state: &mut Self::Domain,
        _block: mir::BasicBlock,
        return_places: mir::CallReturnPlaces<'_, 'tcx>,
    ) {
        if state.is_reachable() {
            self.handle_call_return(return_places, state);
        }
    }

    fn apply_switch_int_edge_effects(
        &mut self,
        _block: mir::BasicBlock,
        _discr: &mir::Operand<'tcx>,
        _apply_edge_effects: &mut impl rustc_mir_dataflow::SwitchIntEdgeEffects<Self::Domain>,
    ) {
    }
}

/// Partial mapping from [`Place`] to [`PlaceIndex`], where some places also have a [`ValueIndex`].
///
/// This data structure essentially maintains a tree of places and their projections. Some
/// additional bookkeeping is done, to speed up traversal over this tree:
/// - For iteration, every [`PlaceInfo`] contains an intrusive linked list of its children.
/// - To directly get the child for a specific projection, there is a `projections` map.
#[derive(Debug)]
pub struct Map {
    locals: IndexVec<mir::Local, Option<PlaceIndex>>,
    projections: FxHashMap<(PlaceIndex, FieldIdx), PlaceIndex>,
    places: IndexVec<PlaceIndex, PlaceInfo>,
    value_count: usize,
    // The Range corresponds to a slice into `inner_values_buffer`.
    inner_values: IndexVec<PlaceIndex, Range<usize>>,
    inner_values_buffer: Vec<ValueIndex>,
}

impl Map {
    /// Returns a map that only tracks places whose type has scalar layout.
    ///
    /// This is currently the only way to create a [`Map`]. The way in which the tracked places are
    /// chosen is an implementation detail and may not be relied upon (other than that their type
    /// are scalars).
    pub fn new(body: &mir::Body) -> Self {
        let mut map = Self {
            locals: IndexVec::new(),
            projections: FxHashMap::default(),
            places: IndexVec::new(),
            value_count: 0,
            inner_values: IndexVec::new(),
            inner_values_buffer: Vec::new(),
        };
        let exclude = excluded_locals(body);
        map.register(body, exclude);
        map
    }

    /// Register all non-excluded places that have scalar layout.
    fn register(&mut self, body: &mir::Body, exclude: BitSet<mir::Local>) {
        let mut worklist = VecDeque::with_capacity(body.local_decls.len());

        // Start by constructing the places for each bare local.
        self.locals = IndexVec::from_elem(None, &body.local_decls);
        for (local, decl) in body.local_decls.iter_enumerated() {
            if exclude.contains(local) {
                continue;
            }

            // Create a place for the local.
            debug_assert!(self.locals[local].is_none());
            let place = self.places.push(PlaceInfo::new(None));
            self.locals[local] = Some(place);

            // And push the eventual children places to the worklist.
            self.register_children(place, decl.ty, &mut worklist);
        }

        // `place.elem` with type `ty`.
        while let Some((mut place, elem, ty)) = worklist.pop_front() {
            // Create a place for this projection.
            place = *self.projections.entry((place, elem)).or_insert_with(|| {
                // Prepend new child to the linked list.
                let next = self.places.push(PlaceInfo::new(Some(elem)));
                self.places[next].next_sibling = self.places[place].first_child;
                self.places[place].first_child = Some(next);
                next
            });

            // And push the eventual children places to the worklist.
            self.register_children(place, ty, &mut worklist);
        }

        // Pre-compute the tree of ValueIndex nested in each PlaceIndex.
        // `inner_values_buffer[inner_values[place]]` is the set of all the values
        // reachable by projecting `place`.
        self.inner_values_buffer = Vec::with_capacity(self.value_count);
        self.inner_values = IndexVec::from_elem(0..0, &self.places);
        for local in body.local_decls.indices() {
            if let Some(place) = self.locals[local] {
                self.cache_preorder_invoke(place);
            }
        }

        // Trim useless places.
        for opt_place in &mut self.locals {
            if let Some(place) = *opt_place && self.inner_values[place].is_empty() {
                *opt_place = None;
            }
        }
        self.projections
            .retain(|_, child| !self.inner_values[*child].is_empty());
    }

    /// Potentially register the (local, projection) place and its fields, recursively.
    ///
    /// Invariant: The projection must only contain trackable elements.
    fn register_children<'tcx>(
        &mut self,
        place: PlaceIndex,
        ty: ty::Ty<'tcx>,
        worklist: &mut VecDeque<(PlaceIndex, FieldIdx, ty::Ty<'tcx>)>,
    ) {
        // Allocate a value slot if it doesn't have one, and the user requested one.
        assert!(self.places[place].value_index.is_none());
        if let ty::TyKind::Ref(..) = ty.kind() {
            self.places[place].value_index = Some(self.value_count.into());
            self.value_count += 1;
        }

        // Add tuple fields to the worklist.
        if let ty::Tuple(list) = ty.kind() {
            for (field, ty) in list.iter().enumerate() {
                worklist.push_back((place, field.into(), ty));
            }
        }
    }

    /// Precompute the list of values inside `root` and store it inside
    /// as a slice within `inner_values_buffer`.
    fn cache_preorder_invoke(&mut self, root: PlaceIndex) {
        let start = self.inner_values_buffer.len();
        if let Some(vi) = self.places[root].value_index {
            self.inner_values_buffer.push(vi);
        }

        // We manually iterate instead of using `children` as we need to mutate `self`.
        let mut next_child = self.places[root].first_child;
        while let Some(child) = next_child {
            ensure_sufficient_stack(|| self.cache_preorder_invoke(child));
            next_child = self.places[child].next_sibling;
        }

        let end = self.inner_values_buffer.len();
        self.inner_values[root] = start..end;
    }

    /// Locates the given place, if it exists in the tree.
    pub fn find(&self, place: mir::PlaceRef<'_>) -> Option<PlaceIndex> {
        let mut index = *self.locals[place.local].as_ref()?;

        for &elem in place.projection {
            if let mir::ProjectionElem::Field(elem, _) = elem {
                index = self.apply(index, elem)?;
            }
        }

        Some(index)
    }

    /// Iterate over all direct children.
    pub fn children(&self, parent: PlaceIndex) -> impl Iterator<Item = PlaceIndex> + '_ {
        Children::new(self, parent)
    }

    /// Applies a single projection element, yielding the corresponding child.
    pub fn apply(&self, place: PlaceIndex, elem: FieldIdx) -> Option<PlaceIndex> {
        self.projections.get(&(place, elem)).copied()
    }

    /// Invoke a function on the given place and all places that may alias it.
    fn for_each_aliasing_place(&self, place: mir::PlaceRef<'_>, f: &mut impl FnMut(ValueIndex)) {
        let Some(mut index) = self.locals[place.local] else {
            // The local is not tracked at all, so it does not alias anything.
            return;
        };
        for elem in place.projection {
            let mir::ProjectionElem::Field(elem, _) = *elem else {
                return;
            };
            // A field aliases the parent place.
            if let Some(vi) = self.places[index].value_index {
                f(vi);
            }

            let Some(sub) = self.apply(index, elem) else {
                return;
            };
            index = sub;
        }
        self.for_each_value_inside(index, f);
    }

    /// Invoke a function on each value in the given place and all descendants.
    fn for_each_value_inside(&self, root: PlaceIndex, f: &mut impl FnMut(ValueIndex)) {
        let range = self.inner_values[root].clone();
        let values = &self.inner_values_buffer[range];
        for &v in values {
            f(v);
        }
    }

    fn for_each_tracked_place(&self, mut f: impl FnMut(PlaceIndex, mir::Local, &[FieldIdx])) {
        let mut projection = Vec::new();
        for (local, place) in self.locals.iter_enumerated() {
            if let Some(place) = place {
                self.for_each_tracked_place_rec(
                    *place,
                    &mut projection,
                    &mut |place, projection| {
                        f(place, local, projection);
                    },
                );
            }
        }
    }

    fn for_each_tracked_place_rec(
        &self,
        root: PlaceIndex,
        projection: &mut Vec<FieldIdx>,
        f: &mut impl FnMut(PlaceIndex, &[FieldIdx]),
    ) {
        // Fast path is there is nothing to do.
        if self.inner_values[root].is_empty() {
            return;
        }

        if self.places[root].value_index.is_some() {
            f(root, projection);
        }

        for child in self.children(root) {
            let elem = self.places[child].proj_elem.unwrap();
            projection.push(elem);
            self.for_each_tracked_place_rec(child, projection, f);
            projection.pop();
        }
    }
}

/// This is the information tracked for every [`PlaceIndex`] and is stored by [`Map`].
///
/// Together, `first_child` and `next_sibling` form an intrusive linked list, which is used to
/// model a tree structure (a replacement for a member like `children: Vec<PlaceIndex>`).
#[derive(Debug)]
struct PlaceInfo {
    /// We store a [`ValueIndex`] if and only if the placed is tracked by the analysis.
    value_index: Option<ValueIndex>,

    /// The projection used to go from parent to this node (only None for root).
    proj_elem: Option<FieldIdx>,

    /// The left-most child.
    first_child: Option<PlaceIndex>,

    /// Index of the sibling to the right of this node.
    next_sibling: Option<PlaceIndex>,
}

impl PlaceInfo {
    fn new(proj_elem: Option<FieldIdx>) -> Self {
        Self { next_sibling: None, proj_elem, first_child: None, value_index: None }
    }
}

struct Children<'a> {
    map: &'a Map,
    next: Option<PlaceIndex>,
}

impl<'a> Children<'a> {
    fn new(map: &'a Map, parent: PlaceIndex) -> Self {
        Self { map, next: map.places[parent].first_child }
    }
}

impl<'a> Iterator for Children<'a> {
    type Item = PlaceIndex;

    fn next(&mut self) -> Option<Self::Item> {
        match self.next {
            Some(child) => {
                self.next = self.map.places[child].next_sibling;
                Some(child)
            }
            None => None,
        }
    }
}

/// Returns all locals with projections that have their reference or address taken.
fn excluded_locals(body: &mir::Body<'_>) -> BitSet<mir::Local> {
    struct Collector {
        result: BitSet<mir::Local>,
    }

    impl<'tcx> mir::visit::Visitor<'tcx> for Collector {
        fn visit_place(
            &mut self,
            place: &mir::Place<'tcx>,
            context: mir::visit::PlaceContext,
            _location: mir::Location,
        ) {
            if (context.is_borrow()
                || context.is_address_of()
                || context.is_drop()
                || context
                    == mir::visit::PlaceContext::MutatingUse(
                        mir::visit::MutatingUseContext::AsmOutput,
                    ))
                && !place.is_indirect()
            {
                // A pointer to a place could be used to access other places with the same local,
                // hence we have to exclude the local completely.
                self.result.insert(place.local);
            }
        }
    }

    let mut collector = Collector { result: BitSet::new_empty(body.local_decls.len()) };
    collector.visit_body(body);
    collector.result
}

rustc_index::newtype_index!(
    /// This index uniquely identifies a place.
    ///
    /// Not every place has a `PlaceIndex`, and not every `PlaceIndex` corresponds to a tracked
    /// place. However, every tracked place and all places along its projection have a `PlaceIndex`.
    pub struct PlaceIndex {}
);

rustc_index::newtype_index!(
    /// This index uniquely identifies a tracked place and therefore a slot in [`State`].
    ///
    /// It is an implementation detail of this module.
    struct ValueIndex {}
);

/// Used as the result for r-value.
pub enum PlaceOrValue {
    Value(FlatSet<Loc>),
    Place(PlaceIndex),
}

impl PlaceOrValue {
    pub const TOP: Self = PlaceOrValue::Value(FlatSet::TOP);
}

/// See [`State`].
#[derive(PartialEq, Eq, Debug)]
enum StateData {
    Reachable(IndexVec<ValueIndex, FlatSet<Loc>>),
    Unreachable,
}

impl Clone for StateData {
    fn clone(&self) -> Self {
        match self {
            Self::Reachable(x) => Self::Reachable(x.clone()),
            Self::Unreachable => Self::Unreachable,
        }
    }

    fn clone_from(&mut self, source: &Self) {
        match (&mut *self, source) {
            (Self::Reachable(x), Self::Reachable(y)) => {
                // We go through `raw` here, because `IndexVec` currently has a naive `clone_from`.
                x.raw.clone_from(&y.raw);
            }
            _ => *self = source.clone(),
        }
    }
}

/// The dataflow state for an instance of [`ValueAnalysis`].
///
/// Every instance specifies a lattice that represents the possible values of a single tracked
/// place. If we call this lattice `V` and set of tracked places `P`, then a [`State`] is an
/// element of `{unreachable} ∪ (P -> V)`. This again forms a lattice, where the bottom element is
/// `unreachable` and the top element is the mapping `p ↦ ⊤`. Note that the mapping `p ↦ ⊥` is not
/// the bottom element (because joining an unreachable and any other reachable state yields a
/// reachable state). All operations on unreachable states are ignored.
///
/// Flooding means assigning a value (by default `⊤`) to all tracked projections of a given place.
#[derive(PartialEq, Eq, Debug)]
pub struct State(StateData);

impl Clone for State {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }

    fn clone_from(&mut self, source: &Self) {
        self.0.clone_from(&source.0);
    }
}

impl JoinSemiLattice for State {
    fn join(&mut self, other: &Self) -> bool {
        match (&mut self.0, &other.0) {
            (_, StateData::Unreachable) => false,
            (StateData::Unreachable, _) => {
                *self = other.clone();
                true
            }
            (StateData::Reachable(this), StateData::Reachable(other)) => this.join(other),
        }
    }
}

impl State {
    pub fn is_reachable(&self) -> bool {
        matches!(&self.0, StateData::Reachable(_))
    }

    pub fn flood(&mut self, place: mir::PlaceRef<'_>, map: &Map) {
        self.flood_with(place, map, FlatSet::TOP);
    }

    pub fn flood_with(&mut self, place: mir::PlaceRef<'_>, map: &Map, value: FlatSet<Loc>) {
        let StateData::Reachable(values) = &mut self.0 else { return };
        map.for_each_aliasing_place(place, &mut |vi| {
            values[vi] = value.clone();
        });
    }

    /// Helper method to interpret `target = result`.
    pub fn assign(&mut self, target: mir::PlaceRef<'_>, result: PlaceOrValue, map: &Map) {
        self.flood(target, map);
        if let Some(target) = map.find(target) {
            self.insert_idx(target, result, map);
        }
    }

    /// Low-level method that assigns to a place.
    /// This does nothing if the place is not tracked.
    ///
    /// The target place must have been flooded before calling this method.
    pub fn insert_idx(&mut self, target: PlaceIndex, result: PlaceOrValue, map: &Map) {
        match result {
            PlaceOrValue::Value(value) => self.insert_value_idx(target, value, map),
            PlaceOrValue::Place(source) => self.insert_place_idx(target, source, map),
        }
    }

    /// Copies `source` to `target`, including all tracked places beneath.
    ///
    /// If `target` contains a place that is not contained in `source`, it will be overwritten with
    /// Top. Also, because this will copy all entries one after another, it may only be used for
    /// places that are non-overlapping or identical.
    ///
    /// The target place must have been flooded before calling this method.
    pub fn insert_place_idx(&mut self, target: PlaceIndex, source: PlaceIndex, map: &Map) {
        let StateData::Reachable(values) = &mut self.0 else { return };

        // If both places are tracked, we copy the value to the target.
        // If the target is tracked, but the source is not, we do nothing, as invalidation has
        // already been performed.
        if let Some(target_value) = map.places[target].value_index {
            if let Some(source_value) = map.places[source].value_index {
                values[target_value] = values[source_value].clone();
            }
        }
        for target_child in map.children(target) {
            // Try to find corresponding child and recurse. Reasoning is similar as above.
            let projection = map.places[target_child].proj_elem.unwrap();
            if let Some(source_child) = map.projections.get(&(source, projection)) {
                self.insert_place_idx(target_child, *source_child, map);
            }
        }
    }

    /// Low-level method that assigns a value to a place.
    /// This does nothing if the place is not tracked.
    ///
    /// The target place must have been flooded before calling this method.
    pub fn insert_value_idx(&mut self, target: PlaceIndex, value: FlatSet<Loc>, map: &Map) {
        let StateData::Reachable(values) = &mut self.0 else { return };
        if let Some(value_index) = map.places[target].value_index {
            values[value_index] = value;
        }
    }

    /// Retrieve the value stored for a place, or ⊤ if it is not tracked.
    pub fn get(&self, place: mir::PlaceRef<'_>, map: &Map) -> FlatSet<Loc> {
        map.find(place)
            .map_or(FlatSet::TOP, |place| self.get_idx(place, map))
    }

    /// Retrieve the value stored for a place index, or ⊤ if it is not tracked.
    pub fn get_idx(&self, place: PlaceIndex, map: &Map) -> FlatSet<Loc> {
        match &self.0 {
            StateData::Reachable(values) => {
                map.places[place]
                    .value_index
                    .map_or(FlatSet::TOP, |v| values[v].clone())
            }
            StateData::Unreachable => {
                // Because this is unreachable, we can return any value we want.
                FlatSet::BOTTOM
            }
        }
    }
}

/// This is used to visualize the dataflow analysis.
impl<'a, 'tcx> DebugWithContext<PointsToAnalysis<'a, 'tcx>> for State {
    fn fmt_with(&self, ctxt: &PointsToAnalysis, f: &mut fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.0 {
            StateData::Reachable(values) => debug_with_context(values, None, ctxt.map, f),
            StateData::Unreachable => write!(f, "unreachable"),
        }
    }

    fn fmt_diff_with(
        &self,
        old: &Self,
        ctxt: &PointsToAnalysis,
        f: &mut fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        match (&self.0, &old.0) {
            (StateData::Reachable(this), StateData::Reachable(old)) => {
                debug_with_context(this, Some(old), ctxt.map, f)
            }
            _ => Ok(()), // Consider printing something here.
        }
    }
}

fn debug_with_context_rec<V: fmt::Debug + Eq>(
    place: PlaceIndex,
    place_str: &str,
    new: &IndexSlice<ValueIndex, V>,
    old: Option<&IndexSlice<ValueIndex, V>>,
    map: &Map,
    f: &mut fmt::Formatter<'_>,
) -> std::fmt::Result {
    if let Some(value) = map.places[place].value_index {
        match old {
            None => writeln!(f, "{}: {:?}", place_str, new[value])?,
            Some(old) => {
                if new[value] != old[value] {
                    writeln!(f, "\u{001f}-{}: {:?}", place_str, old[value])?;
                    writeln!(f, "\u{001f}+{}: {:?}", place_str, new[value])?;
                }
            }
        }
    }

    for child in map.children(place) {
        let info_elem = map.places[child].proj_elem.unwrap();
        let child_place_str = format!("{}.{}", place_str, info_elem.index());
        debug_with_context_rec(child, &child_place_str, new, old, map, f)?;
    }

    Ok(())
}

fn debug_with_context<V: fmt::Debug + Eq>(
    new: &IndexSlice<ValueIndex, V>,
    old: Option<&IndexSlice<ValueIndex, V>>,
    map: &Map,
    f: &mut fmt::Formatter<'_>,
) -> std::fmt::Result {
    for (local, place) in map.locals.iter_enumerated() {
        if let Some(place) = place {
            debug_with_context_rec(*place, &format!("{local:?}"), new, old, map, f)?;
        }
    }
    Ok(())
}
