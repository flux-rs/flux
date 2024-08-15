//! Ghost statements are statements that are not part of the original mir, but are added from information
//! extracted from the compiler or some additional analysis.
mod fold_unfold;
mod points_to;

use std::{fmt, io, iter};

use flux_common::dbg;
use flux_config as config;
use flux_middle::{
    global_env::GlobalEnv,
    queries::QueryResult,
    rustc::{
        lowering,
        mir::{BasicBlock, Body, Place},
    },
};
use rustc_data_structures::unord::UnordMap;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{def::DefKind, def_id::LocalDefId};
use rustc_middle::{
    mir::{Location, START_BLOCK},
    ty::TyCtxt,
};

type LocationMap = FxHashMap<Location, Vec<GhostStatement>>;
type EdgeMap = FxHashMap<BasicBlock, FxHashMap<BasicBlock, Vec<GhostStatement>>>;

pub(crate) fn compute_ghost_statements(
    genv: GlobalEnv,
    def_id: LocalDefId,
) -> QueryResult<UnordMap<LocalDefId, GhostStatements>> {
    let mut data = UnordMap::default();
    for def_id in all_nested_bodies(genv.tcx(), def_id) {
        data.insert(def_id, GhostStatements::new(genv, def_id)?);
    }
    Ok(data)
}

pub(crate) enum GhostStatement {
    Fold(Place),
    Unfold(Place),
    Unblock(Place),
    PtrToRef(Place),
}

impl fmt::Debug for GhostStatement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            GhostStatement::Fold(place) => write!(f, "fold({place:?})"),
            GhostStatement::Unfold(place) => write!(f, "unfold({place:?})"),
            GhostStatement::Unblock(place) => write!(f, "unblock({place:?})"),
            GhostStatement::PtrToRef(place) => write!(f, "ptr_to_ref({place:?})"),
        }
    }
}

pub(crate) struct GhostStatements {
    at_start: Vec<GhostStatement>,
    at_location: LocationMap,
    at_edge: EdgeMap,
}

impl GhostStatements {
    fn new(genv: GlobalEnv, def_id: LocalDefId) -> QueryResult<Self> {
        let body = genv.mir(def_id)?;

        let mut stmts = Self {
            at_start: Default::default(),
            at_location: LocationMap::default(),
            at_edge: EdgeMap::default(),
        };

        // We have fn_sig for function items, but not for closures or generators.
        let fn_sig = if genv.def_kind(def_id) == DefKind::Closure {
            None
        } else {
            Some(genv.fn_sig(def_id)?)
        };

        fold_unfold::add_ghost_statements(&mut stmts, genv, &body, fn_sig.as_ref())?;
        points_to::add_ghost_statements(&mut stmts, genv, body.rustc_body(), fn_sig.as_ref())?;
        stmts.add_unblocks(&body);

        if config::dump_mir() {
            let mut writer =
                dbg::writer_for_item(genv.tcx(), def_id.to_def_id(), "ghost.mir").unwrap();
            stmts.write_mir(genv.tcx(), &body, &mut writer).unwrap();
        }
        Ok(stmts)
    }

    fn add_unblocks(&mut self, body: &Body) {
        for (location, borrows) in body.calculate_borrows_out_of_scope_at_location() {
            let stmts = borrows.into_iter().map(|bidx| {
                let borrow = body.borrow_data(bidx);
                let place = lowering::lower_place(&borrow.borrowed_place).unwrap();
                GhostStatement::Unblock(place)
            });
            self.at_location.entry(location).or_default().extend(stmts);
        }
    }

    fn insert_at(&mut self, point: Point, stmt: GhostStatement) {
        self.extend_at(point, [stmt]);
    }

    fn extend_at(&mut self, point: Point, stmts: impl IntoIterator<Item = GhostStatement>) {
        match point {
            Point::FunEntry => {
                self.at_start.extend(stmts);
            }
            Point::BeforeLocation(location) => {
                self.at_location.entry(location).or_default().extend(stmts);
            }
            Point::Edge(from, to) => {
                self.at_edge
                    .entry(from)
                    .or_default()
                    .entry(to)
                    .or_default()
                    .extend(stmts);
            }
        }
    }

    fn at(&mut self, point: Point) -> StatementsAt {
        StatementsAt { stmts: self, point }
    }

    pub(crate) fn statements_at(&self, point: Point) -> impl Iterator<Item = &GhostStatement> {
        match point {
            Point::FunEntry => Some(&self.at_start).into_iter().flatten(),
            Point::BeforeLocation(location) => {
                self.at_location.get(&location).into_iter().flatten()
            }
            Point::Edge(from, to) => {
                self.at_edge
                    .get(&from)
                    .and_then(|m| m.get(&to))
                    .into_iter()
                    .flatten()
            }
        }
    }

    pub(crate) fn write_mir<'tcx, W: io::Write>(
        &self,
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        w: &mut W,
    ) -> io::Result<()> {
        use rustc_middle::mir::PassWhere;
        rustc_middle::mir::pretty::write_mir_fn(
            tcx,
            body.inner(),
            &mut |pass, w| {
                match pass {
                    PassWhere::BeforeBlock(bb) if bb == START_BLOCK => {
                        for stmt in &self.at_start {
                            writeln!(w, "    {stmt:?};")?;
                        }
                    }
                    PassWhere::BeforeLocation(location) => {
                        for stmt in self.statements_at(Point::BeforeLocation(location)) {
                            writeln!(w, "        {stmt:?};")?;
                        }
                    }
                    PassWhere::AfterTerminator(bb) => {
                        if let Some(map) = self.at_edge.get(&bb) {
                            writeln!(w)?;
                            for (target, stmts) in map {
                                write!(w, "        -> {target:?} {{")?;
                                for stmt in stmts {
                                    write!(w, "\n            {stmt:?};")?;
                                }
                                write!(w, "\n        }}")?;
                            }
                            writeln!(w)?;
                        }
                    }
                    _ => {}
                }
                Ok(())
            },
            w,
        )
    }
}

/// A point in the control flow graph where ghost statements can be inserted.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) enum Point {
    /// The entry of the function before the first basic block. This is not the same as the first
    /// location in the first basic block because, for some functions, the first basic block can have
    /// incoming edges, and we want to execute ghost statements only once.
    FunEntry,
    /// The point before a location in a basic block.
    BeforeLocation(Location),
    /// An edge between two basic blocks.
    Edge(BasicBlock, BasicBlock),
}

struct StatementsAt<'a> {
    stmts: &'a mut GhostStatements,
    point: Point,
}

impl StatementsAt<'_> {
    fn insert(&mut self, stmt: GhostStatement) {
        self.stmts.insert_at(self.point, stmt);
    }
}

fn all_nested_bodies(tcx: TyCtxt, def_id: LocalDefId) -> impl Iterator<Item = LocalDefId> {
    use rustc_hir as hir;
    struct ClosureFinder<'hir> {
        hir: rustc_middle::hir::map::Map<'hir>,
        closures: FxHashSet<LocalDefId>,
    }

    impl<'hir> rustc_hir::intravisit::Visitor<'hir> for ClosureFinder<'hir> {
        type NestedFilter = rustc_middle::hir::nested_filter::OnlyBodies;

        fn nested_visit_map(&mut self) -> Self::Map {
            self.hir
        }

        fn visit_expr(&mut self, ex: &'hir hir::Expr<'hir>) {
            if let hir::ExprKind::Closure(closure) = ex.kind {
                self.closures.insert(closure.def_id);
            }

            hir::intravisit::walk_expr(self, ex);
        }
    }
    let hir = tcx.hir();
    let body = hir.body_owned_by(def_id).value;
    let mut finder = ClosureFinder { hir, closures: FxHashSet::default() };
    hir::intravisit::Visitor::visit_expr(&mut finder, body);
    finder.closures.into_iter().chain(iter::once(def_id))
}
