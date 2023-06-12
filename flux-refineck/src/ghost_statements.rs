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
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::{mir::Location, ty::TyCtxt};

use crate::fold_unfold;

pub(crate) struct GhostStatements {
    pub at_location: LocationMap,
    pub at_goto: GotoMap,
}

type LocationMap = FxHashMap<Location, Vec<GhostStatement>>;
type GotoMap = FxHashMap<BasicBlock, FxHashMap<BasicBlock, Vec<GhostStatement>>>;

pub(crate) enum GhostStatement {
    Fold(Place),
    Unfold(Place),
    Unblock(Place),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) enum Point {
    Location(Location),
    Edge(BasicBlock, BasicBlock),
}

pub(crate) fn compute_ghost_statements(
    genv: &GlobalEnv,
    def_id: LocalDefId,
) -> QueryResult<FxHashMap<DefId, GhostStatements>> {
    let mut data = FxHashMap::default();
    for def_id in all_nested_bodies(genv.tcx, def_id) {
        data.insert(def_id.to_def_id(), GhostStatements::new(genv, def_id)?);
    }
    Ok(data)
}

impl GhostStatements {
    fn new(genv: &GlobalEnv, def_id: LocalDefId) -> QueryResult<Self> {
        let body = genv.mir(def_id)?;
        let fold_unfolds = fold_unfold::run_analysis(genv, &body)?;
        let mut at_location = LocationMap::default();
        let mut at_goto = GotoMap::default();
        for (point, stmts) in fold_unfolds.into_statements() {
            match point {
                Point::Location(location) => at_location.entry(location).or_default().extend(stmts),
                Point::Edge(from, to) => {
                    at_goto
                        .entry(from)
                        .or_default()
                        .entry(to)
                        .or_default()
                        .extend(stmts);
                }
            }
        }
        for (location, borrows) in body.calculate_borrows_out_of_scope_at_location() {
            let stmts = borrows.into_iter().map(|bidx| {
                let borrow = body.borrow_data(bidx);
                let place = lowering::lower_place(&borrow.borrowed_place).unwrap();
                GhostStatement::Unblock(place)
            });
            at_location.entry(location).or_default().extend(stmts);
        }
        let stmts = Self { at_location, at_goto };
        if config::dump_mir() {
            let mut writer =
                dbg::writer_for_item(genv.tcx, def_id.to_def_id(), "ghost.mir").unwrap();
            stmts.write_mir(&body, &mut writer).unwrap();
        }
        Ok(stmts)
    }

    pub(crate) fn statements_at(&self, point: Point) -> impl Iterator<Item = &GhostStatement> {
        match point {
            Point::Location(location) => self.at_location.get(&location).into_iter().flatten(),
            Point::Edge(from, to) => {
                self.at_goto
                    .get(&from)
                    .and_then(|m| m.get(&to))
                    .into_iter()
                    .flatten()
            }
        }
    }

    pub(crate) fn write_mir<W: io::Write>(&self, body: &Body, w: &mut W) -> io::Result<()> {
        for (bb, data) in body.basic_blocks.iter_enumerated() {
            let mut location = Location { block: bb, statement_index: 0 };
            write!(w, "{bb:?}: {{")?;
            for stmt in &data.statements {
                for stmt in self.statements_at(Point::Location(location)) {
                    write!(w, "\n    {stmt:?};")?;
                }
                location = location.successor_within_block();

                if stmt.is_nop() {
                    continue;
                }
                write!(w, "\n    {stmt:?};")?;
            }
            for stmt in self.statements_at(Point::Location(location)) {
                write!(w, "\n    {stmt:?};")?;
            }
            if let Some(terminator) = &data.terminator {
                write!(w, "\n    {terminator:?}")?;
            }
            if let Some(map) = self.at_goto.get(&bb) {
                writeln!(w)?;
                for (target, stmts) in map {
                    write!(w, "\n    -> {target:?} {{")?;
                    for stmt in stmts {
                        write!(w, "\n        {stmt:?};")?;
                    }
                    write!(w, "\n    }}")?;
                }
            }
            writeln!(w, "\n}}\n")?;
        }
        Ok(())
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
    let body_id = hir.body_owned_by(def_id);
    let body_expr = hir.body(body_id).value;
    let mut finder = ClosureFinder { hir, closures: FxHashSet::default() };
    hir::intravisit::Visitor::visit_expr(&mut finder, body_expr);
    finder.closures.into_iter().chain(iter::once(def_id))
}

impl fmt::Debug for GhostStatement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            GhostStatement::Fold(place) => write!(f, "fold({place:?})"),
            GhostStatement::Unfold(place) => write!(f, "unfold({place:?})"),
            GhostStatement::Unblock(place) => write!(f, "unblock({place:?})"),
        }
    }
}
