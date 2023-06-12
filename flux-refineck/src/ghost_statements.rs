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
use itertools::Itertools;
use rustc_data_structures::fx::FxIndexMap;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::{mir::Location, ty::TyCtxt};

use crate::fold_unfold::{self, FoldUnfolds};

pub(crate) struct GhostStatements {
    pub fold_unfolds: FoldUnfolds,
    pub unblocks: FxIndexMap<Point, Vec<GhostStatement>>,
}

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

impl GhostStatements {
    fn new(genv: &GlobalEnv, def_id: LocalDefId) -> QueryResult<Self> {
        let body = genv.mir(def_id)?;
        let fold_unfolds = fold_unfold::run_analysis(genv, &body)?;
        let unblocks = body
            .calculate_borrows_out_of_scope_at_location()
            .into_iter()
            .map(|(location, idxs)| {
                let stmts = idxs
                    .into_iter()
                    .map(|idx| {
                        let borrow = body.borrow_data(idx);
                        let place = lowering::lower_place(&borrow.borrowed_place).unwrap();
                        GhostStatement::Unblock(place)
                    })
                    .collect_vec();
                (Point::Location(location), stmts)
            })
            .collect();
        let stmts = Self { fold_unfolds, unblocks };
        if config::dump_mir() {
            let mut writer =
                dbg::writer_for_item(genv.tcx, def_id.to_def_id(), "ghost.mir").unwrap();
            stmts.write_mir(&body, &mut writer).unwrap();
        }
        Ok(stmts)
    }

    pub(crate) fn statements_at(&self, point: Point) -> impl Iterator<Item = &GhostStatement> {
        let fold_unfolds = self.fold_unfolds.fold_unfolds_at(point);
        let unblocks = self
            .unblocks
            .get(&point)
            .map_or([].as_slice(), Vec::as_slice)
            .iter();
        fold_unfolds.chain(unblocks)
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
            writeln!(w, "\n}}\n")?;
        }
        Ok(())
    }
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
