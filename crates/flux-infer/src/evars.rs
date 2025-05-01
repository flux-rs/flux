use std::fmt;

use flux_common::index::IndexVec;
use flux_middle::{
    pretty::{Pretty, PrettyCx, impl_debug_with_default_cx, w},
    rty::{EVid, Expr, fold::TypeFoldable},
};

use crate::refine_tree::Marker;

#[derive(Default, Debug)]
pub(crate) struct EVarStore {
    evars: IndexVec<EVid, EVarState>,
    scopes: Vec<Vec<EVid>>,
}

pub(crate) enum EVarState {
    Solved(Expr),
    Unsolved(Marker),
}

impl EVarStore {
    pub(crate) fn fresh(&mut self, marker: Marker) -> EVid {
        let evid = self.evars.push(EVarState::Unsolved(marker));
        if let Some(scope) = self.scopes.last_mut() {
            scope.push(evid);
        }
        evid
    }

    pub(crate) fn push_scope(&mut self) {
        self.scopes.push(vec![]);
    }

    pub(crate) fn pop_scope(&mut self) -> Result<(), EVid> {
        let Some(scope) = self.scopes.pop() else { return Ok(()) };
        for evid in scope {
            if let EVarState::Unsolved(..) = self.get(evid) {
                panic!("pop_scope: {evid:?}");
                return Err(evid);
            }
        }
        Ok(())
    }

    pub(crate) fn replace_evars<T: TypeFoldable>(&self, t: &T) -> Result<T, EVid> {
        t.replace_evars(&mut |evid| {
            match self.get(evid) {
                EVarState::Solved(expr) => Some(expr.clone()),
                EVarState::Unsolved(..) => None,
            }
        })
    }

    pub(crate) fn solve(&mut self, evid: EVid, expr: Expr) {
        debug_assert!(matches!(self.evars[evid], EVarState::Unsolved(_)));
        self.evars[evid] = EVarState::Solved(expr);
    }

    pub(crate) fn get(&self, evid: EVid) -> &EVarState {
        &self.evars[evid]
    }
}

impl Pretty for EVarState {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EVarState::Solved(expr) => w!(cx, f, "Solved({:?})", expr),
            EVarState::Unsolved(_) => w!(cx, f, "Unsolved"),
        }
    }
}

impl_debug_with_default_cx!(EVarState);
