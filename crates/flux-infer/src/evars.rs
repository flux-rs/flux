use flux_common::index::IndexVec;
use flux_middle::rty::{fold::TypeFoldable, EVid, Expr};

use crate::refine_tree::{RefineCtxt, Snapshot};

#[derive(Default)]
pub(crate) struct EVarStore {
    evars: IndexVec<EVid, EVarState>,
    scopes: Vec<Vec<EVid>>,
    // document
    a: usize,
}

pub(crate) enum EVarState {
    Solved(Expr),
    Unsolved(Snapshot),
}

impl EVarStore {
    pub(crate) fn fresh(&mut self, rcx: &RefineCtxt) -> EVid {
        let evid = self.evars.push(EVarState::Unsolved(rcx.snapshot()));
        if let Some(scope) = self.scopes.last_mut() {
            scope.push(evid);
        }
        evid
    }

    pub(crate) fn push_scope(&mut self) {
        self.scopes.push(vec![]);
    }

    pub(crate) fn pop_scope(&mut self) -> Result<(), EVid> {
        let scope = self.scopes.pop().unwrap();
        for evid in scope {
            if let EVarState::Unsolved(..) = self.get(evid) {
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
