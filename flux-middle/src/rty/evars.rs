use std::sync::atomic::{AtomicU64, Ordering::Relaxed};

use flux_common::index::IndexVec;
use rustc_hash::FxHashMap;
use rustc_index::newtype_index;

use super::Expr;

static NEXT_CTXT_ID: AtomicU64 = AtomicU64::new(0);

#[derive(Debug, Default)]
pub struct EVarGen {
    evars: FxHashMap<CtxtId, IndexVec<EVid, EVarEntry>>,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct EVar {
    pub cx: CtxtId,
    id: EVid,
}

#[derive(Debug)]
pub enum EVarEntry {
    Unresolved,
    Resolved(Expr),
}

newtype_index! {
    struct EVid {}
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct CtxtId(u64);

impl EVarGen {
    pub fn new() -> Self {
        EVarGen { evars: FxHashMap::default() }
    }

    pub fn new_ctxt(&mut self) -> CtxtId {
        let cx = CtxtId(NEXT_CTXT_ID.fetch_add(1, Relaxed));
        self.evars.insert(cx, IndexVec::new());
        cx
    }

    pub fn fresh_in_cx(&mut self, cx: CtxtId) -> EVar {
        let evid = self.evars.get_mut(&cx).unwrap().push(EVarEntry::Unresolved);
        EVar { id: evid, cx }
    }

    pub fn solve(&mut self, evar: EVar, expr: impl Into<Expr>, replace: bool) {
        let evars = self.evars.get_mut(&evar.cx).unwrap();
        if matches!(evars[evar.id], EVarEntry::Unresolved) || replace {
            evars[evar.id] = EVarEntry::Resolved(expr.into());
        }
    }

    pub fn entry(&self, evar: EVar) -> Option<&EVarEntry> {
        Some(&self.evars.get(&evar.cx)?[evar.id])
    }
}

mod pretty {
    use super::*;
    use crate::pretty::*;

    impl Pretty for EVar {
        fn fmt(&self, _cx: &PPrintCx, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            define_scoped!(cx, f);
            w!("?e{}", ^self.id.as_u32())
        }
    }

    impl_debug_with_default_cx!(EVar);
}
