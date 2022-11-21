use std::sync::atomic::{AtomicU64, Ordering::Relaxed};

use flux_common::index::IndexVec;
use rustc_index::newtype_index;

use super::Expr;

static NEXT_CTXT_ID: AtomicU64 = AtomicU64::new(0);

#[derive(Debug)]
pub struct EVarCtxt {
    id: CtxtId,
    evars: IndexVec<EVid, EVarEntry>,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct EVar {
    id: EVid,
    cx: CtxtId,
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
struct CtxtId(u64);

impl EVarCtxt {
    pub fn new() -> Self {
        let id = CtxtId(NEXT_CTXT_ID.fetch_add(1, Relaxed));
        EVarCtxt { id, evars: IndexVec::new() }
    }

    pub fn fresh(&mut self) -> EVar {
        let evid = self.evars.push(EVarEntry::Unresolved);
        EVar { id: evid, cx: self.id }
    }

    pub fn solve(&mut self, evar: EVar, expr: impl Into<Expr>) {
        debug_assert_eq!(evar.cx, self.id);
        self.evars[evar.id] = EVarEntry::Resolved(expr.into());
    }

    pub fn entry(&self, evar: EVar) -> Option<&EVarEntry> {
        if evar.cx != self.id {
            return None;
        }
        Some(&self.evars[evar.id])
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
