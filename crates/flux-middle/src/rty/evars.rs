use std::sync::atomic::{AtomicU64, Ordering::Relaxed};

use flux_common::{bug, index::IndexVec};
use itertools::Itertools;
use rustc_data_structures::fx::FxIndexMap;
use rustc_hash::FxHashMap;
use rustc_index::newtype_index;
use rustc_macros::{Decodable, Encodable};

use super::{Expr, ExprKind, Var};

// FIXME(nilehmann) since an `EVarGen` is created multiple times per function, we keep contexts ids
// unique globally to avoid any unintended clash. We should instead create on `EVarGen` per function
// in which case we can possible keep idx unique per `EVarGen`.
static NEXT_CTXT_ID: AtomicU64 = AtomicU64::new(0);

/// A generator of evars. Evars are associated with a context. Contexts are visited in a stack-like
/// fashion. When entering a context data can be associated to that particular context. When a context
/// is exited, all its evars are put in a list of pending contexts. No more evars can be generated
/// for pending contexts, but they can still be unified. At any point, pending contexts can be solved,
/// returning a solution for all of their evars or an error if some evar hasn't been unified yet.
#[derive(Debug)]
pub struct EVarGen<T> {
    stack: FxIndexMap<EVarCxId, EVarCtxt<T>>,
    pending: FxIndexMap<EVarCxId, EVarCtxt<T>>,
}

impl<T> Default for EVarGen<T> {
    fn default() -> Self {
        Self { stack: Default::default(), pending: Default::default() }
    }
}

#[derive(Debug)]
struct EVarCtxt<T> {
    vars: IndexVec<EVid, EVarState>,
    data: T,
}

pub struct EVarSol {
    evars: FxHashMap<EVarCxId, IndexVec<EVid, Expr>>,
}

/// An *e*xistential *var*riable is identified by a context and an id. Two evars
/// are considered equal if both the context and id are equal.
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Encodable, Decodable)]
pub struct EVar {
    cx: EVarCxId,
    id: EVid,
}

#[derive(Debug)]
pub struct UnsolvedEvar {
    pub evar: EVar,
}

#[derive(Debug)]
enum EVarState {
    Unsolved,
    Unified(Expr),
}

newtype_index! {
    /// *E*xistential *v*ariable *id*
    #[orderable]
    #[encodable]
    struct EVid {}
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, PartialOrd, Ord, Encodable, Decodable)]
pub struct EVarCxId(u64);

impl EVar {
    pub fn cx(&self) -> EVarCxId {
        self.cx
    }
}

impl<T> EVarGen<T> {
    /// Enters a new context generating a context id guaranteed to be globally fresh. That is, it
    /// will be unique among context ids generated by this or other instances of [`EVarGen`]. The
    /// context can be used to generate fresh evars by calling [`EVarGen::fresh_in`].
    pub fn enter_context(&mut self, data: T) -> EVarCxId {
        let cxid = EVarCxId(NEXT_CTXT_ID.fetch_add(1, Relaxed));
        self.stack
            .insert(cxid, EVarCtxt { vars: IndexVec::new(), data });
        cxid
    }

    /// Exit the current context, putting it in the pending list.
    pub fn exit_context(&mut self) -> EVarCxId {
        let (cxid, ctxt) = self.stack.pop().unwrap();
        self.pending.insert(cxid, ctxt);
        cxid
    }

    /// Generates an evar guaranteed to be fresh in the provided context.
    ///
    /// # Panics
    ///
    /// This function panics if the context `cxid` was not generated by this [`EVarGen`] instance or
    /// has already been popped.
    pub fn fresh_in(&mut self, cxid: EVarCxId) -> EVar {
        let evid = self
            .stack
            .get_mut(&cxid)
            .unwrap()
            .vars
            .push(EVarState::Unsolved);
        EVar { id: evid, cx: cxid }
    }

    /// Generates a fresh evar in the current (top of the stack) context
    pub fn fresh_in_current(&mut self) -> EVar {
        let cxid = *self.stack.last().unwrap().0;
        self.fresh_in(cxid)
    }

    /// Returns the data associated with the context `cxid`
    ///
    /// # Panics
    ///
    /// This function panics if the context `cxid` was not generated by this [`EVarGen`] instance.
    pub fn data(&self, cxid: EVarCxId) -> &T {
        &self
            .stack
            .get(&cxid)
            .or_else(|| self.pending.get(&cxid))
            .unwrap()
            .data
    }

    pub fn current_data(&self) -> &T {
        &self
            .stack
            .last()
            .unwrap_or_else(|| bug!("no context"))
            .1
            .data
    }

    pub fn unify(&mut self, evar: EVar, arg: impl Into<Expr>, replace: bool) {
        let evars = &mut self.stack.get_mut(&evar.cx).unwrap().vars;
        if matches!(evars[evar.id], EVarState::Unsolved) || replace {
            evars[evar.id] = EVarState::Unified(arg.into());
        }
    }

    /// Try to solve evars in all pending contexts and then empty the pending list.
    pub fn try_solve_pending(&mut self) -> Result<EVarSol, UnsolvedEvar> {
        let evars = self
            .pending
            .drain(..)
            .map(|(cx, evars)| {
                let evars = evars
                    .vars
                    .into_iter_enumerated()
                    .map(|(id, state)| {
                        match state {
                            EVarState::Unsolved => Err(UnsolvedEvar { evar: EVar { cx, id } }),
                            EVarState::Unified(e) => Ok(e),
                        }
                    })
                    .try_collect()?;
                Ok((cx, evars))
            })
            .try_collect()?;

        let mut sol = EVarSol { evars };
        sol.fix();
        Ok(sol)
    }
}

impl EVarSol {
    fn fix(&mut self) {
        let vec = self
            .iter()
            .flat_map(|(evar, arg)| {
                if let ExprKind::Var(Var::EVar(evar2)) = arg.kind() {
                    Some((evar, self.get(*evar2).unwrap().clone()))
                } else {
                    None
                }
            })
            .collect_vec();
        for (evar, arg) in vec {
            self.evars.get_mut(&evar.cx).unwrap()[evar.id] = arg;
        }
    }

    pub(crate) fn get(&self, evar: EVar) -> Option<&Expr> {
        Some(&self.evars.get(&evar.cx)?[evar.id])
    }

    fn iter(&self) -> impl Iterator<Item = (EVar, &Expr)> {
        self.evars.iter().flat_map(|(cx, args)| {
            args.iter_enumerated().map(|(id, expr)| {
                let evar = EVar { cx: *cx, id };
                (evar, expr)
            })
        })
    }
}

mod pretty {
    use std::fmt;

    use rustc_data_structures::fx::FxIndexMap;

    use super::*;
    use crate::pretty::*;

    impl Pretty for EVar {
        fn fmt(&self, _cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!("?{}e#{}", ^self.id.as_u32(), ^self.cx.0)
        }
    }

    impl fmt::Debug for EVarSol {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let map: FxIndexMap<EVar, _> = self.iter().collect();
            fmt::Debug::fmt(&map, f)
        }
    }

    impl_debug_with_default_cx!(EVar);
}
