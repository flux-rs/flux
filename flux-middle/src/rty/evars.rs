use std::sync::atomic::{AtomicU64, Ordering::Relaxed};

use flux_common::index::IndexVec;
use itertools::Itertools;
use rustc_hash::FxHashMap;
use rustc_index::newtype_index;
use rustc_macros::{Decodable, Encodable};

use super::{Expr, ExprKind, Var};

static NEXT_CTXT_ID: AtomicU64 = AtomicU64::new(0);

#[derive(Debug, Default)]
pub struct EVarGen {
    evars: FxHashMap<EVarCxId, IndexVec<EVid, EVarState>>,
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
    struct EVid {}
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, PartialOrd, Ord, Encodable, Decodable)]
pub struct EVarCxId(u64);

impl EVar {
    pub fn cx(&self) -> EVarCxId {
        self.cx
    }
}

impl EVarGen {
    pub fn new() -> Self {
        EVarGen { evars: FxHashMap::default() }
    }

    /// Generates a context id guaranteed to be globally fresh. That is, it will be unique
    /// among context ids generated by this or other instances of [`EVarGen`]. The context
    /// can be used to generate fresh evars by calling [`EVarGen::fresh_in_cx`].
    pub fn new_ctxt(&mut self) -> EVarCxId {
        let cx = EVarCxId(NEXT_CTXT_ID.fetch_add(1, Relaxed));
        self.evars.insert(cx, IndexVec::new());
        cx
    }

    /// Generates an evar guaranteed to be fresh in the provided context.
    ///
    /// # Panics
    ///
    /// This function panics if the context `cx` was not generated by this [`EVarGen`] instance.
    pub fn fresh_in_cx(&mut self, cx: EVarCxId) -> EVar {
        let evid = self.evars.get_mut(&cx).unwrap().push(EVarState::Unsolved);
        EVar { id: evid, cx }
    }

    pub fn unify(&mut self, evar: EVar, arg: impl Into<Expr>, replace: bool) {
        let evars = self.evars.get_mut(&evar.cx).unwrap();
        if matches!(evars[evar.id], EVarState::Unsolved) || replace {
            evars[evar.id] = EVarState::Unified(arg.into());
        }
    }

    pub fn solve(self) -> Result<EVarSol, UnsolvedEvar> {
        let evars = self
            .evars
            .into_iter()
            .map(|(cx, evars)| {
                let evars = evars
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
        fn fmt(&self, _cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!("?e{}#{}", ^self.id.as_u32(), ^self.cx.0)
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
