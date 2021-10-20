use std::fmt::{self, Write};

use itertools::Itertools;
use liquid_rust_common::{format::PadAdapter, index::IndexVec};
use rustc_hash::FxHashMap;

use crate::ty::{EVar, Expr, Sort};

pub struct UnificationCtxt {
    sorts: FxHashMap<EVar, Sort>,
    parent: IndexVec<EVar, EVar>,
    subst: FxHashMap<EVar, Expr>,
}

impl UnificationCtxt {
    pub fn new() -> Self {
        Self {
            sorts: FxHashMap::default(),
            parent: IndexVec::new(),
            subst: FxHashMap::default(),
        }
    }

    pub fn new_evar(&mut self, sort: Sort) -> EVar {
        let evar = self.parent.next_index();
        self.parent.push(evar);
        self.sorts.insert(evar, sort);
        evar
    }

    pub fn unify(&mut self, evar1: EVar, evar2: EVar) {
        let evar1 = self.find_mut(evar1);
        let evar2 = self.find_mut(evar2);
        self.parent[evar1] = evar2;

        assert!(self.sorts[&evar1] == self.sorts[&evar2]);
        self.sorts.remove(&evar2);
    }

    pub fn instantiate(&mut self, evar: EVar, expr: Expr, sort: Sort) {
        let evar = self.find_mut(evar);
        assert!(self.sorts.get(&evar) == Some(&sort));
        assert!(self.subst.insert(evar, expr).is_none());
    }

    pub fn lookup(&self, evar: EVar) -> Option<Expr> {
        self.subst.get(&self.find(evar)).cloned()
    }

    fn find_mut(&mut self, evar: EVar) -> EVar {
        if self.parent[evar] != evar {
            self.parent[evar] = self.find_mut(self.parent[evar])
        }
        self.parent[evar]
    }

    fn find(&self, mut evar: EVar) -> EVar {
        while self.parent[evar] != evar {
            evar = self.parent[evar];
        }
        evar
    }
}

impl fmt::Debug for UnificationCtxt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "UnificationCtxt {{")?;
        let groups = self
            .parent
            .iter()
            .into_group_map_by(|&&evar| self.find(evar));
        let mut w = PadAdapter::wrap_fmt(f);
        for (evar, group) in groups {
            write!(
                w,
                "\n{{{:?}}}: {:?}{}",
                group.iter().format(", "),
                self.sorts[&evar],
                match self.subst.get(&evar) {
                    Some(expr) => format!(" -> {:?}", expr),
                    None => "".to_string(),
                },
            )?;
        }
        write!(f, "\n}}")
    }
}
