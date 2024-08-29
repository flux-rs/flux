use std::ops::ControlFlow;

use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_span::Symbol;
use toposort_scc::IndexGraph;

use super::{fold::TypeSuperFoldable, ESpan};
use crate::{
    fhir::SpecFuncKind,
    rty::{
        fold::{TypeFoldable, TypeFolder, TypeSuperVisitable, TypeVisitable, TypeVisitor},
        Binder, Expr, ExprKind, SpecFunc,
    },
};

#[derive(Default)]
pub struct SpecFuncDefns {
    defns: FxHashMap<Symbol, SpecFunc>,
}

pub(super) struct Normalizer<'a> {
    defs: &'a SpecFuncDefns,
}

impl SpecFuncDefns {
    pub fn new(defns: FxHashMap<Symbol, SpecFunc>) -> Result<Self, Vec<Symbol>> {
        let raw = SpecFuncDefns { defns };
        raw.normalize()
    }

    fn defn_deps(&self, expr: &Binder<Expr>) -> FxHashSet<Symbol> {
        struct DepsVisitor(FxHashSet<Symbol>);
        impl TypeVisitor for DepsVisitor {
            fn visit_expr(&mut self, expr: &Expr) -> ControlFlow<!> {
                if let ExprKind::App(func, _) = expr.kind()
                    && let ExprKind::GlobalFunc(sym, SpecFuncKind::Def) = func.kind()
                {
                    self.0.insert(*sym);
                }
                expr.super_visit_with(self)
            }
        }
        let mut visitor = DepsVisitor(FxHashSet::default());
        expr.visit_with(&mut visitor);
        visitor.0
    }

    /// Returns
    /// * either Ok(d1...dn) which are topologically sorted such that
    ///   forall i < j, di does not depend on i.e. "call" dj
    /// * or Err(d1...dn) where d1 'calls' d2 'calls' ... 'calls' dn 'calls' d1
    fn sorted_defns(&self) -> Result<Vec<Symbol>, Vec<Symbol>> {
        // 1. Make the Symbol-Index
        let mut i2s: Vec<Symbol> = Vec::new();
        let mut s2i: FxHashMap<Symbol, usize> = FxHashMap::default();
        for (i, s) in self.defns.keys().enumerate() {
            i2s.push(*s);
            s2i.insert(*s, i);
        }

        // 2. Make the dependency graph
        let mut adj_list: Vec<Vec<usize>> = vec![];
        for name in &i2s {
            let defn = self.defns.get(name).unwrap();
            let deps = self.defn_deps(&defn.expr);
            let ddeps = deps
                .iter()
                .filter_map(|s| s2i.get(s).copied())
                .collect_vec();
            adj_list.push(ddeps);
        }
        let mut g = IndexGraph::from_adjacency_list(&adj_list);
        g.transpose();

        // 3. Topologically sort the graph
        match g.toposort_or_scc() {
            Ok(is) => Ok(is.iter().map(|i| i2s[*i]).collect()),
            Err(mut scc) => {
                let cycle = scc.pop().unwrap();
                let mut names: Vec<Symbol> = cycle.iter().map(|i| i2s[*i]).collect();
                names.sort();
                Err(names)
            }
        }
    }

    // private function normalize (expand_defns) which does the SCC-expansion
    fn normalize(mut self) -> Result<Self, Vec<Symbol>> {
        // 1. Topologically sort the Defns
        let ds = self.sorted_defns()?;

        // 2. Expand each defn in the sorted order
        let mut exp_defns = SpecFuncDefns { defns: FxHashMap::default() };
        for d in ds {
            if let Some(defn) = self.defns.remove(&d) {
                let expr = defn.expr.normalize(&exp_defns);
                let exp_defn = SpecFunc { expr, ..defn };
                exp_defns.defns.insert(d, exp_defn);
            }
        }
        Ok(exp_defns)
    }

    fn func_defn(&self, f: &Symbol) -> Option<&SpecFunc> {
        self.defns.get(f)
    }
}

impl<'a> Normalizer<'a> {
    pub(super) fn new(defs: &'a SpecFuncDefns) -> Self {
        Self { defs }
    }

    fn at_base(expr: Expr, espan: Option<ESpan>) -> Expr {
        match espan {
            Some(espan) => BaseSpanner::new(espan).fold_expr(&expr),
            None => expr,
        }
    }

    fn app(&mut self, func: &Expr, args: &[Expr], espan: Option<ESpan>) -> Expr {
        match func.kind() {
            ExprKind::GlobalFunc(sym, SpecFuncKind::Def)
                if let Some(defn) = self.defs.func_defn(sym) =>
            {
                let res = defn.expr.replace_bound_refts(args);
                Self::at_base(res, espan)
            }
            ExprKind::Abs(lam) => {
                let res = lam.apply(args);
                Self::at_base(res, espan)
            }
            _ => ExprKind::App(func.clone(), args.into()).intern_at_opt(espan),
        }
    }
}

impl TypeFolder for Normalizer<'_> {
    fn fold_expr(&mut self, expr: &Expr) -> Expr {
        let expr = expr.super_fold_with(self);
        let span = expr.span();
        match expr.kind() {
            ExprKind::App(func, args) => self.app(func, args, span),
            ExprKind::FieldProj(e, proj) => e.proj_and_reduce(*proj),
            _ => expr,
        }
    }
}

struct BaseSpanner {
    espan: ESpan,
}

impl BaseSpanner {
    fn new(espan: ESpan) -> Self {
        Self { espan }
    }
}

impl TypeFolder for BaseSpanner {
    fn fold_expr(&mut self, expr: &Expr) -> Expr {
        expr.super_fold_with(self).at_base(Some(self.espan))
    }
}
