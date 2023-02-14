use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_span::Symbol;
use toposort_scc::IndexGraph;

use crate::rty::{
    fold::{TypeFoldable, TypeFolder, TypeVisitor},
    Binder, Defn, Expr, ExprKind,
};

#[derive(Default)]
pub struct Defns {
    defns: FxHashMap<Symbol, Defn>,
}

pub(super) struct Normalizer<'a> {
    defs: &'a Defns,
}

impl Defns {
    pub fn new(defns: FxHashMap<Symbol, Defn>) -> Result<Self, Vec<Symbol>> {
        let raw = Defns { defns };
        raw.normalize()
    }

    fn defn_deps(&self, expr: &Binder<Expr>) -> FxHashSet<Symbol> {
        struct DepsVisitor(FxHashSet<Symbol>);
        impl TypeVisitor for DepsVisitor {
            fn visit_expr(&mut self, expr: &Expr) {
                if let ExprKind::App(func, _) = expr.kind()
                    && let ExprKind::Func(sym) = func.kind()
                {
                    self.0.insert(*sym);
                }
                expr.super_visit_with(self);
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
        for name in i2s.iter() {
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
                Err(cycle.iter().map(|i| i2s[*i]).collect())
            }
        }
    }

    // private function normalize (expand_defns) which does the SCC-expansion
    fn normalize(mut self) -> Result<Self, Vec<Symbol>> {
        // 1. Topologically sort the Defns
        let ds = self.sorted_defns()?;

        // 2. Expand each defn in the sorted order
        let mut exp_defns = Defns { defns: FxHashMap::default() };
        for d in ds {
            if let Some(defn) = self.defns.remove(&d) {
                let expr = defn.expr.normalize(&exp_defns);
                let exp_defn = Defn { expr, ..defn };
                exp_defns.defns.insert(d, exp_defn);
            }
        }
        Ok(exp_defns)
    }

    fn func_defn(&self, f: &Symbol) -> Option<&Defn> {
        if let Some(defn) = self.defns.get(f) {
            return Some(defn);
        }
        None
    }
}

impl<'a> Normalizer<'a> {
    pub(super) fn new(defs: &'a Defns) -> Self {
        Self { defs }
    }

    fn app(&self, func: &Expr, args: &[Expr]) -> Expr {
        match func.kind() {
            ExprKind::Func(sym) if let Some(defn) = self.defs.func_defn(sym) => {
                defn.expr.replace_bvars(&Expr::tuple(args))
            }
            ExprKind::Abs(body) => body.replace_bvars(&Expr::tuple(args)),
            _ => Expr::app(func.clone(), args),
        }
    }

    fn tuple_proj(&self, tup: &Expr, proj: u32) -> Expr {
        if let ExprKind::Tuple(exprs) = tup.kind() {
            exprs[proj as usize].clone()
        } else {
            Expr::tuple_proj(tup, proj)
        }
    }
}

impl TypeFolder for Normalizer<'_> {
    fn fold_expr(&mut self, expr: &Expr) -> Expr {
        let expr = expr.super_fold_with(self);
        match expr.kind() {
            ExprKind::App(func, args) => self.app(func, args),
            ExprKind::TupleProj(tup, proj) => self.tuple_proj(tup, *proj),
            _ => expr,
        }
    }
}
