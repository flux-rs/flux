//! Collects the opaque sorts mentioned anywhere in a [`Task`].
use rustc_data_structures::fx::FxIndexSet;

use crate::{
    Bind, ConstDecl, Constraint, DataDecl, Expr, FunDef, KVarDecl, Pred, Qualifier, Sort, SortCtor,
    Task, Types, WKVar,
};

pub(crate) type Acc<T> = FxIndexSet<<T as Types>::Opaque>;

fn sort<T: Types>(s: &Sort<T>, acc: &mut Acc<T>) {
    match s {
        Sort::Opaque(o) => {
            acc.insert(o.clone());
        }
        Sort::BitVec(s) | Sort::Abs(_, s) => sort(s, acc),
        Sort::Func(s) => s.iter().for_each(|s| sort(s, acc)),
        Sort::App(ctor, args) => {
            match ctor {
                SortCtor::Set | SortCtor::Map | SortCtor::Data(_) => {}
            }
            args.iter().for_each(|s| sort(s, acc));
        }
        Sort::Int | Sort::Bool | Sort::Real | Sort::Str | Sort::BvSize(_) | Sort::Var(_) => {}
    }
}

fn exprs<T: Types>(es: &[Expr<T>], acc: &mut Acc<T>) {
    es.iter().for_each(|e| expr(e, acc));
}

fn expr<T: Types>(e: &Expr<T>, acc: &mut Acc<T>) {
    match e {
        Expr::Constant(_) | Expr::Var(_) | Expr::ThyFunc(_) => {}
        Expr::App(head, sort_args, args, out_sort) => {
            expr(head, acc);
            exprs(args, acc);
            sort_args
                .iter()
                .flatten()
                .chain(out_sort)
                .for_each(|s| sort(s, acc));
        }
        Expr::Neg(e) | Expr::Not(e) | Expr::IsCtor(_, e) => expr(e, acc),
        Expr::BinaryOp(_, es)
        | Expr::Imp(es)
        | Expr::Iff(es)
        | Expr::Atom(_, es)
        | Expr::Let(_, es) => exprs(&**es, acc),
        Expr::IfThenElse(es) => exprs(&**es, acc),
        Expr::And(es) | Expr::Or(es) => exprs(es, acc),
        Expr::Quantifier(_, binders, e) => {
            binders.iter().for_each(|(_, s)| sort(s, acc));
            expr(e, acc);
        }
        Expr::WKVar(WKVar { args, .. }) => exprs(args, acc),
    }
}

fn pred<T: Types>(p: &Pred<T>, acc: &mut Acc<T>) {
    match p {
        Pred::KVar(_, args) => exprs(args, acc),
        Pred::Expr(e) => expr(e, acc),
    }
}

fn bind<T: Types>(b: &Bind<T>, acc: &mut Acc<T>) {
    sort(&b.sort, acc);
    b.preds.iter().for_each(|p| pred(p, acc));
}

impl<T: Types> Constraint<T> {
    pub fn collect_opaque_sorts(&self, acc: &mut FxIndexSet<T::Opaque>) {
        match self {
            Constraint::Pred(p, _) => pred(p, acc),
            Constraint::Conj(cs) => cs.iter().for_each(|c| c.collect_opaque_sorts(acc)),
            Constraint::ForAll(b, c) => {
                bind(b, acc);
                c.collect_opaque_sorts(acc);
            }
        }
    }
}

impl<T: Types> Task<T> {
    /// Opaque sorts mentioned anywhere in the task, in order of first occurrence.
    pub fn collect_opaque_sorts(&self) -> FxIndexSet<T::Opaque> {
        let mut acc = FxIndexSet::default();
        for ConstDecl { sort: s, .. } in &self.constants {
            sort(s, &mut acc);
        }
        for DataDecl { ctors, .. } in &self.data_decls {
            for field in ctors.iter().flat_map(|c| &c.fields) {
                sort(&field.sort, &mut acc);
            }
        }
        for FunDef { sort: fsort, body, .. } in &self.define_funs {
            fsort.inputs.iter().for_each(|s| sort(s, &mut acc));
            sort(&fsort.output, &mut acc);
            if let Some(body) = body {
                expr(&body.expr, &mut acc);
            }
        }
        for KVarDecl { sorts, .. } in &self.kvars {
            sorts.iter().for_each(|s| sort(s, &mut acc));
        }
        self.constraint.collect_opaque_sorts(&mut acc);
        for Qualifier { args, body, .. } in &self.qualifiers {
            args.iter().for_each(|a| sort(&a.sort, &mut acc));
            expr(body, &mut acc);
        }
        acc
    }
}
