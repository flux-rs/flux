//! Expanding the expression alias `defn` in [`flux_middle::fhir`]
//! i.e. replacing {v:nat(v)} with {v:0<=v} in all the relevant signatures.
//! As this is done _after_ wf-checking, there should be no user-visible errors during expansion...

use rustc_hash::FxHashMap;
use rustc_span::Symbol;

use crate::fhir::{
    self, BaseTy, Constraint, Defn, Expr, ExprKind, FnSig, Func, Indices, Name, RefineArg, Ty,
};

pub fn expand_fhir_map(mut map: fhir::Map) -> fhir::Map {
    let mut exp_map = fhir::Map::default();

    // FnSigs
    for (def_id, fn_sig) in std::mem::take(&mut map.fns) {
        let exp_fn_sig = expand_fn_sig(&map.defns, fn_sig);
        exp_map.insert_fn_sig(def_id, exp_fn_sig)
    }

    return exp_map;
}
// ------------------------------------------------------------------------------------

// ------------------------------------------------------------------------------------
type Subst = FxHashMap<Name, Expr>;

fn subst_expr(subst: &Subst, e: &Expr) -> Expr {
    match &e.kind {
        ExprKind::Var(name, _sym, _span) => {
            if let Some(e) = subst.get(name) {
                e.clone()
            } else {
                panic!("subst_expr: unbound variable: {:?}", e);
            }
        }
        ExprKind::Const(_, _) | ExprKind::Literal(_) => e.clone(),
        ExprKind::BinaryOp(o, box [e1, e2]) => {
            let e1 = subst_expr(subst, &e1);
            let e2 = subst_expr(subst, &e2);
            let kind = ExprKind::BinaryOp(*o, Box::new([e1, e2]));
            Expr { kind, span: e.span }
        }
        ExprKind::App(f, args) => {
            let args = args.iter().map(|e| subst_expr(subst, e)).collect();
            let kind = ExprKind::App(f.clone(), args);
            Expr { kind, span: e.span }
        }
        ExprKind::IfThenElse(box [e1, e2, e3]) => {
            let e1 = subst_expr(subst, &e1);
            let e2 = subst_expr(subst, &e2);
            let e3 = subst_expr(subst, &e3);
            let kind = ExprKind::IfThenElse(Box::new([e1, e2, e3]));
            Expr { kind, span: e.span }
        }
    }
}

fn expand_defn(defn: &Defn, args: Vec<Expr>) -> ExprKind {
    let mut subst: Subst = FxHashMap::default();
    for (param, arg) in defn.args.iter().zip(args) {
        subst.insert(param.name.name, arg);
    }
    let exp_body = subst_expr(&subst, &defn.expr);
    exp_body.kind
}

fn expand_app(defns: &FxHashMap<Symbol, Defn>, f: Func, args: Vec<Expr>) -> ExprKind {
    let exp_args: Vec<Expr> = args
        .into_iter()
        .map(|arg| expand_expr(defns, arg))
        .collect();

    if let Func::Uif(uif, _) = f {
        if let Some(defn) = defns.get(&uif) {
            return expand_defn(defn, exp_args);
        }
    }
    return ExprKind::App(f, exp_args);
}

fn expand_expr(defns: &FxHashMap<Symbol, Defn>, expr: Expr) -> Expr {
    let kind = match expr.kind {
        fhir::ExprKind::App(f, args) => expand_app(defns, f, args),
        fhir::ExprKind::Const(_, _) | fhir::ExprKind::Var(_, _, _) | fhir::ExprKind::Literal(_) => {
            expr.kind
        }
        fhir::ExprKind::BinaryOp(op, box [e1, e2]) => {
            fhir::ExprKind::BinaryOp(op, Box::new([expand_expr(defns, e1), expand_expr(defns, e2)]))
        }
        fhir::ExprKind::IfThenElse(box [e1, e2, e3]) => {
            fhir::ExprKind::IfThenElse(Box::new([
                expand_expr(defns, e1),
                expand_expr(defns, e2),
                expand_expr(defns, e3),
            ]))
        }
    };
    Expr { kind, span: expr.span }
}

fn expand_bty(defns: &FxHashMap<Symbol, Defn>, bty: BaseTy) -> BaseTy {
    match bty {
        BaseTy::Adt(did, tys) => {
            BaseTy::Adt(did, tys.into_iter().map(|ty| expand_ty(defns, ty)).collect())
        }
        BaseTy::Int(_) | BaseTy::Uint(_) | BaseTy::Bool => bty,
    }
}

fn expand_refine_arg(defns: &FxHashMap<Symbol, Defn>, arg: RefineArg) -> RefineArg {
    match arg {
        RefineArg::Expr { expr, is_binder } => {
            RefineArg::Expr { expr: expand_expr(defns, expr), is_binder }
        }
        RefineArg::Abs(_, _, _) => arg,
    }
}

fn expand_indices(defns: &FxHashMap<Symbol, Defn>, idxs: Indices) -> Indices {
    let exp_indices = idxs
        .indices
        .into_iter()
        .map(|arg| expand_refine_arg(defns, arg))
        .collect();
    Indices { indices: exp_indices, span: idxs.span }
}

fn expand_ty(defns: &FxHashMap<Symbol, Defn>, ty: Ty) -> Ty {
    match ty {
        Ty::BaseTy(bty) => Ty::BaseTy(expand_bty(defns, bty)),
        Ty::Indexed(bty, idxs) => Ty::Indexed(expand_bty(defns, bty), expand_indices(defns, idxs)),
        Ty::Exists(bty, names, expr) => {
            Ty::Exists(expand_bty(defns, bty), names, expand_expr(defns, expr))
        }
        Ty::Constr(expr, box ty) => {
            Ty::Constr(expand_expr(defns, expr), Box::new(expand_ty(defns, ty)))
        }
        Ty::Ref(rk, box ty) => Ty::Ref(rk, Box::new(expand_ty(defns, ty))),
        Ty::Tuple(tys) => Ty::Tuple(tys.into_iter().map(|ty| expand_ty(defns, ty)).collect()),
        Ty::Array(box ty, n) => Ty::Array(Box::new(expand_ty(defns, ty)), n),
        Ty::Slice(box ty) => Ty::Slice(Box::new(expand_ty(defns, ty))),
        Ty::Float(_) | Ty::Str | Ty::Char | Ty::Ptr(_) | Ty::Param(_) | Ty::Never => ty,
    }
}

fn expand_constraint(
    defns: &FxHashMap<Symbol, fhir::Defn>,
    constr: fhir::Constraint,
) -> Constraint {
    match constr {
        Constraint::Type(x, ty) => Constraint::Type(x, expand_ty(defns, ty)),
        Constraint::Pred(p) => Constraint::Pred(expand_expr(defns, p)),
    }
}

fn expand_fn_sig(defns: &FxHashMap<Symbol, Defn>, fn_sig: FnSig) -> FnSig {
    let params = fn_sig.params;
    let requires: Vec<Constraint> = fn_sig
        .requires
        .into_iter()
        .map(|constr| expand_constraint(defns, constr))
        .collect();

    fhir::FnSig { params, requires, args: fn_sig.args, ret: fn_sig.ret, ensures: fn_sig.ensures }
}
