//! Expanding the expression alias `defn` in [`flux_middle::fhir`]
//! i.e. replacing {v:nat(v)} with {v:0<=v} in all the relevant signatures.
//! As this is done _after_ wf-checking, there should be no user-visible errors during expansion...

use std::{
    collections::{HashMap, HashSet},
    error::Error,
};

use flux_errors::FluxSession;
use rustc_errors::ErrorGuaranteed;
use rustc_hash::FxHashMap;
use rustc_span::Symbol;
use toposort_scc::IndexGraph;

use crate::fhir::{
    self, AdtDef, BaseTy, Constraint, Defn, EnumDef, Expr, ExprKind, FnSig, Func, Indices, Name,
    Qualifier, RefineArg, StructDef, Ty, VariantDef, VariantRet,
};

pub fn expand_fhir_map(
    sess: &FluxSession,
    mut map: fhir::Map,
) -> Result<fhir::Map, ErrorGuaranteed> {
    let mut exp_map = fhir::Map::default();

    // Shift the things without any expressions (hence need for expansion)
    exp_map.consts = std::mem::take(&mut map.consts);
    exp_map.assumes = std::mem::take(&mut map.assumes);

    // remove the uifs that correspond to defns
    exp_map.uifs = HashMap::default();
    for (name, uif) in std::mem::take(&mut map.uifs) {
        if !map.defns.contains_key(&name) {
            exp_map.uifs.insert(name, uif);
        }
    }

    // Expand all the definitions in the map
    exp_map.defns = expand_defns(sess, std::mem::take(&mut map.defns))?;

    // Qualifiers
    for qualifier in std::mem::take(&mut map.qualifiers) {
        exp_map.insert_qualifier(expand_qualifier(&exp_map.defns, qualifier));
    }

    // FnSigs
    for (def_id, fn_sig) in std::mem::take(&mut map.fns) {
        let exp_fn_sig = expand_fn_sig(&exp_map.defns, fn_sig);
        exp_map.insert_fn_sig(def_id, exp_fn_sig)
    }

    // AdtDefs
    for (def_id, adt_def) in std::mem::take(&mut map.adts) {
        let exp_adt_def = expand_adt_def(&exp_map.defns, adt_def);
        exp_map.insert_adt(def_id, exp_adt_def)
    }

    // Structs
    for (def_id, struct_def) in std::mem::take(&mut map.structs) {
        let exp_struct_def = expand_struct_def(&exp_map.defns, struct_def);
        exp_map.insert_struct(def_id, exp_struct_def)
    }

    // Enums
    for (def_id, enum_def) in std::mem::take(&mut map.enums) {
        let exp_enum_def = expand_enum_def(&exp_map.defns, enum_def);
        exp_map.insert_enum(def_id, exp_enum_def)
    }

    Ok(exp_map)
}

type Subst = FxHashMap<Name, Expr>;
type Defns = FxHashMap<Symbol, Defn>;

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

fn func_defn(defns: &Defns, f: Func) -> Option<&Defn> {
    if let Func::Uif(uif, _) = f {
        if let Some(defn) = defns.get(&uif) {
            return Some(defn);
        }
    }
    return None;
}

fn expand_app(defns: &Defns, f: Func, args: Vec<Expr>) -> ExprKind {
    let exp_args: Vec<Expr> = args
        .into_iter()
        .map(|arg| expand_expr(defns, arg))
        .collect();

    if let Some(defn) = func_defn(defns, f.clone()) {
        return expand_defn(defn, exp_args);
    }
    return ExprKind::App(f, exp_args);
}

fn expand_expr(defns: &Defns, expr: Expr) -> Expr {
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

fn expand_qualifier(defns: &Defns, qualifier: Qualifier) -> Qualifier {
    Qualifier {
        name: qualifier.name,
        args: qualifier.args,
        expr: expand_expr(defns, qualifier.expr),
    }
}

fn expand_bty(defns: &Defns, bty: BaseTy) -> BaseTy {
    match bty {
        BaseTy::Adt(did, tys) => {
            BaseTy::Adt(did, tys.into_iter().map(|ty| expand_ty(defns, ty)).collect())
        }
        BaseTy::Int(_) | BaseTy::Uint(_) | BaseTy::Bool => bty,
    }
}

fn expand_refine_arg(defns: &Defns, arg: RefineArg) -> RefineArg {
    match arg {
        RefineArg::Expr { expr, is_binder } => {
            RefineArg::Expr { expr: expand_expr(defns, expr), is_binder }
        }
        RefineArg::Abs(_, _, _) => arg,
    }
}

fn expand_indices(defns: &Defns, idxs: Indices) -> Indices {
    let exp_indices = idxs
        .indices
        .into_iter()
        .map(|arg| expand_refine_arg(defns, arg))
        .collect();
    Indices { indices: exp_indices, span: idxs.span }
}

fn expand_ty(defns: &Defns, ty: Ty) -> Ty {
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

fn expand_struct_def(defns: &Defns, struct_def: StructDef) -> StructDef {
    let exp_kind = match struct_def.kind {
        fhir::StructKind::Transparent { fields } => {
            let exp_fields = fields
                .into_iter()
                .map(|tyo| tyo.map(|t| expand_ty(defns, t)))
                .collect();
            fhir::StructKind::Transparent { fields: exp_fields }
        }
        fhir::StructKind::Opaque => struct_def.kind,
    };

    StructDef { def_id: struct_def.def_id, kind: exp_kind }
}

fn expand_variant_def(defns: &Defns, variant_def: VariantDef) -> VariantDef {
    let exp_fields = variant_def
        .fields
        .into_iter()
        .map(|ty| expand_ty(defns, ty))
        .collect();
    let exp_ret_bty = expand_bty(defns, variant_def.ret.bty);
    let exp_ret_idxs = expand_indices(defns, variant_def.ret.indices);
    let exp_ret = VariantRet { bty: exp_ret_bty, indices: exp_ret_idxs };
    VariantDef { params: variant_def.params, fields: exp_fields, ret: exp_ret }
}

fn expand_enum_def(defns: &Defns, enum_def: EnumDef) -> EnumDef {
    let exp_variants = enum_def
        .variants
        .into_iter()
        .map(|variant_def| expand_variant_def(defns, variant_def))
        .collect();

    EnumDef { def_id: enum_def.def_id, variants: exp_variants }
}

fn expand_adt_def(defns: &Defns, adt_def: AdtDef) -> AdtDef {
    let invariants = adt_def
        .invariants
        .into_iter()
        .map(|inv| expand_expr(defns, inv))
        .collect();
    AdtDef { invariants, ..adt_def }
}

fn expand_fn_sig(defns: &Defns, fn_sig: FnSig) -> FnSig {
    let params = fn_sig.params;
    let requires: Vec<Constraint> = fn_sig
        .requires
        .into_iter()
        .map(|constr| expand_constraint(defns, constr))
        .collect();
    let args = fn_sig
        .args
        .into_iter()
        .map(|arg| expand_ty(defns, arg))
        .collect();
    let ret = expand_ty(defns, fn_sig.ret);
    let ensures = fn_sig
        .ensures
        .into_iter()
        .map(|constr| expand_constraint(defns, constr))
        .collect();
    fhir::FnSig { params, requires, args, ret, ensures }
}

// ---------------------------------------------------------------------------------------

fn defn_deps(defns: &Defns, expr: &Expr, res: &mut HashSet<Symbol>) {
    match &expr.kind {
        ExprKind::Const(_, _) | ExprKind::Var(_, _, _) | ExprKind::Literal(_) => (),
        ExprKind::BinaryOp(_, box [e1, e2]) => {
            defn_deps(defns, &e1, res);
            defn_deps(defns, &e2, res);
        }
        ExprKind::IfThenElse(box [e1, e2, e3]) => {
            defn_deps(defns, &e1, res);
            defn_deps(defns, &e2, res);
            defn_deps(defns, &e3, res);
        }
        ExprKind::App(f, es) => {
            if let Some(defn) = func_defn(defns, f.clone()) {
                res.insert(defn.name);
            }
            es.iter().for_each(|e| defn_deps(defns, e, res));
        }
    }
}
/// Returns
/// * either Ok(d1...dn) which are topologically sorted such that
///   forall i < j, di does not depend on i.e. "call" dj
/// * or Err(d1...dn) where d1 'calls' d2 'calls' ... 'calls' dn 'calls' d1

fn sorted_defns(defns: &Defns) -> Result<Vec<Symbol>, Vec<Symbol>> {
    // 1. Make the Symbol-Index
    let mut i2s: Vec<Symbol> = Vec::new();
    let mut s2i: FxHashMap<Symbol, usize> = FxHashMap::default();
    for (i, s) in defns.keys().enumerate() {
        i2s.push(*s);
        s2i.insert(*s, i);
    }

    // 2. Make the dependency graph
    let mut adj_list: Vec<Vec<usize>> = vec![];
    for name in i2s.iter() {
        let defn = defns.get(&name).unwrap();
        let mut deps = HashSet::default();
        defn_deps(defns, &defn.expr, &mut deps);
        adj_list.push(deps.iter().map(|s| *s2i.get(s).unwrap()).collect());
    }
    let mut g = IndexGraph::from_adjacency_list(&adj_list);
    g.transpose();
    // println!("TRACE: i2s = {:?}, adj_list = {:?}", i2s, adj_list);

    // 3. Topologically sort the graph
    match g.toposort_or_scc() {
        Ok(is) => {
            // println!("TRACE: topo-sort {:?}", is);
            Ok(is.iter().map(|i| i2s[*i]).collect())
        }
        Err(mut scc) => {
            let cycle = scc.pop().unwrap();
            Err(cycle.iter().map(|i| i2s[*i]).collect())
        }
    }
}

fn expand_defns(sess: &FluxSession, mut defns: Defns) -> Result<Defns, ErrorGuaranteed> {
    // 1. Topo-Sort the Defns
    let ds = match sorted_defns(&defns) {
        Ok(ds) => ds,
        Err(cs) => panic!("Alias defn cycle {:?}", cs),
    };

    // 2. Expand each defn in the sorted order
    let mut exp_defns = FxHashMap::default();
    for d in ds {
        let defn = defns.remove(&d).unwrap();
        let expr = expand_expr(&exp_defns, defn.expr);
        let exp_defn = Defn { expr, ..defn };
        // println!("TRACE: exp_defn {:?}", exp_defn);
        exp_defns.insert(d, exp_defn);
    }
    Ok(exp_defns)
}
