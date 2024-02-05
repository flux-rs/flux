use super::{
    AliasPred, BaseTy, BaseTyKind, Constraint, EnumDef, Expr, ExprKind, FieldDef, FnOutput, FnSig,
    FuncSort, GenericArg, Generics, Ident, Lifetime, Lit, PolyFuncSort, Pred, PredKind, QPath,
    RefineArg, RefineArgKind, RefineParam, Sort, StructDef, Ty, TyKind, TypeBinding, VariantDef,
    VariantRet,
};

#[macro_export]
macro_rules! walk_list {
    ($visitor: expr, $method: ident, $list: expr $(, $($extra_args: expr),* )?) => {
        {
            #[allow(for_loops_over_fallibles)]
            for elem in $list {
                $visitor.$method(elem $(, $($extra_args,)* )?)
            }
        }
    }
}

pub trait Visitor: Sized {
    fn visit_generics(&mut self, generics: &Generics) {
        walk_generics(self, generics);
    }

    fn visit_struct_def(&mut self, struct_def: &StructDef) {
        walk_struct_def(self, struct_def);
    }

    fn visit_enum_def(&mut self, enum_def: &EnumDef) {
        walk_enum_def(self, enum_def);
    }

    fn visit_variant(&mut self, variant: &VariantDef) {
        walk_variant(self, variant);
    }

    fn visit_field_def(&mut self, field: &FieldDef) {
        walk_field_def(self, field);
    }

    fn visit_variant_ret(&mut self, ret: &VariantRet) {
        walk_variant_ret(self, ret);
    }

    fn visit_fn_sig(&mut self, sig: &FnSig) {
        walk_fn_sig(self, sig);
    }

    fn visit_refine_param(&mut self, param: &RefineParam) {
        walk_refine_param(self, param);
    }

    fn visit_constraint(&mut self, constraint: &Constraint) {
        walk_constraint(self, constraint);
    }

    fn visit_fn_output(&mut self, output: &FnOutput) {
        walk_fn_output(self, output);
    }

    fn visit_generic_arg(&mut self, arg: &GenericArg) {
        walk_generic_arg(self, arg);
    }

    fn visit_lifetime(&mut self, _lft: &Lifetime) {}

    fn visit_ty(&mut self, ty: &Ty) {
        walk_ty(self, ty);
    }

    fn visit_bty(&mut self, bty: &BaseTy) {
        walk_bty(self, bty);
    }

    fn visit_qpath(&mut self, qpath: &QPath) {
        walk_qpath(self, qpath);
    }

    fn visit_type_binding(&mut self, binding: &TypeBinding) {
        walk_type_binding(self, binding);
    }

    fn visit_sort(&mut self, sort: &Sort) {
        walk_sort(self, sort);
    }

    fn visit_poly_func_sort(&mut self, func: &PolyFuncSort) {
        walk_poly_func_sort(self, func);
    }

    fn visit_func_sort(&mut self, func: &FuncSort) {
        walk_func_sort(self, func);
    }

    fn visit_refine_arg(&mut self, arg: &RefineArg) {
        walk_refine_arg(self, arg);
    }

    fn visit_expr(&mut self, expr: &Expr) {
        walk_expr(self, expr);
    }

    fn visit_pred(&mut self, pred: &Pred) {
        walk_pred(self, pred);
    }

    fn visit_alias_pred(&mut self, alias_pred: &AliasPred) {
        walk_alias_pred(self, alias_pred);
    }

    fn visit_literal(&mut self, _lit: &Lit) {}

    fn visit_ident(&mut self, _ident: Ident) {}
}

pub fn walk_struct_def<V: Visitor>(vis: &mut V, struct_def: &StructDef) {
    walk_list!(vis, visit_refine_param, struct_def.params);
    walk_list!(vis, visit_expr, struct_def.invariants);
}

pub fn walk_enum_def<V: Visitor>(vis: &mut V, enum_def: &EnumDef) {
    walk_list!(vis, visit_refine_param, enum_def.params);
    walk_list!(vis, visit_variant, enum_def.variants);
    walk_list!(vis, visit_expr, enum_def.invariants);
}

pub fn walk_variant<V: Visitor>(vis: &mut V, variant: &VariantDef) {
    walk_list!(vis, visit_refine_param, variant.params);
    walk_list!(vis, visit_field_def, variant.fields);
    vis.visit_variant_ret(&variant.ret);
}

pub fn walk_field_def<V: Visitor>(vis: &mut V, field: &FieldDef) {
    let FieldDef { def_id: _, ty, lifted: _ } = field;
    vis.visit_ty(ty);
}

pub fn walk_variant_ret<V: Visitor>(vis: &mut V, ret: &VariantRet) {
    let VariantRet { bty, idx } = ret;
    vis.visit_bty(bty);
    vis.visit_refine_arg(idx);
}

pub fn walk_generics<V: Visitor>(vis: &mut V, generics: &Generics) {
    walk_list!(vis, visit_refine_param, generics.refinement_params);
}

pub fn walk_fn_sig<V: Visitor>(vis: &mut V, sig: &FnSig) {
    walk_list!(vis, visit_constraint, sig.requires);
    walk_list!(vis, visit_ty, sig.args);
    vis.visit_fn_output(&sig.output);
}

pub fn walk_refine_param<V: Visitor>(vis: &mut V, param: &RefineParam) {
    let RefineParam { ident, sort, kind: _, fhir_id: _ } = param;
    vis.visit_ident(*ident);
    vis.visit_sort(sort);
}

pub fn walk_constraint<V: Visitor>(vis: &mut V, constraint: &Constraint) {
    match constraint {
        Constraint::Type(loc, ty, _) => {
            vis.visit_ident(*loc);
            vis.visit_ty(ty);
        }
        Constraint::Pred(p) => vis.visit_expr(p),
    }
}

pub fn walk_fn_output<V: Visitor>(vis: &mut V, output: &FnOutput) {
    walk_list!(vis, visit_refine_param, output.params);
    vis.visit_ty(&output.ret);
    walk_list!(vis, visit_constraint, output.ensures);
}

pub fn walk_generic_arg<V: Visitor>(vis: &mut V, arg: &GenericArg) {
    match arg {
        GenericArg::Lifetime(lft) => vis.visit_lifetime(lft),
        GenericArg::Type(ty) => vis.visit_ty(ty),
    }
}

pub fn walk_ty<V: Visitor>(vis: &mut V, ty: &Ty) {
    match ty.kind {
        TyKind::BaseTy(bty) => vis.visit_bty(&bty),
        TyKind::Indexed(bty, idx) => {
            vis.visit_bty(&bty);
            vis.visit_refine_arg(&idx);
        }
        TyKind::Exists(params, ty) => {
            walk_list!(vis, visit_refine_param, params);
            vis.visit_ty(ty);
        }
        TyKind::Constr(pred, ty) => {
            vis.visit_pred(&pred);
            vis.visit_ty(ty);
        }
        TyKind::Ptr(lft, loc) => {
            vis.visit_lifetime(&lft);
            vis.visit_ident(loc);
        }
        TyKind::Ref(lft, mty) => {
            vis.visit_lifetime(&lft);
            vis.visit_ty(mty.ty);
        }
        TyKind::Tuple(tys) => {
            walk_list!(vis, visit_ty, tys);
        }
        TyKind::Array(ty, _len) => {
            vis.visit_ty(ty);
        }
        TyKind::RawPtr(ty, _mtblt) => {
            vis.visit_ty(ty);
        }
        TyKind::OpaqueDef(_item_id, generics, refine, _bool) => {
            walk_list!(vis, visit_generic_arg, generics);
            walk_list!(vis, visit_refine_arg, refine);
        }
        TyKind::Never => {}
        TyKind::Hole(_) => {}
    }
}

pub fn walk_bty<V: Visitor>(vis: &mut V, bty: &BaseTy) {
    match &bty.kind {
        BaseTyKind::Path(path) => vis.visit_qpath(path),
        BaseTyKind::Slice(ty) => vis.visit_ty(ty),
    }
}

pub fn walk_qpath<V: Visitor>(vis: &mut V, qpath: &QPath) {
    match qpath {
        QPath::Resolved(self_ty, path) => {
            if let Some(self_ty) = self_ty {
                vis.visit_ty(self_ty);
            }
            walk_list!(vis, visit_generic_arg, path.args);
            walk_list!(vis, visit_type_binding, path.bindings);
            walk_list!(vis, visit_refine_arg, path.refine);
        }
    }
}

pub fn walk_type_binding<V: Visitor>(vis: &mut V, binding: &TypeBinding) {
    let TypeBinding { ident: _, term } = binding;
    vis.visit_ty(term);
}

pub fn walk_sort<V: Visitor>(vis: &mut V, sort: &Sort) {
    match sort {
        Sort::App(_ctor, args) => {
            walk_list!(vis, visit_sort, *args);
        }
        Sort::Func(fun) => vis.visit_poly_func_sort(fun),
        Sort::BitVec(_)
        | Sort::Int
        | Sort::Param(_)
        | Sort::SelfParam { .. }
        | Sort::SelfAlias { .. }
        | Sort::Var(_)
        | Sort::Bool
        | Sort::Real
        | Sort::Loc
        | Sort::Infer => {}
    }
}

pub fn walk_poly_func_sort<V: Visitor>(vis: &mut V, func: &PolyFuncSort) {
    let PolyFuncSort { params: _, fsort } = func;
    vis.visit_func_sort(fsort);
}

pub fn walk_func_sort<V: Visitor>(vis: &mut V, func: &FuncSort) {
    walk_list!(vis, visit_sort, func.inputs_and_output);
}

pub fn walk_refine_arg<V: Visitor>(vis: &mut V, arg: &RefineArg) {
    match arg.kind {
        RefineArgKind::Expr(expr) => vis.visit_expr(&expr),
        RefineArgKind::Abs(params, body) => {
            walk_list!(vis, visit_refine_param, params);
            vis.visit_expr(&body);
        }
        RefineArgKind::Record(flds) => {
            walk_list!(vis, visit_refine_arg, flds);
        }
    }
}

pub fn walk_alias_pred<V: Visitor>(vis: &mut V, alias_pred: &AliasPred) {
    walk_list!(vis, visit_generic_arg, alias_pred.generic_args);
}

pub fn walk_pred<V: Visitor>(vis: &mut V, pred: &Pred) {
    match pred.kind {
        PredKind::Expr(expr) => vis.visit_expr(&expr),
        PredKind::Alias(alias_pred, refine_args) => {
            vis.visit_alias_pred(&alias_pred);
            walk_list!(vis, visit_refine_arg, refine_args);
        }
    }
}

pub fn walk_expr<V: Visitor>(vis: &mut V, expr: &Expr) {
    match expr.kind {
        ExprKind::Const(_def_id, _span) => {}
        ExprKind::Var(var, _) => vis.visit_ident(var),
        ExprKind::Dot(base, _fld) => {
            vis.visit_ident(base);
        }
        ExprKind::Literal(lit) => vis.visit_literal(&lit),
        ExprKind::BinaryOp(_op, e1, e2) => {
            vis.visit_expr(e1);
            vis.visit_expr(e2);
        }
        ExprKind::UnaryOp(_op, e) => vis.visit_expr(e),
        ExprKind::App(_func, args) => {
            walk_list!(vis, visit_expr, args);
        }
        ExprKind::IfThenElse(e1, e2, e3) => {
            vis.visit_expr(e1);
            vis.visit_expr(e2);
            vis.visit_expr(e3);
        }
    }
}
