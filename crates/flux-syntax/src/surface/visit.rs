//! A visitor for types in [`surface`]
//!
//! In general there's no specific order except that [refinement parameters] should be
//! visited in an order that matches their scope. Name resolution relies on this gurantee.
//!
//! [`surface`]: crate::surface
//! [refinement parameters]: crate::surface::RefineParam
use rustc_span::symbol::Ident;

use super::{
    Async, BaseSort, BaseTy, BaseTyKind, ConstArg, ConstantInfo, ConstructorArg, Ensures, EnumDef,
    Expr, ExprKind, ExprPath, ExprPathSegment, FieldExpr, FnInput, FnOutput, FnRetTy, FnSig,
    GenericArg, GenericArgKind, GenericParam, Generics, Impl, ImplAssocReft, Indices, ItemKind,
    Lit, Path, PathSegment, Qualifier, RefineArg, RefineParam, Sort, SortPath, SpecFunc, StructDef,
    Trait, TraitAssocReft, TraitRef, Ty, TyAlias, TyKind, VariantDef, VariantRet,
    WhereBoundPredicate,
};
use crate::surface::{FluxItem, ImplItemFn, Item, PrimOpProp, SortDecl, TraitItemFn};

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
    fn visit_flux_item(&mut self, item: &FluxItem) {
        walk_flux_item(self, item);
    }

    fn visit_qualifier(&mut self, qualifier: &Qualifier) {
        walk_qualifier(self, qualifier);
    }

    fn visit_sort_decl(&mut self, sort_decl: &SortDecl) {
        walk_sort_decl(self, sort_decl);
    }

    fn visit_defn(&mut self, defn: &SpecFunc) {
        walk_defn(self, defn);
    }

    fn visit_primop_prop(&mut self, prop: &PrimOpProp) {
        walk_primop_prop(self, prop);
    }

    fn visit_refine_param(&mut self, param: &RefineParam) {
        walk_refine_param(self, param);
    }

    fn visit_generic_param(&mut self, param: &GenericParam) {
        walk_generic_param(self, param);
    }

    fn visit_sort(&mut self, sort: &Sort) {
        walk_sort(self, sort);
    }

    fn visit_item(&mut self, item: &Item) {
        walk_item(self, item);
    }

    fn visit_trait_item(&mut self, item: &TraitItemFn) {
        walk_trait_item(self, item);
    }

    fn visit_impl_item(&mut self, item: &ImplItemFn) {
        walk_impl_item(self, item);
    }

    fn visit_trait(&mut self, trait_: &Trait) {
        walk_trait(self, trait_);
    }

    fn visit_trait_assoc_reft(&mut self, assoc_reft: &TraitAssocReft) {
        walk_trait_assoc_reft(self, assoc_reft);
    }

    fn visit_impl(&mut self, impl_: &Impl) {
        walk_impl(self, impl_);
    }

    fn visit_impl_assoc_reft(&mut self, assoc_reft: &ImplAssocReft) {
        walk_impl_assoc_reft(self, assoc_reft);
    }

    fn visit_trait_ref(&mut self, trait_ref: &TraitRef) {
        walk_trait_ref(self, trait_ref);
    }

    fn visit_base_sort(&mut self, bsort: &BaseSort) {
        walk_base_sort(self, bsort);
    }

    fn visit_sort_path(&mut self, path: &SortPath) {
        walk_sort_path(self, path);
    }

    fn visit_ty_alias(&mut self, ty_alias: &TyAlias) {
        walk_ty_alias(self, ty_alias);
    }

    fn visit_struct_def(&mut self, struct_def: &StructDef) {
        walk_struct_def(self, struct_def);
    }

    fn visit_constant(&mut self, _constant: &ConstantInfo) {
        walk_constant(self, _constant);
    }

    fn visit_enum_def(&mut self, enum_def: &EnumDef) {
        walk_enum_def(self, enum_def);
    }

    fn visit_variant(&mut self, variant: &VariantDef) {
        walk_variant(self, variant);
    }

    fn visit_variant_ret(&mut self, ret: &VariantRet) {
        walk_variant_ret(self, ret);
    }

    fn visit_fn_sig(&mut self, fn_sig: &FnSig) {
        walk_fn_sig(self, fn_sig);
    }

    fn visit_fn_output(&mut self, fn_output: &FnOutput) {
        walk_fn_output(self, fn_output);
    }

    fn visit_async(&mut self, _asyncness: &Async) {}

    fn visit_generics(&mut self, generics: &Generics) {
        walk_generics(self, generics);
    }

    fn visit_fn_input(&mut self, input: &FnInput) {
        walk_fn_input(self, input);
    }

    fn visit_fn_ret_ty(&mut self, fn_ret_ty: &FnRetTy) {
        walk_fn_ret_ty(self, fn_ret_ty);
    }

    fn visit_ensures(&mut self, ensures: &Ensures) {
        walk_ensures(self, ensures);
    }

    fn visit_where_predicate(&mut self, predicate: &WhereBoundPredicate) {
        walk_where_predicate(self, predicate);
    }

    fn visit_generic_arg(&mut self, arg: &GenericArg) {
        walk_generic_arg(self, arg);
    }

    fn visit_refine_arg(&mut self, arg: &RefineArg) {
        walk_refine_arg(self, arg);
    }

    fn visit_indices(&mut self, indices: &Indices) {
        walk_indices(self, indices);
    }

    fn visit_ty(&mut self, ty: &Ty) {
        walk_ty(self, ty);
    }

    fn visit_const_arg(&mut self, _const_arg: &ConstArg) {}

    fn visit_bty(&mut self, bty: &BaseTy) {
        walk_bty(self, bty);
    }

    fn visit_path(&mut self, path: &Path) {
        walk_path(self, path);
    }

    fn visit_path_segment(&mut self, segment: &PathSegment) {
        walk_path_segment(self, segment);
    }

    fn visit_expr(&mut self, expr: &Expr) {
        walk_expr(self, expr);
    }

    fn visit_constructor_args(&mut self, expr: &ConstructorArg) {
        match expr {
            ConstructorArg::FieldExpr(field_expr) => walk_field_expr(self, field_expr),
            ConstructorArg::Spread(spread) => self.visit_expr(&spread.expr),
        }
    }

    fn visit_path_expr(&mut self, qpath: &ExprPath) {
        walk_path_expr(self, qpath);
    }

    fn visit_path_expr_segment(&mut self, segment: &ExprPathSegment) {
        walk_path_expr_segment(self, segment);
    }

    fn visit_ident(&mut self, _ident: Ident) {}

    fn visit_literal(&mut self, _lit: Lit) {}
}

pub fn walk_flux_item<V: Visitor>(vis: &mut V, item: &FluxItem) {
    match item {
        FluxItem::Qualifier(qualifier) => vis.visit_qualifier(qualifier),
        FluxItem::FuncDef(spec_func) => vis.visit_defn(spec_func),
        FluxItem::SortDecl(sort_decl) => vis.visit_sort_decl(sort_decl),
        FluxItem::PrimOpProp(prim_op_prop) => vis.visit_primop_prop(prim_op_prop),
    }
}

pub fn walk_qualifier<V: Visitor>(vis: &mut V, qualifier: &Qualifier) {
    vis.visit_ident(qualifier.name);
    walk_list!(vis, visit_refine_param, &qualifier.params);
    vis.visit_expr(&qualifier.expr);
}

pub fn walk_sort_decl<V: Visitor>(vis: &mut V, sort_decl: &SortDecl) {
    vis.visit_ident(sort_decl.name);
    walk_list!(vis, visit_ident, sort_decl.sort_vars.iter().copied());
}

pub fn walk_defn<V: Visitor>(vis: &mut V, defn: &SpecFunc) {
    vis.visit_ident(defn.name);
    walk_list!(vis, visit_ident, defn.sort_vars.iter().copied());
    walk_list!(vis, visit_refine_param, &defn.params);
    vis.visit_sort(&defn.output);
    if let Some(body) = &defn.body {
        vis.visit_expr(body);
    }
}

pub fn walk_primop_prop<V: Visitor>(vis: &mut V, prop: &PrimOpProp) {
    vis.visit_ident(prop.name);
    walk_list!(vis, visit_refine_param, &prop.params);
    vis.visit_expr(&prop.body);
}

pub fn walk_refine_param<V: Visitor>(vis: &mut V, param: &RefineParam) {
    vis.visit_ident(param.ident);
    vis.visit_sort(&param.sort);
}

pub fn walk_generic_param<V: Visitor>(vis: &mut V, param: &GenericParam) {
    vis.visit_ident(param.name);
}

pub fn walk_sort<V: Visitor>(vis: &mut V, sort: &Sort) {
    match sort {
        Sort::Base(bsort) => vis.visit_base_sort(bsort),
        Sort::Func { inputs, output } => {
            walk_list!(vis, visit_base_sort, inputs);
            vis.visit_base_sort(output);
        }
        Sort::Infer => {}
    }
}

pub fn walk_item<V: Visitor>(vis: &mut V, item: &Item) {
    match &item.kind {
        ItemKind::Fn(fn_sig) => {
            if let Some(fn_sig) = fn_sig {
                vis.visit_fn_sig(fn_sig);
            }
        }
        ItemKind::Struct(struct_def) => vis.visit_struct_def(struct_def),
        ItemKind::Enum(enum_def) => vis.visit_enum_def(enum_def),
        ItemKind::Trait(trait_) => vis.visit_trait(trait_),
        ItemKind::Impl(impl_) => vis.visit_impl(impl_),
        ItemKind::Const(cst) => vis.visit_constant(cst),
        ItemKind::TyAlias(ty_alias) => vis.visit_ty_alias(ty_alias),
        ItemKind::Mod => {}
    }
}

pub fn walk_trait_item<V: Visitor>(vis: &mut V, item: &TraitItemFn) {
    if let Some(fn_sig) = item.sig.as_ref() {
        vis.visit_fn_sig(fn_sig);
    }
}

pub fn walk_impl_item<V: Visitor>(vis: &mut V, item: &ImplItemFn) {
    if let Some(fn_sig) = item.sig.as_ref() {
        vis.visit_fn_sig(fn_sig);
    }
}

pub fn walk_trait<V: Visitor>(vis: &mut V, trait_: &Trait) {
    if let Some(generics) = &trait_.generics {
        vis.visit_generics(generics);
    }
    walk_list!(vis, visit_trait_assoc_reft, &trait_.assoc_refinements);
}

pub fn walk_trait_assoc_reft<V: Visitor>(vis: &mut V, assoc_reft: &TraitAssocReft) {
    vis.visit_ident(assoc_reft.name);
    walk_list!(vis, visit_refine_param, &assoc_reft.params);
    vis.visit_base_sort(&assoc_reft.output);
    if let Some(expr) = &assoc_reft.body {
        vis.visit_expr(expr);
    }
}

pub fn walk_impl<V: Visitor>(vis: &mut V, impl_: &Impl) {
    if let Some(generics) = &impl_.generics {
        vis.visit_generics(generics);
    }
    walk_list!(vis, visit_impl_assoc_reft, &impl_.assoc_refinements);
}

pub fn walk_impl_assoc_reft<V: Visitor>(vis: &mut V, assoc_reft: &ImplAssocReft) {
    vis.visit_ident(assoc_reft.name);
    walk_list!(vis, visit_refine_param, &assoc_reft.params);
    vis.visit_expr(&assoc_reft.body);
    vis.visit_base_sort(&assoc_reft.output);
}

pub fn walk_trait_ref<V: Visitor>(vis: &mut V, trait_ref: &TraitRef) {
    vis.visit_path(&trait_ref.path);
}

pub fn walk_base_sort<V: Visitor>(vis: &mut V, bsort: &BaseSort) {
    match bsort {
        BaseSort::BitVec(_len) => {}
        BaseSort::Path(path) => vis.visit_sort_path(path),
        BaseSort::SortOf(qself, path) => {
            vis.visit_ty(qself);
            vis.visit_path(path);
        }
    }
}

pub fn walk_sort_path<V: Visitor>(vis: &mut V, path: &SortPath) {
    walk_list!(vis, visit_ident, path.segments.iter().copied());
    walk_list!(vis, visit_base_sort, &path.args);
}

pub fn walk_ty_alias<V: Visitor>(vis: &mut V, ty_alias: &TyAlias) {
    vis.visit_ident(ty_alias.ident);
    vis.visit_generics(&ty_alias.generics);
    walk_list!(vis, visit_refine_param, &ty_alias.params);
    if let Some(index) = &ty_alias.index {
        vis.visit_refine_param(index);
    }
    vis.visit_ty(&ty_alias.ty);
}
pub fn walk_constant<V: Visitor>(vis: &mut V, constant_info: &ConstantInfo) {
    if let Some(expr) = &constant_info.expr {
        vis.visit_expr(expr);
    }
}

pub fn walk_struct_def<V: Visitor>(vis: &mut V, struct_def: &StructDef) {
    if let Some(generics) = &struct_def.generics {
        vis.visit_generics(generics);
    }
    if let Some(refined_by) = &struct_def.refined_by {
        walk_list!(vis, visit_refine_param, refined_by);
    }
    walk_list!(vis, visit_expr, &struct_def.invariants);
    struct_def.fields.iter().flatten().for_each(|field| {
        vis.visit_ty(field);
    });
}

pub fn walk_enum_def<V: Visitor>(vis: &mut V, enum_def: &EnumDef) {
    if let Some(refined_by) = &enum_def.refined_by {
        walk_list!(vis, visit_refine_param, refined_by);
    }
    walk_list!(vis, visit_expr, &enum_def.invariants);
    enum_def
        .variants
        .iter()
        .flatten()
        .for_each(|variant| vis.visit_variant(variant));
}

pub fn walk_variant<V: Visitor>(vis: &mut V, variant: &VariantDef) {
    walk_list!(vis, visit_ty, &variant.fields);
    if let Some(ret) = &variant.ret {
        vis.visit_variant_ret(ret);
    }
}

pub fn walk_fn_trait_ref<V: Visitor>(vis: &mut V, in_arg: &GenericArg, out_arg: &GenericArg) {
    vis.visit_generic_arg(in_arg);
    vis.visit_generic_arg(out_arg);
}

pub fn walk_variant_ret<V: Visitor>(vis: &mut V, ret: &VariantRet) {
    vis.visit_path(&ret.path);
    vis.visit_indices(&ret.indices);
}

pub fn walk_fn_sig<V: Visitor>(vis: &mut V, fn_sig: &FnSig) {
    vis.visit_async(&fn_sig.asyncness);
    vis.visit_generics(&fn_sig.generics);
    walk_list!(vis, visit_refine_param, &fn_sig.params);
    for requires in &fn_sig.requires {
        walk_list!(vis, visit_refine_param, &requires.params);
        vis.visit_expr(&requires.pred);
    }
    walk_list!(vis, visit_fn_input, &fn_sig.inputs);
    vis.visit_fn_output(&fn_sig.output);
}

pub fn walk_fn_output<V: Visitor>(vis: &mut V, fn_output: &FnOutput) {
    vis.visit_fn_ret_ty(&fn_output.returns);
    walk_list!(vis, visit_ensures, &fn_output.ensures);
}

pub fn walk_generics<V: Visitor>(vis: &mut V, generics: &Generics) {
    walk_list!(vis, visit_generic_param, &generics.params);
    if let Some(predicates) = &generics.predicates {
        walk_list!(vis, visit_where_predicate, predicates);
    }
}

pub fn walk_fn_input<V: Visitor>(vis: &mut V, arg: &FnInput) {
    match arg {
        FnInput::Constr(bind, path, pred, _node_id) => {
            vis.visit_ident(*bind);
            vis.visit_path(path);
            vis.visit_expr(pred);
        }
        FnInput::StrgRef(bind, ty, _node_id) => {
            vis.visit_ident(*bind);
            vis.visit_ty(ty);
        }
        FnInput::Ty(bind, ty, _node_id) => {
            if let Some(bind) = bind {
                vis.visit_ident(*bind);
            }
            vis.visit_ty(ty);
        }
    }
}

pub fn walk_fn_ret_ty<V: Visitor>(vis: &mut V, fn_ret_ty: &FnRetTy) {
    match fn_ret_ty {
        FnRetTy::Default(_span) => {}
        FnRetTy::Ty(ty) => vis.visit_ty(ty),
    }
}

pub fn walk_ensures<V: Visitor>(vis: &mut V, ensures: &Ensures) {
    match ensures {
        Ensures::Type(bind, ty, _node_id) => {
            vis.visit_ident(*bind);
            vis.visit_ty(ty);
        }
        Ensures::Pred(pred) => {
            vis.visit_expr(pred);
        }
    }
}

pub fn walk_where_predicate<V: Visitor>(vis: &mut V, predicate: &WhereBoundPredicate) {
    vis.visit_ty(&predicate.bounded_ty);
    walk_list!(vis, visit_trait_ref, &predicate.bounds);
}

pub fn walk_generic_arg<V: Visitor>(vis: &mut V, arg: &GenericArg) {
    match &arg.kind {
        GenericArgKind::Type(ty) => {
            vis.visit_ty(ty);
        }
        GenericArgKind::Constraint(ident, ty) => {
            vis.visit_ident(*ident);
            vis.visit_ty(ty);
        }
    }
}

pub fn walk_refine_arg<V: Visitor>(vis: &mut V, arg: &RefineArg) {
    match arg {
        RefineArg::Bind(ident, _kind, _span, _node_id) => {
            vis.visit_ident(*ident);
        }
        RefineArg::Expr(e) => {
            vis.visit_expr(e);
        }
        RefineArg::Abs(params, e, _node_id, _span) => {
            walk_list!(vis, visit_refine_param, params);
            vis.visit_expr(e);
        }
    }
}

pub fn walk_indices<V: Visitor>(vis: &mut V, indices: &Indices) {
    walk_list!(vis, visit_refine_arg, &indices.indices);
}

pub fn walk_ty<V: Visitor>(vis: &mut V, ty: &Ty) {
    match &ty.kind {
        TyKind::Base(bty) => vis.visit_bty(bty),
        TyKind::Indexed { bty, indices } => {
            vis.visit_indices(indices);
            vis.visit_bty(bty);
        }
        TyKind::Exists { bind, bty, pred } => {
            vis.visit_ident(*bind);
            vis.visit_bty(bty);
            vis.visit_expr(pred);
        }
        TyKind::GeneralExists { params, ty, pred } => {
            walk_list!(vis, visit_refine_param, params);
            vis.visit_ty(ty);
            if let Some(pred) = pred {
                vis.visit_expr(pred);
            }
        }
        TyKind::Ref(_mutbl, ty) => {
            vis.visit_ty(ty);
        }
        TyKind::Constr(pred, ty) => {
            vis.visit_expr(pred);
            vis.visit_ty(ty);
        }
        TyKind::Tuple(tys) => {
            walk_list!(vis, visit_ty, tys);
        }
        TyKind::Array(ty, len) => {
            vis.visit_const_arg(len);
            vis.visit_ty(ty);
        }
        TyKind::ImplTrait(_node_id, trait_ref) => {
            walk_list!(vis, visit_trait_ref, trait_ref);
        }
        TyKind::Hole => {}
    }
}

pub fn walk_bty<V: Visitor>(vis: &mut V, bty: &BaseTy) {
    match &bty.kind {
        BaseTyKind::Path(qself, path) => {
            if let Some(qself) = qself {
                vis.visit_ty(qself);
            }
            vis.visit_path(path);
        }
        BaseTyKind::Slice(ty) => vis.visit_ty(ty),
    }
}

pub fn walk_path<V: Visitor>(vis: &mut V, path: &Path) {
    walk_list!(vis, visit_path_segment, &path.segments);
    walk_list!(vis, visit_refine_arg, &path.refine);
}

pub fn walk_path_segment<V: Visitor>(vis: &mut V, segment: &PathSegment) {
    vis.visit_ident(segment.ident);
    walk_list!(vis, visit_generic_arg, &segment.args);
}

pub fn walk_field_expr<V: Visitor>(vis: &mut V, expr: &FieldExpr) {
    vis.visit_ident(expr.ident);
    vis.visit_expr(&expr.expr);
}

pub fn walk_expr<V: Visitor>(vis: &mut V, expr: &Expr) {
    match &expr.kind {
        ExprKind::Path(qpath) => vis.visit_path_expr(qpath),
        ExprKind::Dot(base, fld) => {
            vis.visit_expr(base);
            vis.visit_ident(*fld);
        }
        ExprKind::Literal(lit) => {
            vis.visit_literal(*lit);
        }
        ExprKind::BinaryOp(_bin_op, box exprs) => {
            walk_list!(vis, visit_expr, exprs);
        }
        ExprKind::UnaryOp(_un_op, e) => {
            vis.visit_expr(e);
        }
        ExprKind::PrimUIF(_) => {}
        ExprKind::Call(callee, args) => {
            vis.visit_expr(callee);
            walk_list!(vis, visit_expr, args);
        }
        ExprKind::AssocReft(qself, path, name) => {
            vis.visit_ty(qself);
            vis.visit_path(path);
            vis.visit_ident(*name);
        }
        ExprKind::IfThenElse(box exprs) => {
            walk_list!(vis, visit_expr, exprs);
        }
        ExprKind::Constructor(path, exprs) => {
            if let Some(path) = path {
                vis.visit_path_expr(path);
            }
            walk_list!(vis, visit_constructor_args, exprs);
        }
        ExprKind::BoundedQuant(_, i, _, e) => {
            vis.visit_refine_param(i);
            vis.visit_expr(e);
        }
        ExprKind::Block(decls, body) => {
            for decl in decls {
                // the order here is important because the parameter is not in scope
                // in the initializer
                vis.visit_expr(&decl.init);
                vis.visit_refine_param(&decl.param);
            }
            vis.visit_expr(body);
        }
        ExprKind::SetLiteral(exprs) => {
            walk_list!(vis, visit_expr, exprs);
        }
    }
}

pub fn walk_path_expr<V: Visitor>(vis: &mut V, qpath: &ExprPath) {
    walk_list!(vis, visit_path_expr_segment, &qpath.segments);
}

pub fn walk_path_expr_segment<V: Visitor>(vis: &mut V, segment: &ExprPathSegment) {
    vis.visit_ident(segment.ident);
}
