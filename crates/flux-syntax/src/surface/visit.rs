//! A visitor for types in [`surface`]
//!
//! In general there's no specific order except that [refinement parameters] should be
//! visited in an order that matches their scope. Name resolution relies on this gurantee.
//!
//! [`surface`]: crate::surface
//! [refinement parameters]: crate::surface::RefineParam
use rustc_span::symbol::Ident;

use super::{
    Async, BaseSort, BaseTy, BaseTyKind, ConstArg, ConstArgKind, ConstantInfo, ConstructorArg,
    Ensures, EnumDef, Expr, ExprKind, ExprPath, ExprPathSegment, FieldExpr, FnInput, FnOutput,
    FnRetTy, FnSig, GenericArg, GenericArgKind, GenericParam, Generics, Impl, ImplAssocReft,
    Indices, ItemKind, Lit, Path, PathSegment, Qualifier, RefineArg, RefineParam, Requires, Sort,
    SortPath, SpecFunc, StructDef, Trait, TraitAssocReft, TraitRef, Ty, TyAlias, TyKind,
    UseTreeKind, VariantDef, VariantRet, WhereBoundPredicate,
};
use crate::surface::{FluxItem, ImplItemFn, Item, PrimOpProp, SortDecl, TraitItemFn, UseTree};

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

pub trait Visitor<'v>: Sized {
    fn visit_flux_item(&mut self, item: &'v FluxItem) {
        walk_flux_item(self, item);
    }

    fn visit_qualifier(&mut self, qualifier: &'v Qualifier) {
        walk_qualifier(self, qualifier);
    }

    fn visit_sort_decl(&mut self, sort_decl: &'v SortDecl) {
        walk_sort_decl(self, sort_decl);
    }

    fn visit_defn(&mut self, defn: &'v SpecFunc) {
        walk_defn(self, defn);
    }

    fn visit_primop_prop(&mut self, prop: &'v PrimOpProp) {
        walk_primop_prop(self, prop);
    }

    fn visit_refine_param(&mut self, param: &'v RefineParam) {
        walk_refine_param(self, param);
    }

    fn visit_generic_param(&mut self, param: &'v GenericParam) {
        walk_generic_param(self, param);
    }

    fn visit_sort(&mut self, sort: &'v Sort) {
        walk_sort(self, sort);
    }

    fn visit_item(&mut self, item: &'v Item) {
        walk_item(self, item);
    }

    fn visit_trait_item(&mut self, item: &'v TraitItemFn) {
        walk_trait_item(self, item);
    }

    fn visit_impl_item(&mut self, item: &'v ImplItemFn) {
        walk_impl_item(self, item);
    }

    fn visit_trait(&mut self, trait_: &'v Trait) {
        walk_trait(self, trait_);
    }

    fn visit_trait_assoc_reft(&mut self, assoc_reft: &'v TraitAssocReft) {
        walk_trait_assoc_reft(self, assoc_reft);
    }

    fn visit_impl(&mut self, impl_: &'v Impl) {
        walk_impl(self, impl_);
    }

    fn visit_impl_assoc_reft(&mut self, assoc_reft: &'v ImplAssocReft) {
        walk_impl_assoc_reft(self, assoc_reft);
    }

    fn visit_trait_ref(&mut self, trait_ref: &'v TraitRef) {
        walk_trait_ref(self, trait_ref);
    }

    fn visit_base_sort(&mut self, bsort: &'v BaseSort) {
        walk_base_sort(self, bsort);
    }

    fn visit_sort_path(&mut self, path: &'v SortPath) {
        walk_sort_path(self, path);
    }

    fn visit_ty_alias(&mut self, ty_alias: &'v TyAlias) {
        walk_ty_alias(self, ty_alias);
    }

    fn visit_struct_def(&mut self, struct_def: &'v StructDef) {
        walk_struct_def(self, struct_def);
    }

    fn visit_constant(&mut self, _constant: &'v ConstantInfo) {
        walk_constant(self, _constant);
    }

    fn visit_enum_def(&mut self, enum_def: &'v EnumDef) {
        walk_enum_def(self, enum_def);
    }

    fn visit_variant(&mut self, variant: &'v VariantDef) {
        walk_variant(self, variant);
    }

    fn visit_variant_ret(&mut self, ret: &'v VariantRet) {
        walk_variant_ret(self, ret);
    }

    fn visit_fn_sig(&mut self, fn_sig: &'v FnSig) {
        walk_fn_sig(self, fn_sig);
    }

    fn visit_requires(&mut self, requires: &'v Requires) {
        walk_requires(self, requires);
    }

    fn visit_fn_output(&mut self, fn_output: &'v FnOutput) {
        walk_fn_output(self, fn_output);
    }

    fn visit_async(&mut self, _asyncness: &'v Async) {}

    fn visit_generics(&mut self, generics: &'v Generics) {
        walk_generics(self, generics);
    }

    fn visit_fn_input(&mut self, input: &'v FnInput) {
        walk_fn_input(self, input);
    }

    fn visit_fn_ret_ty(&mut self, fn_ret_ty: &'v FnRetTy) {
        walk_fn_ret_ty(self, fn_ret_ty);
    }

    fn visit_ensures(&mut self, ensures: &'v Ensures) {
        walk_ensures(self, ensures);
    }

    fn visit_where_predicate(&mut self, predicate: &'v WhereBoundPredicate) {
        walk_where_predicate(self, predicate);
    }

    fn visit_generic_arg(&mut self, arg: &'v GenericArg) {
        walk_generic_arg(self, arg);
    }

    fn visit_refine_arg(&mut self, arg: &'v RefineArg) {
        walk_refine_arg(self, arg);
    }

    fn visit_indices(&mut self, indices: &'v Indices) {
        walk_indices(self, indices);
    }

    fn visit_ty(&mut self, ty: &'v Ty) {
        walk_ty(self, ty);
    }

    fn visit_const_arg(&mut self, const_arg: &'v ConstArg) {
        walk_const_arg(self, const_arg);
    }

    fn visit_bty(&mut self, bty: &'v BaseTy) {
        walk_bty(self, bty);
    }

    fn visit_path(&mut self, path: &'v Path) {
        walk_path(self, path);
    }

    fn visit_path_segment(&mut self, segment: &'v PathSegment) {
        walk_path_segment(self, segment);
    }

    fn visit_expr(&mut self, expr: &'v Expr) {
        walk_expr(self, expr);
    }

    fn visit_constructor_args(&mut self, expr: &'v ConstructorArg) {
        match expr {
            ConstructorArg::FieldExpr(field_expr) => walk_field_expr(self, field_expr),
            ConstructorArg::Spread(spread) => self.visit_expr(&spread.expr),
        }
    }

    fn visit_path_expr(&mut self, qpath: &'v ExprPath) {
        walk_path_expr(self, qpath);
    }

    fn visit_path_expr_segment(&mut self, segment: &'v ExprPathSegment) {
        walk_path_expr_segment(self, segment);
    }

    fn visit_ident(&mut self, _ident: Ident) {}

    fn visit_literal(&mut self, _lit: Lit) {}
}

pub fn walk_flux_item<'v, V: Visitor<'v>>(vis: &mut V, item: &'v FluxItem) {
    match item {
        FluxItem::Qualifier(qualifier) => vis.visit_qualifier(qualifier),
        FluxItem::FuncDef(spec_func) => vis.visit_defn(spec_func),
        FluxItem::SortDecl(sort_decl) => vis.visit_sort_decl(sort_decl),
        FluxItem::PrimOpProp(prim_op_prop) => vis.visit_primop_prop(prim_op_prop),
        FluxItem::Use(use_tree) => walk_use_tree(vis, use_tree),
    }
}

pub fn walk_use_tree<'v, V: Visitor<'v>>(vis: &mut V, use_tree: &'v UseTree) {
    vis.visit_path_expr(&use_tree.prefix);
    match &use_tree.kind {
        UseTreeKind::Simple => {}
        UseTreeKind::Nested(items) => {
            for item in items {
                walk_use_tree(vis, item);
            }
        }
    }
}

pub fn walk_qualifier<'v, V: Visitor<'v>>(vis: &mut V, qualifier: &'v Qualifier) {
    vis.visit_ident(qualifier.name);
    walk_list!(vis, visit_refine_param, &qualifier.params);
    vis.visit_expr(&qualifier.expr);
}

pub fn walk_sort_decl<'v, V: Visitor<'v>>(vis: &mut V, sort_decl: &'v SortDecl) {
    vis.visit_ident(sort_decl.name);
    walk_list!(vis, visit_ident, sort_decl.sort_vars.iter().copied());
}

pub fn walk_defn<'v, V: Visitor<'v>>(vis: &mut V, defn: &'v SpecFunc) {
    vis.visit_ident(defn.name);
    walk_list!(vis, visit_ident, defn.sort_vars.iter().copied());
    walk_list!(vis, visit_refine_param, &defn.params);
    vis.visit_sort(&defn.output);
    if let Some(body) = &defn.body {
        vis.visit_expr(body);
    }
}

pub fn walk_primop_prop<'v, V: Visitor<'v>>(vis: &mut V, prop: &'v PrimOpProp) {
    vis.visit_ident(prop.name);
    walk_list!(vis, visit_refine_param, &prop.params);
    vis.visit_expr(&prop.body);
}

pub fn walk_requires<'v, V: Visitor<'v>>(vis: &mut V, requires: &'v Requires) {
    walk_list!(vis, visit_refine_param, &requires.params);
    vis.visit_expr(&requires.pred);
}

pub fn walk_refine_param<'v, V: Visitor<'v>>(vis: &mut V, param: &'v RefineParam) {
    vis.visit_ident(param.ident);
    vis.visit_sort(&param.sort);
}

pub fn walk_generic_param<'v, V: Visitor<'v>>(vis: &mut V, param: &'v GenericParam) {
    vis.visit_ident(param.name);
}

pub fn walk_sort<'v, V: Visitor<'v>>(vis: &mut V, sort: &'v Sort) {
    match sort {
        Sort::Base(bsort) => vis.visit_base_sort(bsort),
        Sort::Func { inputs, output } => {
            walk_list!(vis, visit_base_sort, inputs);
            vis.visit_base_sort(output);
        }
        Sort::Infer => {}
    }
}

pub fn walk_item<'v, V: Visitor<'v>>(vis: &mut V, item: &'v Item) {
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
        ItemKind::Static(static_info) => vis.visit_ty(&static_info.ty),
        ItemKind::TyAlias(ty_alias) => vis.visit_ty_alias(ty_alias),
        ItemKind::Mod => {}
    }
}

pub fn walk_trait_item<'v, V: Visitor<'v>>(vis: &mut V, item: &'v TraitItemFn) {
    if let Some(fn_sig) = item.sig.as_ref() {
        vis.visit_fn_sig(fn_sig);
    }
}

pub fn walk_impl_item<'v, V: Visitor<'v>>(vis: &mut V, item: &'v ImplItemFn) {
    if let Some(fn_sig) = item.sig.as_ref() {
        vis.visit_fn_sig(fn_sig);
    }
}

pub fn walk_trait<'v, V: Visitor<'v>>(vis: &mut V, trait_: &'v Trait) {
    if let Some(generics) = &trait_.generics {
        vis.visit_generics(generics);
    }
    walk_list!(vis, visit_trait_assoc_reft, &trait_.assoc_refinements);
}

pub fn walk_trait_assoc_reft<'v, V: Visitor<'v>>(vis: &mut V, assoc_reft: &'v TraitAssocReft) {
    vis.visit_ident(assoc_reft.name);
    walk_list!(vis, visit_refine_param, &assoc_reft.params);
    vis.visit_base_sort(&assoc_reft.output);
    if let Some(expr) = &assoc_reft.body {
        vis.visit_expr(expr);
    }
}

pub fn walk_impl<'v, V: Visitor<'v>>(vis: &mut V, impl_: &'v Impl) {
    if let Some(generics) = &impl_.generics {
        vis.visit_generics(generics);
    }
    walk_list!(vis, visit_impl_assoc_reft, &impl_.assoc_refinements);
}

pub fn walk_impl_assoc_reft<'v, V: Visitor<'v>>(vis: &mut V, assoc_reft: &'v ImplAssocReft) {
    vis.visit_ident(assoc_reft.name);
    walk_list!(vis, visit_refine_param, &assoc_reft.params);
    vis.visit_expr(&assoc_reft.body);
    vis.visit_base_sort(&assoc_reft.output);
}

pub fn walk_trait_ref<'v, V: Visitor<'v>>(vis: &mut V, trait_ref: &'v TraitRef) {
    vis.visit_path(&trait_ref.path);
}

pub fn walk_base_sort<'v, V: Visitor<'v>>(vis: &mut V, bsort: &'v BaseSort) {
    match bsort {
        BaseSort::BitVec(_len) => {}
        BaseSort::Path(path) => vis.visit_sort_path(path),
        BaseSort::SortOf(qself, path) => {
            vis.visit_ty(qself);
            vis.visit_path(path);
        }
        BaseSort::Tuple(sorts) => {
            walk_list!(vis, visit_base_sort, sorts);
        }
    }
}

pub fn walk_sort_path<'v, V: Visitor<'v>>(vis: &mut V, path: &'v SortPath) {
    walk_list!(vis, visit_ident, path.segments.iter().copied());
    walk_list!(vis, visit_base_sort, &path.args);
}

pub fn walk_ty_alias<'v, V: Visitor<'v>>(vis: &mut V, ty_alias: &'v TyAlias) {
    vis.visit_ident(ty_alias.ident);
    vis.visit_generics(&ty_alias.generics);
    walk_list!(vis, visit_refine_param, &ty_alias.params);
    if let Some(index) = &ty_alias.index {
        vis.visit_refine_param(index);
    }
    vis.visit_ty(&ty_alias.ty);
}
pub fn walk_constant<'v, V: Visitor<'v>>(vis: &mut V, constant_info: &'v ConstantInfo) {
    if let Some(expr) = &constant_info.expr {
        vis.visit_expr(expr);
    }
}

pub fn walk_struct_def<'v, V: Visitor<'v>>(vis: &mut V, struct_def: &'v StructDef) {
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

pub fn walk_enum_def<'v, V: Visitor<'v>>(vis: &mut V, enum_def: &'v EnumDef) {
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

pub fn walk_variant<'v, V: Visitor<'v>>(vis: &mut V, variant: &'v VariantDef) {
    walk_list!(vis, visit_ty, &variant.fields);
    if let Some(ret) = &variant.ret {
        vis.visit_variant_ret(ret);
    }
}

pub fn walk_fn_trait_ref<'v, V: Visitor<'v>>(
    vis: &mut V,
    in_arg: &'v GenericArg,
    out_arg: &'v GenericArg,
) {
    vis.visit_generic_arg(in_arg);
    vis.visit_generic_arg(out_arg);
}

pub fn walk_variant_ret<'v, V: Visitor<'v>>(vis: &mut V, ret: &'v VariantRet) {
    vis.visit_path(&ret.path);
    vis.visit_indices(&ret.indices);
}

// Explicit refinement params must be brought into scope *before* the generics, because a
// `where` clause lives in `generics.predicates` and may mention them, e.g. an `hrn` parameter
// used in the refinement of an `Fn`-trait bound e.g. tests/tests/pos/abstract_refinements/test05.rs
// Implicit params (named inputs, `@`/`#` binders) are already pre-collected in `on_fn_sig`
// before the walk, so only the explicit ones need this.

pub fn walk_fn_sig<'v, V: Visitor<'v>>(vis: &mut V, fn_sig: &'v FnSig) {
    vis.visit_async(&fn_sig.asyncness);

    walk_list!(vis, visit_refine_param, &fn_sig.params);
    vis.visit_generics(&fn_sig.generics);
    walk_list!(vis, visit_requires, &fn_sig.requires);
    walk_list!(vis, visit_fn_input, &fn_sig.inputs);
    if let Some(no_panic_expr) = &fn_sig.no_panic {
        vis.visit_expr(no_panic_expr);
    }
    vis.visit_fn_output(&fn_sig.output);
}

pub fn walk_fn_output<'v, V: Visitor<'v>>(vis: &mut V, fn_output: &'v FnOutput) {
    vis.visit_fn_ret_ty(&fn_output.returns);
    walk_list!(vis, visit_ensures, &fn_output.ensures);
}

pub fn walk_generics<'v, V: Visitor<'v>>(vis: &mut V, generics: &'v Generics) {
    walk_list!(vis, visit_generic_param, &generics.params);
    if let Some(predicates) = &generics.predicates {
        walk_list!(vis, visit_where_predicate, predicates);
    }
}

pub fn walk_fn_input<'v, V: Visitor<'v>>(vis: &mut V, arg: &'v FnInput) {
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

pub fn walk_fn_ret_ty<'v, V: Visitor<'v>>(vis: &mut V, fn_ret_ty: &'v FnRetTy) {
    match fn_ret_ty {
        FnRetTy::Default(_span) => {}
        FnRetTy::Ty(ty) => vis.visit_ty(ty),
    }
}

pub fn walk_ensures<'v, V: Visitor<'v>>(vis: &mut V, ensures: &'v Ensures) {
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

pub fn walk_where_predicate<'v, V: Visitor<'v>>(vis: &mut V, predicate: &'v WhereBoundPredicate) {
    vis.visit_ty(&predicate.bounded_ty);
    walk_list!(vis, visit_trait_ref, &predicate.bounds);
}

pub fn walk_generic_arg<'v, V: Visitor<'v>>(vis: &mut V, arg: &'v GenericArg) {
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

pub fn walk_refine_arg<'v, V: Visitor<'v>>(vis: &mut V, arg: &'v RefineArg) {
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

pub fn walk_indices<'v, V: Visitor<'v>>(vis: &mut V, indices: &'v Indices) {
    walk_list!(vis, visit_refine_arg, &indices.indices);
}

pub fn walk_ty<'v, V: Visitor<'v>>(vis: &mut V, ty: &'v Ty) {
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
        TyKind::BareFn(bare_fn) => {
            walk_list!(vis, visit_ty, &bare_fn.inputs);
            vis.visit_fn_ret_ty(&bare_fn.output);
        }
        TyKind::ImplTrait(_node_id, trait_ref) => {
            walk_list!(vis, visit_trait_ref, trait_ref);
        }
        TyKind::Hole => {}
    }
}

pub fn walk_const_arg<'v, V: Visitor<'v>>(vis: &mut V, const_arg: &'v ConstArg) {
    if let ConstArgKind::Path(path) = &const_arg.kind {
        vis.visit_path(path);
    }
}

pub fn walk_bty<'v, V: Visitor<'v>>(vis: &mut V, bty: &'v BaseTy) {
    match &bty.kind {
        BaseTyKind::Path(qself, path) => {
            if let Some(qself) = qself {
                vis.visit_ty(qself);
            }
            vis.visit_path(path);
        }
        BaseTyKind::Slice(ty) => vis.visit_ty(ty),
        BaseTyKind::Ptr(_, ty) => vis.visit_ty(ty),
    }
}

pub fn walk_path<'v, V: Visitor<'v>>(vis: &mut V, path: &'v Path) {
    walk_list!(vis, visit_path_segment, &path.segments);
    walk_list!(vis, visit_refine_arg, &path.refine);
}

pub fn walk_path_segment<'v, V: Visitor<'v>>(vis: &mut V, segment: &'v PathSegment) {
    vis.visit_ident(segment.ident);
    walk_list!(vis, visit_generic_arg, &segment.args);
}

pub fn walk_field_expr<'v, V: Visitor<'v>>(vis: &mut V, expr: &'v FieldExpr) {
    vis.visit_ident(expr.ident);
    vis.visit_refine_arg(&expr.expr);
}

pub fn walk_expr<'v, V: Visitor<'v>>(vis: &mut V, expr: &'v Expr) {
    match &expr.kind {
        ExprKind::Path(qpath) => vis.visit_path_expr(qpath),
        ExprKind::Dot(base, fld) => {
            vis.visit_expr(base);
            vis.visit_ident(*fld);
        }
        ExprKind::Literal(lit) => {
            vis.visit_literal(*lit);
        }
        ExprKind::BinaryOp(_bin_op, deref!(exprs)) => {
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
        ExprKind::IfThenElse(deref!(exprs)) => {
            walk_list!(vis, visit_expr, exprs);
        }
        ExprKind::Constructor(path, exprs) => {
            if let Some(path) = path {
                vis.visit_path_expr(path);
            }
            walk_list!(vis, visit_constructor_args, exprs);
        }
        ExprKind::Quant(_, i, _, e) => {
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
        ExprKind::Tuple(exprs) => {
            walk_list!(vis, visit_expr, exprs);
        }
    }
}

pub fn walk_path_expr<'v, V: Visitor<'v>>(vis: &mut V, qpath: &'v ExprPath) {
    walk_list!(vis, visit_path_expr_segment, &qpath.segments);
}

pub fn walk_path_expr_segment<'v, V: Visitor<'v>>(vis: &mut V, segment: &'v ExprPathSegment) {
    vis.visit_ident(segment.ident);
}
