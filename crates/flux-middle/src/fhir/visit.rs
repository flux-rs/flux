use super::{
    AliasReft, BaseTy, BaseTyKind, Ensures, EnumDef, Expr, ExprKind, FieldDef, FnDecl, FnOutput,
    FnSig, FuncSort, GenericArg, GenericBound, Generics, Impl, ImplAssocReft, ImplItem,
    ImplItemKind, Item, ItemKind, Lifetime, Lit, Node, OpaqueTy, Path, PathExpr, PathSegment,
    PolyFuncSort, PolyTraitRef, QPath, RefineArg, RefineArgKind, RefineParam, Requires, Sort,
    SortPath, StructDef, TraitAssocReft, TraitItem, TraitItemKind, Ty, TyAlias, TyKind,
    TypeBinding, VariantDef, VariantRet, WhereBoundPredicate,
};
use crate::fhir::StructKind;

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
    fn visit_node(&mut self, node: &Node<'v>) {
        walk_node(self, node);
    }

    fn visit_item(&mut self, item: &Item<'v>) {
        walk_item(self, item);
    }

    fn visit_trait_item(&mut self, trait_item: &TraitItem<'v>) {
        walk_trait_item(self, trait_item);
    }

    fn visit_impl_item(&mut self, impl_item: &ImplItem<'v>) {
        walk_impl_item(self, impl_item);
    }

    fn visit_generics(&mut self, generics: &Generics<'v>) {
        walk_generics(self, generics);
    }

    fn visit_where_predicate(&mut self, predicate: &WhereBoundPredicate<'v>) {
        walk_where_predicate(self, predicate);
    }

    fn visit_impl(&mut self, impl_: &Impl<'v>) {
        walk_impl(self, impl_);
    }

    fn visit_impl_assoc_reft(&mut self, assoc_reft: &ImplAssocReft<'v>) {
        walk_impl_assoc_reft(self, assoc_reft);
    }

    fn visit_trait_assoc_reft(&mut self, assoc_reft: &TraitAssocReft<'v>) {
        walk_trait_assoc_reft(self, assoc_reft);
    }

    fn visit_struct_def(&mut self, struct_def: &StructDef<'v>) {
        walk_struct_def(self, struct_def);
    }

    fn visit_enum_def(&mut self, enum_def: &EnumDef<'v>) {
        walk_enum_def(self, enum_def);
    }

    fn visit_variant(&mut self, variant: &VariantDef<'v>) {
        walk_variant(self, variant);
    }

    fn visit_field_def(&mut self, field: &FieldDef<'v>) {
        walk_field_def(self, field);
    }

    fn visit_variant_ret(&mut self, ret: &VariantRet<'v>) {
        walk_variant_ret(self, ret);
    }

    fn visit_ty_alias(&mut self, ty_alias: &TyAlias<'v>) {
        walk_ty_alias(self, ty_alias);
    }

    fn visit_opaque_ty(&mut self, opaque_ty: &OpaqueTy<'v>) {
        walk_opaque_ty(self, opaque_ty);
    }

    fn visit_generic_bound(&mut self, bound: &GenericBound<'v>) {
        walk_generic_bound(self, bound);
    }

    fn visit_poly_trait_ref(&mut self, trait_ref: &PolyTraitRef<'v>) {
        walk_poly_trait_ref(self, trait_ref);
    }

    fn visit_fn_sig(&mut self, sig: &FnSig<'v>) {
        walk_fn_sig(self, sig);
    }

    fn visit_fn_decl(&mut self, decl: &FnDecl<'v>) {
        walk_fn_decl(self, decl);
    }

    fn visit_refine_param(&mut self, param: &RefineParam<'v>) {
        walk_refine_param(self, param);
    }

    fn visit_requires(&mut self, requires: &Requires<'v>) {
        walk_requires(self, requires);
    }

    fn visit_ensures(&mut self, ensures: &Ensures<'v>) {
        walk_ensures(self, ensures);
    }

    fn visit_fn_output(&mut self, output: &FnOutput<'v>) {
        walk_fn_output(self, output);
    }

    fn visit_generic_arg(&mut self, arg: &GenericArg<'v>) {
        walk_generic_arg(self, arg);
    }

    fn visit_lifetime(&mut self, _lft: &Lifetime) {}

    fn visit_ty(&mut self, ty: &Ty<'v>) {
        walk_ty(self, ty);
    }

    fn visit_bty(&mut self, bty: &BaseTy<'v>) {
        walk_bty(self, bty);
    }

    fn visit_qpath(&mut self, qpath: &QPath<'v>) {
        walk_qpath(self, qpath);
    }

    fn visit_path(&mut self, path: &Path<'v>) {
        walk_path(self, path);
    }

    fn visit_path_segment(&mut self, segment: &PathSegment<'v>) {
        walk_path_segment(self, segment);
    }

    fn visit_type_binding(&mut self, binding: &TypeBinding<'v>) {
        walk_type_binding(self, binding);
    }

    fn visit_sort(&mut self, sort: &Sort<'v>) {
        walk_sort(self, sort);
    }

    fn visit_sort_path(&mut self, path: &SortPath<'v>) {
        walk_sort_path(self, path);
    }

    fn visit_poly_func_sort(&mut self, func: &PolyFuncSort<'v>) {
        walk_poly_func_sort(self, func);
    }

    fn visit_func_sort(&mut self, func: &FuncSort<'v>) {
        walk_func_sort(self, func);
    }

    fn visit_refine_arg(&mut self, arg: &RefineArg<'v>) {
        walk_refine_arg(self, arg);
    }

    fn visit_expr(&mut self, expr: &Expr<'v>) {
        walk_expr(self, expr);
    }

    fn visit_alias_reft(&mut self, alias_reft: &AliasReft<'v>) {
        walk_alias_reft(self, alias_reft);
    }

    fn visit_literal(&mut self, _lit: &Lit) {}

    fn visit_path_expr(&mut self, _path: &PathExpr<'v>) {}
}

pub fn walk_impl<'v, V: Visitor<'v>>(vis: &mut V, impl_: &Impl<'v>) {
    vis.visit_generics(&impl_.generics);
    walk_list!(vis, visit_impl_assoc_reft, impl_.assoc_refinements);
}

pub fn walk_struct_def<'v, V: Visitor<'v>>(vis: &mut V, struct_def: &StructDef<'v>) {
    walk_list!(vis, visit_refine_param, struct_def.params);
    walk_list!(vis, visit_expr, struct_def.invariants);
    if let StructKind::Transparent { fields } = struct_def.kind {
        walk_list!(vis, visit_field_def, fields);
    }
}

pub fn walk_enum_def<'v, V: Visitor<'v>>(vis: &mut V, enum_def: &EnumDef<'v>) {
    walk_list!(vis, visit_refine_param, enum_def.params);
    walk_list!(vis, visit_variant, enum_def.variants);
    walk_list!(vis, visit_expr, enum_def.invariants);
}

pub fn walk_variant<'v, V: Visitor<'v>>(vis: &mut V, variant: &VariantDef<'v>) {
    walk_list!(vis, visit_refine_param, variant.params);
    walk_list!(vis, visit_field_def, variant.fields);
    vis.visit_variant_ret(&variant.ret);
}

pub fn walk_field_def<'v, V: Visitor<'v>>(vis: &mut V, field: &FieldDef<'v>) {
    let FieldDef { def_id: _, ty, lifted: _ } = field;
    vis.visit_ty(ty);
}

pub fn walk_variant_ret<'v, V: Visitor<'v>>(vis: &mut V, ret: &VariantRet<'v>) {
    let VariantRet { bty, idx } = ret;
    vis.visit_bty(bty);
    vis.visit_refine_arg(idx);
}

pub fn walk_ty_alias<'v, V: Visitor<'v>>(vis: &mut V, ty_alias: &TyAlias<'v>) {
    vis.visit_generics(&ty_alias.generics);
    vis.visit_ty(&ty_alias.ty);
    walk_list!(vis, visit_refine_param, ty_alias.params);
}

pub fn walk_opaque_ty<'v, V: Visitor<'v>>(vis: &mut V, opaque_ty: &OpaqueTy<'v>) {
    vis.visit_generics(&opaque_ty.generics);
    walk_list!(vis, visit_generic_bound, opaque_ty.bounds);
}

pub fn walk_generic_bound<'v, V: Visitor<'v>>(vis: &mut V, bound: &GenericBound<'v>) {
    match bound {
        GenericBound::Trait(trait_ref, _) => vis.visit_poly_trait_ref(trait_ref),
    }
}

pub fn walk_poly_trait_ref<'v, V: Visitor<'v>>(vis: &mut V, trait_ref: &PolyTraitRef<'v>) {
    vis.visit_path(&trait_ref.trait_ref);
}

pub fn walk_node<'v, V: Visitor<'v>>(vis: &mut V, node: &Node<'v>) {
    match node {
        Node::Item(item) => vis.visit_item(item),
        Node::TraitItem(trait_item) => vis.visit_trait_item(trait_item),
        Node::ImplItem(impl_item) => vis.visit_impl_item(impl_item),
    }
}

pub fn walk_item<'v, V: Visitor<'v>>(vis: &mut V, item: &Item<'v>) {
    match &item.kind {
        ItemKind::Enum(enum_def) => vis.visit_enum_def(enum_def),
        ItemKind::Struct(struct_def) => vis.visit_struct_def(struct_def),
        ItemKind::TyAlias(ty_alias) => vis.visit_ty_alias(ty_alias),
        ItemKind::Trait(trait_) => {
            vis.visit_generics(&trait_.generics);
            walk_list!(vis, visit_trait_assoc_reft, trait_.assoc_refinements);
        }
        ItemKind::Impl(impl_) => vis.visit_impl(impl_),
        ItemKind::Fn(fn_sig) => vis.visit_fn_sig(fn_sig),
        ItemKind::OpaqueTy(opaque_ty) => vis.visit_opaque_ty(opaque_ty),
    }
}

pub fn walk_trait_item<'v, V: Visitor<'v>>(vis: &mut V, trait_item: &TraitItem<'v>) {
    match &trait_item.kind {
        TraitItemKind::Fn(fn_sig) => vis.visit_fn_sig(fn_sig),
        TraitItemKind::Type(assoc_type) => {
            vis.visit_generics(&assoc_type.generics);
        }
    }
}

pub fn walk_impl_item<'v, V: Visitor<'v>>(vis: &mut V, impl_item: &ImplItem<'v>) {
    match &impl_item.kind {
        ImplItemKind::Fn(fn_sig) => vis.visit_fn_sig(fn_sig),
        ImplItemKind::Type(assoc_type) => {
            vis.visit_generics(&assoc_type.generics);
        }
    }
}

pub fn walk_trait_assoc_reft<'v, V: Visitor<'v>>(vis: &mut V, assoc_reft: &TraitAssocReft<'v>) {
    walk_list!(vis, visit_refine_param, assoc_reft.params);
    vis.visit_sort(&assoc_reft.output);
}

pub fn walk_impl_assoc_reft<'v, V: Visitor<'v>>(vis: &mut V, assoc_reft: &ImplAssocReft<'v>) {
    walk_list!(vis, visit_refine_param, assoc_reft.params);
    vis.visit_sort(&assoc_reft.output);
    vis.visit_expr(&assoc_reft.body);
}

pub fn walk_generics<'v, V: Visitor<'v>>(vis: &mut V, generics: &Generics<'v>) {
    walk_list!(vis, visit_refine_param, generics.refinement_params);
    walk_list!(vis, visit_where_predicate, generics.predicates);
}

pub fn walk_where_predicate<'v, V: Visitor<'v>>(vis: &mut V, predicate: &WhereBoundPredicate<'v>) {
    vis.visit_ty(&predicate.bounded_ty);
    walk_list!(vis, visit_generic_bound, predicate.bounds);
}

pub fn walk_fn_sig<'v, V: Visitor<'v>>(vis: &mut V, sig: &FnSig<'v>) {
    vis.visit_fn_decl(sig.decl);
}

pub fn walk_fn_decl<'v, V: Visitor<'v>>(vis: &mut V, decl: &FnDecl<'v>) {
    vis.visit_generics(&decl.generics);
    walk_list!(vis, visit_requires, decl.requires);
    walk_list!(vis, visit_ty, decl.inputs);
    vis.visit_fn_output(&decl.output);
}

pub fn walk_refine_param<'v, V: Visitor<'v>>(vis: &mut V, param: &RefineParam<'v>) {
    vis.visit_sort(&param.sort);
}

pub fn walk_requires<'v, V: Visitor<'v>>(vis: &mut V, requires: &Requires<'v>) {
    walk_list!(vis, visit_refine_param, requires.params);
    vis.visit_expr(&requires.pred);
}

pub fn walk_ensures<'v, V: Visitor<'v>>(vis: &mut V, constraint: &Ensures<'v>) {
    match constraint {
        Ensures::Type(loc, ty) => {
            vis.visit_path_expr(loc);
            vis.visit_ty(ty);
        }
        Ensures::Pred(pred) => {
            vis.visit_expr(pred);
        }
    }
}

pub fn walk_fn_output<'v, V: Visitor<'v>>(vis: &mut V, output: &FnOutput<'v>) {
    walk_list!(vis, visit_refine_param, output.params);
    vis.visit_ty(&output.ret);
    walk_list!(vis, visit_ensures, output.ensures);
}

pub fn walk_generic_arg<'v, V: Visitor<'v>>(vis: &mut V, arg: &GenericArg<'v>) {
    match arg {
        GenericArg::Lifetime(lft) => vis.visit_lifetime(lft),
        GenericArg::Type(ty) => vis.visit_ty(ty),
    }
}

pub fn walk_ty<'v, V: Visitor<'v>>(vis: &mut V, ty: &Ty<'v>) {
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
            vis.visit_expr(&pred);
            vis.visit_ty(ty);
        }
        TyKind::StrgRef(lft, loc, ty) => {
            vis.visit_lifetime(&lft);
            vis.visit_path_expr(loc);
            vis.visit_ty(ty);
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

pub fn walk_bty<'v, V: Visitor<'v>>(vis: &mut V, bty: &BaseTy<'v>) {
    match &bty.kind {
        BaseTyKind::Path(path) => vis.visit_qpath(path),
        BaseTyKind::Slice(ty) => vis.visit_ty(ty),
    }
}

pub fn walk_qpath<'v, V: Visitor<'v>>(vis: &mut V, qpath: &QPath<'v>) {
    match qpath {
        QPath::Resolved(qself, path) => {
            if let Some(self_ty) = qself {
                vis.visit_ty(self_ty);
            }
            vis.visit_path(path);
        }
        QPath::TypeRelative(qself, assoc) => {
            vis.visit_ty(qself);
            vis.visit_path_segment(assoc);
        }
    }
}

pub fn walk_path<'v, V: Visitor<'v>>(vis: &mut V, path: &Path<'v>) {
    walk_list!(vis, visit_path_segment, path.segments);
    walk_list!(vis, visit_refine_arg, path.refine);
}

pub fn walk_path_segment<'v, V: Visitor<'v>>(vis: &mut V, segment: &PathSegment<'v>) {
    walk_list!(vis, visit_generic_arg, segment.args);
    walk_list!(vis, visit_type_binding, segment.bindings);
}

pub fn walk_type_binding<'v, V: Visitor<'v>>(vis: &mut V, binding: &TypeBinding<'v>) {
    let TypeBinding { ident: _, term } = binding;
    vis.visit_ty(term);
}

pub fn walk_sort<'v, V: Visitor<'v>>(vis: &mut V, sort: &Sort<'v>) {
    match sort {
        Sort::Path(path) => vis.visit_sort_path(path),
        Sort::Func(func) => vis.visit_poly_func_sort(func),
        Sort::Loc | Sort::BitVec(_) | Sort::Infer => {}
    }
}

pub fn walk_sort_path<'v, V: Visitor<'v>>(vis: &mut V, path: &SortPath<'v>) {
    walk_list!(vis, visit_sort, path.args);
}

pub fn walk_poly_func_sort<'v, V: Visitor<'v>>(vis: &mut V, func: &PolyFuncSort<'v>) {
    let PolyFuncSort { params: _, fsort } = func;
    vis.visit_func_sort(fsort);
}

pub fn walk_func_sort<'v, V: Visitor<'v>>(vis: &mut V, func: &FuncSort<'v>) {
    walk_list!(vis, visit_sort, func.inputs_and_output);
}

pub fn walk_refine_arg<'v, V: Visitor<'v>>(vis: &mut V, arg: &RefineArg<'v>) {
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

pub fn walk_alias_reft<'v, V: Visitor<'v>>(vis: &mut V, alias: &AliasReft<'v>) {
    vis.visit_ty(alias.qself);
    vis.visit_path(&alias.path);
}

pub fn walk_expr<'v, V: Visitor<'v>>(vis: &mut V, expr: &Expr<'v>) {
    match expr.kind {
        ExprKind::Var(path, _) => vis.visit_path_expr(&path),
        ExprKind::Dot(path, _fld) => {
            vis.visit_path_expr(&path);
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
        ExprKind::Alias(alias_reft, args) => {
            vis.visit_alias_reft(&alias_reft);
            walk_list!(vis, visit_expr, args);
        }
        ExprKind::IfThenElse(e1, e2, e3) => {
            vis.visit_expr(e1);
            vis.visit_expr(e2);
            vis.visit_expr(e3);
        }
    }
}
