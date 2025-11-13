use super::{
    AliasReft, AssocItemConstraint, AssocItemConstraintKind, BaseTy, BaseTyKind, Ensures, EnumDef,
    Expr, ExprKind, FieldDef, FieldExpr, FluxItem, FnDecl, FnOutput, FnSig, ForeignItem,
    ForeignItemKind, FuncSort, GenericArg, GenericBound, Generics, Impl, ImplAssocReft, ImplItem,
    ImplItemKind, Item, ItemKind, Lifetime, Lit, OpaqueTy, OwnerNode, Path, PathExpr, PathSegment,
    PolyFuncSort, PolyTraitRef, QPath, Qualifier, RefineParam, Requires, Sort, SortPath, SpecFunc,
    StructDef, TraitAssocReft, TraitItem, TraitItemKind, Ty, TyAlias, TyKind, VariantDef,
    VariantRet, WhereBoundPredicate,
};
use crate::fhir::{PrimOpProp, QPathExpr, SortDecl, StructKind};

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
    fn visit_flux_item(&mut self, item: &FluxItem<'v>) {
        walk_flux_item(self, item);
    }

    fn visit_qualifier(&mut self, qualifier: &Qualifier<'v>) {
        walk_qualifier(self, qualifier);
    }

    fn visit_sort_decl(&mut self, sort_decl: &SortDecl) {
        walk_sort_decl(self, sort_decl);
    }

    fn visit_func(&mut self, func: &SpecFunc<'v>) {
        walk_func(self, func);
    }

    fn visit_primop_prop(&mut self, prop: &PrimOpProp<'v>) {
        walk_primop_prop(self, prop);
    }

    fn visit_node(&mut self, node: &OwnerNode<'v>) {
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

    fn visit_foreign_item(&mut self, foreign_item: &ForeignItem<'v>) {
        walk_foreign_item(self, foreign_item);
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

    fn visit_assoc_item_constraint(&mut self, constraint: &AssocItemConstraint<'v>) {
        walk_assoc_item_constraint(self, constraint);
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

    fn visit_expr(&mut self, expr: &Expr<'v>) {
        walk_expr(self, expr);
    }

    fn visit_field_expr(&mut self, expr: &FieldExpr<'v>) {
        walk_field_expr(self, expr);
    }

    fn visit_alias_reft(&mut self, alias_reft: &AliasReft<'v>) {
        walk_alias_reft(self, alias_reft);
    }

    fn visit_literal(&mut self, _lit: &Lit) {}

    fn visit_path_expr(&mut self, _path: &PathExpr<'v>) {}
}

fn walk_sort_decl<'v, V: Visitor<'v>>(_vis: &mut V, _sort_decl: &SortDecl) {}

fn walk_func<'v, V: Visitor<'v>>(vis: &mut V, func: &SpecFunc<'v>) {
    walk_list!(vis, visit_refine_param, func.args);
    vis.visit_sort(&func.sort);
    if let Some(body) = &func.body {
        vis.visit_expr(body);
    }
}

fn walk_primop_prop<'v, V: Visitor<'v>>(vis: &mut V, prop: &PrimOpProp<'v>) {
    walk_list!(vis, visit_refine_param, prop.args);
    vis.visit_expr(&prop.body);
}

fn walk_qualifier<'v, V: Visitor<'v>>(vis: &mut V, qualifier: &Qualifier<'v>) {
    walk_list!(vis, visit_refine_param, qualifier.args);
    vis.visit_expr(&qualifier.expr);
}

fn walk_flux_item<'v, V: Visitor<'v>>(vis: &mut V, item: &FluxItem<'v>) {
    match item {
        FluxItem::Qualifier(qualifier) => {
            vis.visit_qualifier(qualifier);
        }
        FluxItem::Func(func) => {
            vis.visit_func(func);
        }
        FluxItem::PrimOpProp(prop) => {
            vis.visit_primop_prop(prop);
        }
        FluxItem::SortDecl(sort_decl) => {
            vis.visit_sort_decl(sort_decl);
        }
    }
}

pub fn walk_impl<'v, V: Visitor<'v>>(vis: &mut V, impl_: &Impl<'v>) {
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
    let FieldDef { ty, lifted: _ } = field;
    vis.visit_ty(ty);
}

pub fn walk_variant_ret<'v, V: Visitor<'v>>(vis: &mut V, ret: &VariantRet<'v>) {
    let VariantRet { idx, enum_id: _ } = ret;
    vis.visit_expr(idx);
}

pub fn walk_ty_alias<'v, V: Visitor<'v>>(vis: &mut V, ty_alias: &TyAlias<'v>) {
    if let Some(index) = &ty_alias.index {
        vis.visit_refine_param(index);
    }
    vis.visit_ty(&ty_alias.ty);
}

pub fn walk_opaque_ty<'v, V: Visitor<'v>>(vis: &mut V, opaque_ty: &OpaqueTy<'v>) {
    walk_list!(vis, visit_generic_bound, opaque_ty.bounds);
}

pub fn walk_generic_bound<'v, V: Visitor<'v>>(vis: &mut V, bound: &GenericBound<'v>) {
    match bound {
        GenericBound::Trait(trait_ref) => vis.visit_poly_trait_ref(trait_ref),
        GenericBound::Outlives(_) => {}
    }
}

pub fn walk_poly_trait_ref<'v, V: Visitor<'v>>(vis: &mut V, trait_ref: &PolyTraitRef<'v>) {
    walk_list!(vis, visit_refine_param, trait_ref.refine_params);
    vis.visit_path(&trait_ref.trait_ref);
}

pub fn walk_node<'v, V: Visitor<'v>>(vis: &mut V, node: &OwnerNode<'v>) {
    match node {
        OwnerNode::Item(item) => vis.visit_item(item),
        OwnerNode::TraitItem(trait_item) => vis.visit_trait_item(trait_item),
        OwnerNode::ImplItem(impl_item) => vis.visit_impl_item(impl_item),
        OwnerNode::ForeignItem(foreign_item) => vis.visit_foreign_item(foreign_item),
    }
}

pub fn walk_item<'v, V: Visitor<'v>>(vis: &mut V, item: &Item<'v>) {
    vis.visit_generics(&item.generics);
    match &item.kind {
        ItemKind::Enum(enum_def) => vis.visit_enum_def(enum_def),
        ItemKind::Struct(struct_def) => vis.visit_struct_def(struct_def),
        ItemKind::TyAlias(ty_alias) => vis.visit_ty_alias(ty_alias),
        ItemKind::Trait(trait_) => {
            walk_list!(vis, visit_trait_assoc_reft, trait_.assoc_refinements);
        }
        ItemKind::Impl(impl_) => vis.visit_impl(impl_),
        ItemKind::Fn(fn_sig) => vis.visit_fn_sig(fn_sig),
        ItemKind::Const(info) => {
            if let Some(expr) = info {
                vis.visit_expr(expr);
            }
        }
    }
}

pub fn walk_trait_item<'v, V: Visitor<'v>>(vis: &mut V, trait_item: &TraitItem<'v>) {
    vis.visit_generics(&trait_item.generics);
    match &trait_item.kind {
        TraitItemKind::Fn(fn_sig) => vis.visit_fn_sig(fn_sig),
        TraitItemKind::Type => {}
        TraitItemKind::Const => {}
    }
}

pub fn walk_impl_item<'v, V: Visitor<'v>>(vis: &mut V, impl_item: &ImplItem<'v>) {
    vis.visit_generics(&impl_item.generics);
    match &impl_item.kind {
        ImplItemKind::Fn(fn_sig) => vis.visit_fn_sig(fn_sig),
        ImplItemKind::Const => {}
        ImplItemKind::Type => {}
    }
}

pub fn walk_foreign_item<'v, V: Visitor<'v>>(vis: &mut V, impl_item: &ForeignItem<'v>) {
    match &impl_item.kind {
        ForeignItemKind::Fn(fn_sig, generics) => {
            vis.visit_generics(generics);
            vis.visit_fn_sig(fn_sig);
        }
    }
}

pub fn walk_trait_assoc_reft<'v, V: Visitor<'v>>(vis: &mut V, assoc_reft: &TraitAssocReft<'v>) {
    walk_list!(vis, visit_refine_param, assoc_reft.params);
    vis.visit_sort(&assoc_reft.output);
    if let Some(expr) = &assoc_reft.body {
        vis.visit_expr(expr);
    }
}

pub fn walk_impl_assoc_reft<'v, V: Visitor<'v>>(vis: &mut V, assoc_reft: &ImplAssocReft<'v>) {
    walk_list!(vis, visit_refine_param, assoc_reft.params);
    vis.visit_sort(&assoc_reft.output);
    vis.visit_expr(&assoc_reft.body);
}

pub fn walk_generics<'v, V: Visitor<'v>>(vis: &mut V, generics: &Generics<'v>) {
    walk_list!(vis, visit_refine_param, generics.refinement_params);
    if let Some(predicates) = generics.predicates {
        walk_list!(vis, visit_where_predicate, predicates);
    }
}

pub fn walk_where_predicate<'v, V: Visitor<'v>>(vis: &mut V, predicate: &WhereBoundPredicate<'v>) {
    vis.visit_ty(&predicate.bounded_ty);
    walk_list!(vis, visit_generic_bound, predicate.bounds);
}

pub fn walk_fn_sig<'v, V: Visitor<'v>>(vis: &mut V, sig: &FnSig<'v>) {
    vis.visit_fn_decl(sig.decl);
}

pub fn walk_fn_decl<'v, V: Visitor<'v>>(vis: &mut V, decl: &FnDecl<'v>) {
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
        GenericArg::Const(_) | GenericArg::Infer => {}
    }
}

pub fn walk_ty<'v, V: Visitor<'v>>(vis: &mut V, ty: &Ty<'v>) {
    match ty.kind {
        TyKind::BaseTy(bty) => vis.visit_bty(&bty),
        TyKind::Indexed(bty, idx) => {
            vis.visit_bty(&bty);
            vis.visit_expr(&idx);
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
        TyKind::BareFn(bare_fn) => vis.visit_fn_decl(bare_fn.decl),
        TyKind::Tuple(tys) => {
            walk_list!(vis, visit_ty, tys);
        }
        TyKind::Array(ty, _len) => {
            vis.visit_ty(ty);
        }
        TyKind::RawPtr(ty, _mtblt) => {
            vis.visit_ty(ty);
        }
        TyKind::OpaqueDef(opaque_ty) => {
            vis.visit_opaque_ty(opaque_ty);
        }
        TyKind::TraitObject(poly_traits, lft, _) => {
            walk_list!(vis, visit_poly_trait_ref, poly_traits);
            vis.visit_lifetime(&lft);
        }
        TyKind::Never | TyKind::Infer | TyKind::Err(_) => {}
    }
}

pub fn walk_bty<'v, V: Visitor<'v>>(vis: &mut V, bty: &BaseTy<'v>) {
    match &bty.kind {
        BaseTyKind::Path(path) => vis.visit_qpath(path),
        BaseTyKind::Slice(ty) => vis.visit_ty(ty),
        BaseTyKind::Err(_) => {}
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
    walk_list!(vis, visit_expr, path.refine);
}

pub fn walk_path_segment<'v, V: Visitor<'v>>(vis: &mut V, segment: &PathSegment<'v>) {
    walk_list!(vis, visit_generic_arg, segment.args);
    walk_list!(vis, visit_assoc_item_constraint, segment.constraints);
}

pub fn walk_assoc_item_constraint<'v, V: Visitor<'v>>(
    vis: &mut V,
    constraint: &AssocItemConstraint<'v>,
) {
    match &constraint.kind {
        AssocItemConstraintKind::Equality { term } => {
            vis.visit_ty(term);
        }
    }
}

pub fn walk_sort<'v, V: Visitor<'v>>(vis: &mut V, sort: &Sort<'v>) {
    match sort {
        Sort::Path(path) => vis.visit_sort_path(path),
        Sort::Func(func) => vis.visit_poly_func_sort(func),
        Sort::SortOf(bty) => vis.visit_bty(bty),
        Sort::Loc | Sort::BitVec(_) | Sort::Infer | Sort::Err(_) => {}
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

pub fn walk_alias_reft<'v, V: Visitor<'v>>(vis: &mut V, alias: &AliasReft<'v>) {
    match alias {
        AliasReft::Qualified { qself, trait_, name: _ } => {
            vis.visit_ty(qself);
            vis.visit_path(trait_);
        }
        AliasReft::TypeRelative { qself, name: _ } => {
            vis.visit_ty(qself);
        }
    }
}

pub fn walk_field_expr<'v, V: Visitor<'v>>(vis: &mut V, expr: &FieldExpr<'v>) {
    vis.visit_expr(&expr.expr);
}

pub fn walk_expr<'v, V: Visitor<'v>>(vis: &mut V, expr: &Expr<'v>) {
    match expr.kind {
        ExprKind::Var(qpath) => walk_qpath_expr(vis, qpath),
        ExprKind::Dot(base, _fld) => {
            vis.visit_expr(base);
        }
        ExprKind::Literal(lit) => vis.visit_literal(&lit),
        ExprKind::BinaryOp(_op, e1, e2) => {
            vis.visit_expr(e1);
            vis.visit_expr(e2);
        }
        ExprKind::PrimApp(_op, e1, e2) => {
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
        ExprKind::Abs(refine_params, body) => {
            walk_list!(vis, visit_refine_param, refine_params);
            vis.visit_expr(body);
        }
        ExprKind::Record(exprs) | ExprKind::SetLiteral(exprs) => {
            walk_list!(vis, visit_expr, exprs);
        }
        ExprKind::Constructor(path, exprs, spread) => {
            if let Some(path) = path {
                vis.visit_path_expr(&path);
            }
            walk_list!(vis, visit_field_expr, exprs);
            if let Some(s) = spread {
                vis.visit_expr(&s.expr);
            }
        }
        ExprKind::BoundedQuant(_, param, _, expr) => {
            vis.visit_refine_param(&param);
            vis.visit_expr(expr);
        }
        ExprKind::Block(decls, body) => {
            for decl in decls {
                vis.visit_expr(&decl.init);
                vis.visit_refine_param(&decl.param);
            }
            vis.visit_expr(body);
        }
        ExprKind::Err(_) => {}
    }
}

pub fn walk_qpath_expr<'v, V: Visitor<'v>>(vis: &mut V, qpath: QPathExpr<'v>) {
    match qpath {
        QPathExpr::Resolved(path, _param_kind) => {
            vis.visit_path_expr(&path);
        }
        QPathExpr::TypeRelative(qself, _ident) => vis.visit_ty(qself),
    }
}
