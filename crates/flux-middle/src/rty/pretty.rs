use std::{fmt, iter};

use expr::{FieldBind, pretty::aggregate_nested};
use rustc_type_ir::DebruijnIndex;
use ty::{UnevaluatedConst, ValTree, region_to_string};

use super::*;
use crate::pretty::*;

impl Pretty for ClauseKind {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ClauseKind::Trait(pred) => w!(cx, f, "Trait ({:?})", ^pred),
            ClauseKind::Projection(pred) => w!(cx, f, "Projection ({:?})", ^pred),
            ClauseKind::RegionOutlives(pred) => {
                w!(cx, f, "Outlives ({:?}, {:?})", &pred.0, &pred.1)
            }
            ClauseKind::TypeOutlives(pred) => w!(cx, f, "Outlives ({:?}, {:?})", &pred.0, &pred.1),
            ClauseKind::ConstArgHasType(c, ty) => w!(cx, f, "ConstArgHasType ({:?}, {:?})", c, ty),
        }
    }
}

impl Pretty for BoundRegionKind {
    fn fmt(&self, _cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BoundRegionKind::Anon => w!(cx, f, "'<annon>"),
            BoundRegionKind::Named(_, sym) => w!(cx, f, "{sym}"),
            BoundRegionKind::ClosureEnv => w!(cx, f, "'<env>"),
        }
    }
}

impl<T> Pretty for Binder<T>
where
    T: Pretty,
{
    default fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        cx.with_bound_vars(self.vars(), || {
            if !self.vars().is_empty() {
                cx.fmt_bound_vars(true, "for<", self.vars(), "> ", f)?;
            }
            w!(cx, f, "{:?}", self.skip_binder_ref())
        })
    }
}

impl<T: Pretty> std::fmt::Debug for Binder<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        pprint_with_default_cx(f, self, None)
    }
}

impl Pretty for PolyFnSig {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let vars = self.vars();
        cx.with_bound_vars(vars, || {
            if !vars.is_empty() {
                cx.fmt_bound_vars(true, "for<", vars, "> ", f)?;
            }
            w!(cx, f, "{:?}", self.skip_binder_ref())
        })
    }
}

impl Pretty for SortCtor {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SortCtor::Set => w!(cx, f, "Set"),
            SortCtor::Map => w!(cx, f, "Map"),
            SortCtor::User { name, .. } => w!(cx, f, "{}", ^name),
            SortCtor::Adt(adt_sort_def) => {
                w!(cx, f, "{:?}", adt_sort_def.did())
            }
        }
    }
}

impl Pretty for SortInfer {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SortInfer::SortVar(svid) => w!(cx, f, "{:?}", ^svid),
            SortInfer::NumVar(nvid) => w!(cx, f, "{:?}", ^nvid),
        }
    }
}

impl Pretty for Sort {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sort::Bool => w!(cx, f, "bool"),
            Sort::Int => w!(cx, f, "int"),
            Sort::Real => w!(cx, f, "real"),
            Sort::Str => w!(cx, f, "str"),
            Sort::Char => w!(cx, f, "char"),
            Sort::BitVec(size) => w!(cx, f, "bitvec({:?})", size),
            Sort::Loc => w!(cx, f, "loc"),
            Sort::Var(n) => w!(cx, f, "@{}", ^n.index()),
            Sort::Func(sort) => w!(cx, f, "{:?}", sort),
            Sort::Tuple(sorts) => {
                if let [sort] = &sorts[..] {
                    w!(cx, f, "({:?},)", sort)
                } else {
                    w!(cx, f, "({:?})", join!(", ", sorts))
                }
            }
            Sort::Alias(kind, alias_ty) => {
                fmt_alias_ty(cx, f, *kind, alias_ty)?;
                w!(cx, f, "::sort")
            }
            Sort::App(ctor, sorts) => {
                if sorts.is_empty() {
                    w!(cx, f, "{:?}", ctor)
                } else {
                    w!(cx, f, "{:?}<{:?}>", ctor, join!(", ", sorts))
                }
            }
            Sort::Param(param_ty) => w!(cx, f, "{}::sort", ^param_ty),
            Sort::Infer(svar) => w!(cx, f, "{:?}", svar),
            Sort::Err => w!(cx, f, "err"),
        }
    }
}

impl Pretty for SortArg {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SortArg::Sort(sort) => w!(cx, f, "{:?}", sort),
            SortArg::BvSize(size) => w!(cx, f, "{:?}", size),
        }
    }
}

impl Pretty for BvSize {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BvSize::Fixed(size) => w!(cx, f, "{}", ^size),
            BvSize::Param(param) => w!(cx, f, "{:?}", ^param),
            BvSize::Infer(size_vid) => w!(cx, f, "{:?}", ^size_vid),
        }
    }
}

impl Pretty for FuncSort {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.inputs() {
            [input] => {
                w!(cx, f, "{:?} -> {:?}", input, self.output())
            }
            inputs => {
                w!(cx, f,
                   "({}) -> {:?}",
                   ^inputs
                       .iter()
                       .format_with(", ", |s, f| f(&format_args_cx!(cx, "{:?}", s))),
                   self.output()
                )
            }
        }
    }
}

impl Pretty for PolyFuncSort {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.params.is_empty() {
            w!(cx, f, "{:?}", &self.fsort)
        } else {
            w!(cx, f, "for<{}> {:?}", ^self.params.len(), &self.fsort)
        }
    }
}

impl Pretty for FnSig {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.requires.is_empty() {
            w!(cx, f, "[{:?}] ", join!(", ", &self.requires))?;
        }
        w!(cx, f, "fn({:?}) -> {:?}", join!(", ", &self.inputs), &self.output)?;

        Ok(())
    }
}

impl Pretty for Binder<FnOutput> {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let vars = self.vars();
        cx.with_bound_vars(vars, || {
            if !vars.is_empty() {
                cx.fmt_bound_vars(true, "exists<", vars, "> ", f)?;
            }
            w!(cx, f, "{:?}", self.skip_binder_ref())
        })
    }
}

impl Pretty for FnOutput {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        w!(cx, f, "{:?}", &self.ret)?;
        if !self.ensures.is_empty() {
            w!(cx, f, "; [{:?}]", join!(", ", &self.ensures))?;
        }
        Ok(())
    }
}

impl Pretty for Ensures {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ensures::Type(loc, ty) => w!(cx, f, "{:?}: {:?}", ^loc, ty),
            Ensures::Pred(e) => w!(cx, f, "{:?}", e),
        }
    }
}

impl Pretty for SubsetTy {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.pred.is_trivially_true() {
            w!(cx, f, "{:?}[{:?}]", &self.bty, &self.idx)
        } else {
            w!(cx, f, "{{ {:?}[{:?}] | {:?} }}", &self.bty, &self.idx, &self.pred)
        }
    }
}

// This is a trick to avoid pretty printing `S [S { x: 10, y: 20}]`
// and instead just print `S[{x: 10, y: 20}]` for struct-valued indices.
struct IdxFmt(Expr);

impl PrettyNested for IdxFmt {
    fn fmt_nested(&self, cx: &PrettyCx) -> Result<NestedString, fmt::Error> {
        let kind = self.0.kind();
        match kind {
            ExprKind::Ctor(ctor, flds) => aggregate_nested(cx, ctor, flds, false),
            ExprKind::Tuple(flds) if flds.is_empty() => {
                Ok(NestedString { text: String::new(), key: None, children: None })
            }
            _ => self.0.fmt_nested(cx),
        }
    }
}

impl Pretty for IdxFmt {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let e = if cx.simplify_exprs { self.0.simplify() } else { self.0.clone() };
        if let ExprKind::Ctor(ctor, flds) = e.kind()
            && let Some(adt_sort_def) = cx.adt_sort_def_of(ctor.def_id())
            && let Some(variant) = adt_sort_def.opt_struct_variant()
        {
            let fields = iter::zip(variant.field_names(), flds)
                .map(|(name, value)| FieldBind { name: *name, value: value.clone() })
                .collect_vec();
            w!(cx, f, "{{ {:?} }}", join!(", ", fields))
        } else {
            w!(cx, f, "{:?}", e)
        }
    }
}

impl Pretty for Ty {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            TyKind::Indexed(bty, idx) => {
                if cx.hide_refinements {
                    w!(cx, f, "{:?}", bty)?;
                    return Ok(());
                }
                if idx.is_unit() {
                    w!(cx, f, "{:?}", bty)?;
                } else {
                    w!(cx, f, "{:?}[{:?}]", parens!(bty, !bty.is_atom()), IdxFmt(idx.clone()))?;
                }
                Ok(())
            }
            TyKind::Exists(ty_ctor) => {
                let vars = ty_ctor.vars();
                cx.with_bound_vars(vars, || {
                    if cx.hide_refinements {
                        w!(cx, f, "{:?}", ty_ctor.skip_binder_ref())
                    } else {
                        cx.fmt_bound_vars(false, "∃", vars, ". ", f)?;
                        w!(cx, f, "{:?}", ty_ctor.skip_binder_ref())
                    }
                })
            }
            TyKind::Uninit => w!(cx, f, "uninit"),
            TyKind::StrgRef(re, loc, ty) => w!(cx, f, "&{:?} strg <{:?}: {:?}>", re, loc, ty),
            TyKind::Ptr(pk, loc) => w!(cx, f, "ptr({:?}, {:?})", pk, loc),
            TyKind::Discr(adt_def, place) => w!(cx, f, "discr({:?}, {:?})", adt_def.did(), ^place),
            TyKind::Constr(pred, ty) => {
                if cx.hide_refinements {
                    w!(cx, f, "{:?}", ty)
                } else {
                    w!(cx, f, "{{ {:?} | {:?} }}", ty, pred)
                }
            }
            TyKind::Param(param_ty) => w!(cx, f, "{}", ^param_ty),
            TyKind::Downcast(adt, .., variant_idx, fields) => {
                // base-name
                w!(cx, f, "{:?}", adt.did())?;
                // variant-name: if it is not a struct
                if !adt.is_struct() {
                    w!(cx, f, "::{}", ^adt.variant(*variant_idx).name)?;
                }
                // fields: use curly-braces + names for structs, otherwise use parens
                if adt.is_struct() {
                    let field_binds = iter::zip(&adt.variant(*variant_idx).fields, fields)
                        .map(|(field_def, value)| FieldBind { name: field_def.name, value });
                    w!(cx, f, " {{ {:?} }}", join!(", ", field_binds))?;
                } else if !fields.is_empty() {
                    w!(cx, f, "({:?})", join!(", ", fields))?;
                }
                Ok(())
            }
            TyKind::Blocked(ty) => w!(cx, f, "†{:?}", ty),
            TyKind::Infer(ty_vid) => {
                w!(cx, f, "{ty_vid:?}")
            }
        }
    }

    fn default_cx(tcx: TyCtxt) -> PrettyCx {
        PrettyCx::default(tcx).kvar_args(KVarArgs::Hide)
    }
}

impl Pretty for PtrKind {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PtrKind::Mut(re) => {
                w!(cx, f, "mut")?;
                if !cx.hide_regions {
                    w!(cx, f, "[{:?}]", re)?;
                }
                Ok(())
            }
            PtrKind::Box => w!(cx, f, "box"),
        }
    }
}

impl Pretty for List<Ty> {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let [ty] = &self[..] {
            w!(cx, f, "({:?},)", ty)
        } else {
            w!(cx, f, "({:?})", join!(", ", self))
        }
    }
}

impl Pretty for ExistentialPredicate {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExistentialPredicate::Trait(trait_ref) => w!(cx, f, "{:?}", trait_ref),
            ExistentialPredicate::Projection(proj) => w!(cx, f, "({:?})", proj),
            ExistentialPredicate::AutoTrait(def_id) => w!(cx, f, "{:?}", def_id),
        }
    }
}

impl Pretty for ExistentialTraitRef {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        w!(cx, f, "{:?}", self.def_id)?;
        if !self.args.is_empty() {
            w!(cx, f, "<{:?}>", join!(", ", &self.args))?;
        }
        Ok(())
    }
}

impl Pretty for ExistentialProjection {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        w!(cx, f, "{:?}", self.def_id)?;
        if !self.args.is_empty() {
            w!(cx, f, "<{:?}>", join!(", ", &self.args))?;
        }
        w!(cx, f, " = {:?}", &self.term)
    }
}

impl Pretty for BaseTy {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BaseTy::Int(int_ty) => w!(cx, f, "{}", ^int_ty.name_str()),
            BaseTy::Uint(uint_ty) => w!(cx, f, "{}", ^uint_ty.name_str()),
            BaseTy::Bool => w!(cx, f, "bool"),
            BaseTy::Str => w!(cx, f, "str"),
            BaseTy::Char => w!(cx, f, "char"),
            BaseTy::Adt(adt_def, args) => {
                w!(cx, f, "{:?}", adt_def.did())?;
                let args = args
                    .iter()
                    .filter(|arg| !cx.hide_regions || !matches!(arg, GenericArg::Lifetime(_)))
                    .collect_vec();
                if !args.is_empty() {
                    w!(cx, f, "<{:?}>", join!(", ", args))?;
                }
                Ok(())
            }
            BaseTy::FnDef(def_id, args) => {
                w!(cx, f, "FnDef({:?}[{:?}])", def_id, join!(", ", args))
            }
            BaseTy::Param(param) => w!(cx, f, "{}", ^param),
            BaseTy::Float(float_ty) => w!(cx, f, "{}", ^float_ty.name_str()),
            BaseTy::Slice(ty) => w!(cx, f, "[{:?}]", ty),
            BaseTy::RawPtr(ty, Mutability::Mut) => w!(cx, f, "*mut {:?}", ty),
            BaseTy::RawPtr(ty, Mutability::Not) => w!(cx, f, "*const {:?}", ty),
            BaseTy::Ref(re, ty, mutbl) => {
                w!(cx, f, "&")?;
                if !cx.hide_regions {
                    w!(cx, f, "{:?} ", re)?;
                }
                w!(cx, f, "{}{:?}",  ^mutbl.prefix_str(), ty)
            }
            BaseTy::FnPtr(poly_fn_sig) => {
                w!(cx, f, "{:?}", poly_fn_sig)
            }
            BaseTy::Tuple(tys) => {
                if let [ty] = &tys[..] {
                    w!(cx, f, "({:?},)", ty)
                } else {
                    w!(cx, f, "({:?})", join!(", ", tys))
                }
            }
            BaseTy::Alias(kind, alias_ty) => fmt_alias_ty(cx, f, *kind, alias_ty),
            BaseTy::Array(ty, c) => w!(cx, f, "[{:?}; {:?}]", ty, ^c),
            BaseTy::Never => w!(cx, f, "!"),
            BaseTy::Closure(did, args, _) => {
                w!(cx, f, "{:?}<{:?}>", did, args)
            }
            BaseTy::Coroutine(did, resume_ty, upvars) => {
                w!(cx, f, "Coroutine({:?}, {:?})", did, resume_ty)?;
                if !upvars.is_empty() {
                    w!(cx, f, "<{:?}>", join!(", ", upvars))?;
                }
                Ok(())
            }
            BaseTy::Dynamic(preds, re) => {
                w!(cx, f, "dyn {:?} + {:?}", join!(" + ", preds), re)
            }
            BaseTy::Infer(ty_vid) => {
                w!(cx, f, "{ty_vid:?}")
            }
        }
    }
}

fn fmt_alias_ty(
    cx: &PrettyCx,
    f: &mut fmt::Formatter<'_>,
    kind: AliasKind,
    alias_ty: &AliasTy,
) -> fmt::Result {
    match kind {
        AliasKind::Weak => {
            w!(cx, f, "{:?}", alias_ty.def_id)?;
            if !alias_ty.args.is_empty() {
                w!(cx, f, "<{:?}>", join!(", ", &alias_ty.args))?;
            }
        }
        AliasKind::Projection => {
            let assoc_name = cx.tcx().item_name(alias_ty.def_id);
            let trait_ref = cx.tcx().parent(alias_ty.def_id);
            let trait_generic_count = cx.tcx().generics_of(trait_ref).count() - 1;

            let [self_ty, args @ ..] = &alias_ty.args[..] else {
                return w!(cx, f, "<alias_ty>");
            };

            w!(cx, f, "<{:?} as {:?}", self_ty, trait_ref)?;

            let trait_generics = &args[..trait_generic_count];
            if !trait_generics.is_empty() {
                w!(cx, f, "<{:?}>", join!(", ", trait_generics))?;
            }
            w!(cx, f, ">::{}", ^assoc_name)?;

            let assoc_generics = &args[trait_generic_count..];
            if !assoc_generics.is_empty() {
                w!(cx, f, "<{:?}>", join!(", ", assoc_generics))?;
            }
        }
        AliasKind::Opaque => {
            w!(cx, f, "{:?}", alias_ty.def_id)?;
            if !alias_ty.args.is_empty() {
                w!(cx, f, "<{:?}>", join!(", ", &alias_ty.args))?;
            }
            if !alias_ty.refine_args.is_empty() {
                w!(cx, f, "⟨{:?}⟩", join!(", ", &alias_ty.refine_args))?;
            }
        }
    }
    Ok(())
}

impl Pretty for ValTree {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ValTree::Leaf(v) => w!(cx, f, "Leaf({v:?})"),
            ValTree::Branch(children) => {
                w!(cx, f, "Branch([{:?}])", join!(", ", children))
            }
        }
    }
}
impl Pretty for UnevaluatedConst {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        w!(cx, f, "UnevaluatedConst({:?}[...])", self.def)
    }
}

impl Pretty for Const {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            ConstKind::Param(p) => w!(cx, f, "{}", ^p.name.as_str()),
            ConstKind::Value(_, v) => w!(cx, f, "{v:?}"),
            ConstKind::Infer(infer_const) => w!(cx, f, "{:?}", ^infer_const),
            ConstKind::Unevaluated(uneval_const) => w!(cx, f, "{:?}", uneval_const),
        }
    }
}

impl Pretty for GenericArg {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            GenericArg::Ty(ty) => w!(cx, f, "{:?}", ty),
            GenericArg::Base(ctor) => {
                cx.with_bound_vars(ctor.vars(), || {
                    cx.fmt_bound_vars(false, "λ", ctor.vars(), ". ", f)?;
                    w!(cx, f, "{:?}", ctor.skip_binder_ref())
                })
            }
            GenericArg::Lifetime(re) => w!(cx, f, "{:?}", re),
            GenericArg::Const(c) => w!(cx, f, "{:?}", c),
        }
    }
}

impl Pretty for VariantSig {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        w!(cx, f, "({:?}) => {:?}", join!(", ", self.fields()), &self.idx)
    }
}

impl Pretty for Region {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        w!(cx, f, "{}", ^region_to_string(*self))
    }
}

impl Pretty for DebruijnIndex {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        w!(cx, f, "^{}", ^self.as_usize())
    }
}

impl_debug_with_default_cx!(
    Ensures,
    Sort,
    Ty => "ty",
    BaseTy,
    FnSig,
    GenericArg => "generic_arg",
    VariantSig,
    PtrKind,
    FuncSort,
    SortCtor,
    SubsetTy,
    BvSize,
    ExistentialPredicate,
);

impl PrettyNested for SubsetTy {
    fn fmt_nested(&self, cx: &PrettyCx) -> Result<NestedString, fmt::Error> {
        let bty_d = self.bty.fmt_nested(cx)?;
        let idx_d = IdxFmt(self.idx.clone()).fmt_nested(cx)?;
        if self.pred.is_trivially_true() {
            let text = format!("{}[{}]", bty_d.text, idx_d.text);
            let children = float_children(vec![bty_d.children, idx_d.children]);
            Ok(NestedString { text, children, key: None })
        } else {
            let pred_d = self.pred.fmt_nested(cx)?;
            let text = format!("{{ {}[{}] | {} }}", bty_d.text, idx_d.text, pred_d.text);
            let children = float_children(vec![bty_d.children, idx_d.children, pred_d.children]);
            Ok(NestedString { text, children, key: None })
        }
    }
}

impl PrettyNested for GenericArg {
    fn fmt_nested(&self, cx: &PrettyCx) -> Result<NestedString, fmt::Error> {
        match self {
            GenericArg::Ty(ty) => ty.fmt_nested(cx),
            GenericArg::Base(ctor) => {
                nested_with_bound_vars(cx, "λ", ctor.vars(), |prefix| {
                    let ctor_d = ctor.skip_binder_ref().fmt_nested(cx)?;
                    let text = format!("{}{}", prefix, ctor_d.text);
                    Ok(NestedString { text, children: ctor_d.children, key: None })
                })
            }
            GenericArg::Lifetime(..) | GenericArg::Const(..) => debug_nested(cx, self),
        }
    }
}

impl PrettyNested for BaseTy {
    fn fmt_nested(&self, cx: &PrettyCx) -> Result<NestedString, fmt::Error> {
        match self {
            BaseTy::Int(..)
            | BaseTy::Uint(..)
            | BaseTy::Bool
            | BaseTy::Str
            | BaseTy::Char
            | BaseTy::Float(..)
            | BaseTy::Param(..)
            | BaseTy::Never
            | BaseTy::FnPtr(..)
            | BaseTy::FnDef(..)
            | BaseTy::Alias(..)
            | BaseTy::Closure(..)
            | BaseTy::Coroutine(..)
            | BaseTy::Dynamic(..)
            | BaseTy::Infer(..) => {
                let text = format_cx!(cx, "{:?}", self);
                Ok(NestedString { text, children: None, key: None })
            }
            BaseTy::Slice(ty) => {
                let ty_d = ty.fmt_nested(cx)?;
                let text = format!("[{}]", ty_d.text);
                Ok(NestedString { text, children: ty_d.children, key: None })
            }
            BaseTy::Array(ty, c) => {
                let ty_d = ty.fmt_nested(cx)?;
                let text = format_cx!(cx, "[{:?}; {:?}]", ty_d.text, c);
                Ok(NestedString { text, children: ty_d.children, key: None })
            }
            BaseTy::RawPtr(ty, Mutability::Mut) => {
                let ty_d = ty.fmt_nested(cx)?;
                let text = format!("*mut {}", ty_d.text);
                Ok(NestedString { text, children: ty_d.children, key: None })
            }
            BaseTy::RawPtr(ty, Mutability::Not) => {
                let ty_d = ty.fmt_nested(cx)?;
                let text = format!("*const {}", ty_d.text);
                Ok(NestedString { text, children: ty_d.children, key: None })
            }
            BaseTy::Ref(_, ty, mutbl) => {
                let ty_d = ty.fmt_nested(cx)?;
                let text = format!("&{} {}", mutbl.prefix_str(), ty_d.text);
                Ok(NestedString { text, children: ty_d.children, key: None })
            }
            BaseTy::Tuple(tys) => {
                let mut texts = vec![];
                let mut kidss = vec![];
                for ty in tys {
                    let ty_d = ty.fmt_nested(cx)?;
                    texts.push(ty_d.text);
                    kidss.push(ty_d.children);
                }
                let text = if let [text] = &texts[..] {
                    format!("({},)", text)
                } else {
                    format!("({})", texts.join(", "))
                };
                let children = float_children(kidss);
                Ok(NestedString { text, children, key: None })
            }
            BaseTy::Adt(adt_def, args) => {
                let mut texts = vec![];
                let mut kidss = vec![];
                for arg in args {
                    let arg_d = arg.fmt_nested(cx)?;
                    texts.push(arg_d.text);
                    kidss.push(arg_d.children);
                }
                let args_str = if !args.is_empty() {
                    format!("<{}>", texts.join(", "))
                } else {
                    String::new()
                };
                let text = format_cx!(cx, "{:?}{:?}", adt_def.did(), args_str);
                let children = float_children(kidss);
                Ok(NestedString { text, children, key: None })
            }
        }
    }
}

pub fn nested_with_bound_vars(
    cx: &PrettyCx,
    left: &str,
    vars: &[BoundVariableKind],
    f: impl FnOnce(String) -> Result<NestedString, fmt::Error>,
) -> Result<NestedString, fmt::Error> {
    let mut buffer = String::new();
    cx.with_bound_vars(vars, || {
        if !vars.is_empty() {
            cx.fmt_bound_vars(false, left, vars, ". ", &mut buffer)?;
        }
        f(buffer)
    })
}

impl PrettyNested for Ty {
    fn fmt_nested(&self, cx: &PrettyCx) -> Result<NestedString, fmt::Error> {
        match self.kind() {
            TyKind::Indexed(bty, idx) => {
                let bty_d = bty.fmt_nested(cx)?;
                let idx_d = IdxFmt(idx.clone()).fmt_nested(cx)?;
                let text = if idx_d.text.is_empty() {
                    bty_d.text
                } else {
                    format!("{}[{}]", bty_d.text, idx_d.text)
                };
                let children = float_children(vec![bty_d.children, idx_d.children]);
                Ok(NestedString { text, children, key: None })
            }
            TyKind::Exists(ty_ctor) => {
                nested_with_bound_vars(cx, "∃", ty_ctor.vars(), |exi_str| {
                    let ty_ctor_d = ty_ctor.skip_binder_ref().fmt_nested(cx)?;
                    let text = format!("{}{}", exi_str, ty_ctor_d.text);
                    Ok(NestedString { text, children: ty_ctor_d.children, key: None })
                })
            }
            TyKind::Constr(expr, ty) => {
                let expr_d = expr.fmt_nested(cx)?;
                let ty_d = ty.fmt_nested(cx)?;
                let text = format!("{{ {} | {} }}", ty_d.text, expr_d.text);
                let children = float_children(vec![expr_d.children, ty_d.children]);
                Ok(NestedString { text, children, key: None })
            }
            TyKind::StrgRef(re, loc, ty) => {
                let ty_d = ty.fmt_nested(cx)?;
                let text = format!("&{:?} strg <{:?}: {}>", re, loc, ty_d.text);
                Ok(NestedString { text, children: ty_d.children, key: None })
            }
            TyKind::Blocked(ty) => {
                let ty_d = ty.fmt_nested(cx)?;
                let text = format!("†{}", ty_d.text);
                Ok(NestedString { text, children: ty_d.children, key: None })
            }
            TyKind::Downcast(adt, .., variant_idx, fields) => {
                let is_struct = adt.is_struct();
                let mut text = format_cx!(cx, "{:?}", adt.did());
                if !is_struct {
                    text.push_str(&format!("::{}", adt.variant(*variant_idx).name));
                }
                if is_struct {
                    text.push_str("{..}");
                } else {
                    text.push_str("(..)");
                }
                let keys: Vec<String> = if is_struct {
                    adt.variant(*variant_idx)
                        .fields
                        .iter()
                        .map(|f| f.name.to_string())
                        .collect()
                } else {
                    (0..fields.len()).map(|i| format!("{}", i)).collect()
                };
                let mut children = vec![];
                for (key, field) in keys.into_iter().zip(fields) {
                    let field_d = field.fmt_nested(cx)?;
                    children.push(NestedString { key: Some(key), ..field_d });
                }
                Ok(NestedString { text, children: Some(children), key: None })
            }
            TyKind::Param(..)
            | TyKind::Uninit
            | TyKind::Ptr(..)
            | TyKind::Discr(..)
            | TyKind::Infer(..) => {
                let text = format!("{:?}", self);
                Ok(NestedString { text, children: None, key: None })
            }
        }
    }
}
