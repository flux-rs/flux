use std::fmt;

use flux_rustc_bridge::ty::region_to_string;
use rustc_type_ir::DebruijnIndex;
use ty::{UnevaluatedConst, ValTree};

use super::*;
use crate::pretty::*;

impl Pretty for ClauseKind {
    fn fmt(&self, _cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(_cx, f);
        match self {
            ClauseKind::FnTrait(pred) => w!("FnTrait ({pred:?})"),
            ClauseKind::Trait(pred) => w!("Trait ({pred:?})"),
            ClauseKind::Projection(pred) => w!("Projection ({pred:?})"),
            ClauseKind::CoroutineOblig(pred) => w!("Projection ({pred:?})"),
            ClauseKind::TypeOutlives(pred) => w!("Outlives ({:?}, {:?})", &pred.0, &pred.1),
            ClauseKind::ConstArgHasType(c, ty) => w!("ConstArgHasType ({:?}, {:?})", c, ty),
        }
    }
}

impl Pretty for BoundRegionKind {
    fn fmt(&self, _cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(cx, f);
        match self {
            BoundRegionKind::BrAnon => w!("'<annon>"),
            BoundRegionKind::BrNamed(_, sym) => w!("{sym}"),
            BoundRegionKind::BrEnv => w!("'<env>"),
        }
    }
}

impl<T> Pretty for Binder<T>
where
    T: Pretty,
{
    default fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(cx, f);
        cx.with_bound_vars(self.vars(), || {
            if !self.vars().is_empty() {
                cx.fmt_bound_vars(true, "for<", self.vars(), "> ", f)?;
            }
            w!("{:?}", self.skip_binder_ref())
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
        define_scoped!(cx, f);
        let vars = self.vars();
        cx.with_bound_vars(vars, || {
            if !vars.is_empty() {
                cx.fmt_bound_vars(true, "for<", vars, "> ", f)?;
            }
            w!("{:?}", self.skip_binder_ref())
        })
    }
}

impl Pretty for SortCtor {
    fn fmt(&self, _cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(_cx, f);
        match self {
            SortCtor::Set => w!("Set"),
            SortCtor::Map => w!("Map"),
            SortCtor::User { name, .. } => w!("{}", ^name),
            SortCtor::Adt(adt_sort_def) => {
                w!("{:?}", adt_sort_def.did())
            }
        }
    }
}

impl Pretty for SortInfer {
    fn fmt(&self, _cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(cx, f);
        match self {
            SortInfer::SortVar(svid) => w!("{:?}", ^svid),
            SortInfer::NumVar(nvid) => w!("{:?}", ^nvid),
        }
    }
}

impl Pretty for Sort {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(cx, f);
        match self {
            Sort::Bool => w!("bool"),
            Sort::Int => w!("int"),
            Sort::Real => w!("real"),
            Sort::Str => w!("str"),
            Sort::BitVec(size) => w!("bitvec({:?})", size),
            Sort::Loc => w!("loc"),
            Sort::Var(n) => w!("@{}", ^n.index()),
            Sort::Func(sort) => w!("{:?}", sort),
            Sort::Tuple(sorts) => {
                if let [sort] = &sorts[..] {
                    w!("({:?},)", sort)
                } else {
                    w!("({:?})", join!(", ", sorts))
                }
            }
            Sort::App(ctor, sorts) => {
                if sorts.is_empty() {
                    w!("{:?}", ctor)
                } else {
                    w!("{:?}<{:?}>", ctor, join!(", ", sorts))
                }
            }
            Sort::Param(param_ty) => w!("{}::sort", ^param_ty),
            Sort::Infer(svar) => w!("{:?}", svar),
            Sort::Err => w!("err"),
        }
    }
}

impl Pretty for SortArg {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(cx, f);
        match self {
            SortArg::Sort(sort) => w!("{:?}", sort),
            SortArg::BvSize(size) => w!("{:?}", size),
        }
    }
}

impl Pretty for BvSize {
    fn fmt(&self, _cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(cx, f);
        match self {
            BvSize::Fixed(size) => w!("{}", ^size),
            BvSize::Param(param) => w!("{:?}", ^param),
            BvSize::Infer(size_vid) => w!("{:?}", ^size_vid),
        }
    }
}

impl Pretty for FuncSort {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(cx, f);
        match self.inputs() {
            [input] => {
                w!(f, "{:?} -> {:?}", input, self.output())
            }
            inputs => {
                w!(f,
                   "({}) -> {:?}",
                   ^inputs
                       .iter()
                       .format_with(", ", |s, f| f(&format_args_cx!("{:?}", s))),
                   self.output()
                )
            }
        }
    }
}

impl Pretty for PolyFuncSort {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(cx, f);
        if self.params.is_empty() {
            w!("{:?}", &self.fsort)
        } else {
            w!("for<{}> {:?}", ^self.params.len(), &self.fsort)
        }
    }
}

impl Pretty for FnSig {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(cx, f);
        if !self.requires.is_empty() {
            w!("[{:?}] ", join!(", ", &self.requires))?;
        }
        w!("fn({:?}) -> {:?}", join!(", ", &self.inputs), &self.output)?;

        Ok(())
    }

    fn default_cx(tcx: TyCtxt) -> PrettyCx {
        PrettyCx::default(tcx).show_is_binder(true)
    }
}

impl Pretty for Binder<FnOutput> {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(cx, f);
        let vars = self.vars();
        cx.with_bound_vars(vars, || {
            if !vars.is_empty() {
                cx.fmt_bound_vars(true, "exists<", vars, "> ", f)?;
            }
            w!("{:?}", self.skip_binder_ref())
        })
    }
}

impl Pretty for FnOutput {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(cx, f);
        w!("{:?}", &self.ret)?;
        if !self.ensures.is_empty() {
            w!("; [{:?}]", join!(", ", &self.ensures))?;
        }
        Ok(())
    }
}

impl Pretty for Ensures {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(cx, f);
        match self {
            Ensures::Type(loc, ty) => w!("{:?}: {:?}", ^loc, ty),
            Ensures::Pred(e) => w!("{:?}", e),
        }
    }
}

impl Pretty for SubsetTy {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(cx, f);
        if self.pred.is_trivially_true() {
            w!("{:?}[{:?}]", &self.bty, &self.idx)
        } else {
            w!("{{ {:?}[{:?}] | {:?} }}", &self.bty, &self.idx, &self.pred)
        }
    }
}

impl Pretty for Ty {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(cx, f);
        match self.kind() {
            TyKind::Indexed(bty, idx) => {
                w!("{:?}", bty)?;
                if cx.hide_refinements {
                    return Ok(());
                }
                if idx.is_unit() {
                    if bty.is_adt() {
                        w!("[]")?;
                    }
                } else {
                    w!("[{:?}]", idx)?;
                }
                Ok(())
            }
            TyKind::Exists(ty_ctor) => {
                let vars = ty_ctor.vars();
                cx.with_bound_vars(vars, || {
                    if cx.hide_refinements {
                        w!("{:?}", ty_ctor.skip_binder_ref())
                    } else {
                        cx.fmt_bound_vars(false, "∃", vars, ". ", f)?;
                        w!("{:?}", ty_ctor.skip_binder_ref())
                    }
                })
            }
            TyKind::Uninit => w!("uninit"),
            TyKind::StrgRef(re, loc, ty) => w!("&{:?} strg <{:?}: {:?}>", re, loc, ty),
            TyKind::Ptr(pk, loc) => w!("ptr({:?}, {:?})", pk, loc),
            TyKind::Discr(adt_def, place) => w!("discr({:?}, {:?})", adt_def.did(), ^place),
            TyKind::Constr(pred, ty) => {
                if cx.hide_refinements {
                    w!("{:?}", ty)
                } else {
                    w!("{{ {:?} | {:?} }}", ty, pred)
                }
            }
            TyKind::Param(param_ty) => w!("{}", ^param_ty),
            TyKind::Downcast(adt, .., variant_idx, fields) => {
                w!("{:?}::{}", adt.did(), ^adt.variant(*variant_idx).name)?;
                if !fields.is_empty() {
                    w!("({:?})", join!(", ", fields))?;
                }
                Ok(())
            }
            TyKind::Blocked(ty) => w!("†{:?}", ty),
            TyKind::Alias(AliasKind::Projection, alias_ty) => {
                let assoc_name = cx.tcx.item_name(alias_ty.def_id);
                let trait_ref = cx.tcx.parent(alias_ty.def_id);
                let trait_generic_count = cx.tcx.generics_of(trait_ref).count() - 1;

                let [self_ty, args @ ..] = &alias_ty.args[..] else {
                    return w!("<alias_ty>");
                };

                w!("<{:?} as {:?}", self_ty, trait_ref)?;

                let trait_generics = &args[..trait_generic_count];
                if !trait_generics.is_empty() {
                    w!("<{:?}>", join!(", ", trait_generics))?;
                }
                w!(">::{}", ^assoc_name)?;

                let assoc_generics = &args[trait_generic_count..];
                if !assoc_generics.is_empty() {
                    w!("<{:?}>", join!(", ", assoc_generics))?;
                }
                Ok(())
            }
            TyKind::Alias(AliasKind::Opaque, alias_ty) => {
                w!(
                    "Alias(Opaque, {:?}, [{:?}], [{:?}])",
                    alias_ty.def_id,
                    join!(", ", &alias_ty.args),
                    join!(", ", &alias_ty.refine_args)
                )
            }
            TyKind::Infer(_) => {
                w!("□")
            }
        }
    }

    fn default_cx(tcx: TyCtxt) -> PrettyCx {
        PrettyCx::default(tcx).kvar_args(KVarArgs::Hide)
    }
}

impl Pretty for PtrKind {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(cx, f);
        match self {
            PtrKind::Mut(re) => {
                w!("mut")?;
                if !cx.hide_regions {
                    w!("[{:?}]", re)?;
                }
                Ok(())
            }
            PtrKind::Box => w!("box"),
        }
    }
}

impl Pretty for AliasKind {
    fn fmt(&self, _cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(_cx, f);
        match self {
            AliasKind::Projection => w!("Projection"),
            AliasKind::Opaque => w!("Opaque"),
        }
    }
}

impl Pretty for List<Ty> {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(cx, f);
        if let [ty] = &self[..] {
            w!("({:?},)", ty)
        } else {
            w!("({:?})", join!(", ", self))
        }
    }
}

impl Pretty for ExistentialPredicate {
    fn fmt(&self, _cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(_cx, f);
        match self {
            ExistentialPredicate::Trait(trait_ref) => w!("{:?}", trait_ref),
            ExistentialPredicate::Projection(proj) => w!("({:?})", proj),
            ExistentialPredicate::AutoTrait(def_id) => w!("{:?}", def_id),
        }
    }
}

impl Pretty for ExistentialTraitRef {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(cx, f);

        w!("{:?}", self.def_id)?;
        if !self.args.is_empty() {
            w!("<{:?}>", join!(", ", &self.args))?;
        }
        Ok(())
    }
}

impl Pretty for ExistentialProjection {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(cx, f);

        w!("{:?}", self.def_id)?;
        if !self.args.is_empty() {
            w!("<{:?}>", join!(", ", &self.args))?;
        }
        w!(" = {:?}", &self.term)
    }
}

impl Pretty for BaseTy {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(cx, f);
        match self {
            BaseTy::Int(int_ty) => w!("{}", ^int_ty.name_str()),
            BaseTy::Uint(uint_ty) => w!("{}", ^uint_ty.name_str()),
            BaseTy::Bool => w!("bool"),
            BaseTy::Str => w!("str"),
            BaseTy::Char => w!("char"),
            BaseTy::Adt(adt_def, args) => {
                w!("{:?}", adt_def.did())?;
                let args = args
                    .iter()
                    .filter(|arg| !cx.hide_regions || !matches!(arg, GenericArg::Lifetime(_)))
                    .collect_vec();
                if !args.is_empty() {
                    w!("<{:?}>", join!(", ", args))?;
                }
                Ok(())
            }
            BaseTy::FnDef(def_id, args) => {
                w!("FnDef({:?}[{:?}])", def_id, join!(", ", args))
            }
            BaseTy::Param(param) => w!("{}", ^param),
            BaseTy::Float(float_ty) => w!("{}", ^float_ty.name_str()),
            BaseTy::Slice(ty) => w!("[{:?}]", ty),
            BaseTy::RawPtr(ty, Mutability::Mut) => w!("*mut {:?}", ty),
            BaseTy::RawPtr(ty, Mutability::Not) => w!("*const {:?}", ty),
            BaseTy::Ref(re, ty, mutbl) => {
                w!("&")?;
                if !cx.hide_regions {
                    w!("{:?} ", re)?;
                }
                w!("{}{:?}",  ^mutbl.prefix_str(), ty)
            }
            BaseTy::FnPtr(poly_fn_sig) => {
                w!("{:?}", poly_fn_sig)
            }
            BaseTy::Tuple(tys) => {
                if let [ty] = &tys[..] {
                    w!("({:?},)", ty)
                } else {
                    w!("({:?})", join!(", ", tys))
                }
            }
            BaseTy::Array(ty, c) => w!("[{:?}; {:?}]", ty, ^c),
            BaseTy::Never => w!("!"),
            BaseTy::Closure(did, args, _) => {
                w!("Closure {:?}<{:?}>", did, args)
            }
            BaseTy::Coroutine(did, resume_ty, upvars) => {
                w!("Coroutine({:?}, {:?})", did, resume_ty)?;
                if !upvars.is_empty() {
                    w!("<{:?}>", join!(", ", upvars))?;
                }
                Ok(())
            }
            BaseTy::Dynamic(preds, re) => {
                w!("dyn {:?} + {:?}", join!(" + ", preds), re)
            }
        }
    }
}

impl Pretty for ValTree {
    fn fmt(&self, _cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(_cx, f);
        match self {
            ValTree::Leaf(v) => w!("Leaf({v:?})"),
            ValTree::Branch(children) => {
                w!("Branch([{:?}])", join!(", ", children))
            }
        }
    }
}
impl Pretty for UnevaluatedConst {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(cx, f);
        w!("UnevaluatedConst({:?}[...])", self.def)
    }
}

impl Pretty for Const {
    fn fmt(&self, _cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(_cx, f);
        match &self.kind {
            ConstKind::Param(p) => w!("{}", ^p.name.as_str()),
            ConstKind::Value(_, v) => w!("{v:?}"),
            ConstKind::Infer(infer_const) => w!("{:?}", ^infer_const),
            ConstKind::Unevaluated(uneval_const) => w!("{:?}", uneval_const),
        }
    }
}

impl Pretty for GenericArg {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(cx, f);
        match self {
            GenericArg::Ty(ty) => w!("{:?}", ty),
            GenericArg::Base(ctor) => {
                cx.with_bound_vars(ctor.vars(), || {
                    cx.fmt_bound_vars(false, "λ", ctor.vars(), ". ", f)?;
                    w!("{:?}", ctor.skip_binder_ref())
                })
            }
            GenericArg::Lifetime(re) => w!("{:?}", re),
            GenericArg::Const(c) => w!("{:?}", c),
        }
    }
}

impl Pretty for VariantSig {
    fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(cx, f);
        w!("({:?}) => {:?}", join!(", ", self.fields()), &self.idx)
    }
}

impl Pretty for Region {
    fn fmt(&self, _cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(cx, f);
        w!("{}", ^region_to_string(*self))
    }
}

impl Pretty for DebruijnIndex {
    fn fmt(&self, _cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(cx, f);
        w!("^{}", ^self.as_usize())
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
);
