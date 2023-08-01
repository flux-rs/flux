use super::{Binder, FnSig, GenericArg, Region, Ty, TyKind};
use crate::intern::{Internable, List};

pub(super) trait Subst {
    fn subst(&self, substs: &[GenericArg]) -> Self;
}

impl<T> Subst for Binder<T>
where
    T: Subst,
{
    fn subst(&self, substs: &[GenericArg]) -> Self {
        Binder(self.0.subst(substs), self.1.clone())
    }
}

impl Subst for FnSig {
    fn subst(&self, substs: &[GenericArg]) -> Self {
        FnSig { inputs_and_output: self.inputs_and_output.subst(substs) }
    }
}

impl Subst for Ty {
    fn subst(&self, substs: &[GenericArg]) -> Ty {
        match self.kind() {
            TyKind::Adt(adt_def, substs) => Ty::mk_adt(adt_def.clone(), substs.subst(substs)),
            TyKind::Array(ty, len) => Ty::mk_array(ty.subst(substs), len.clone()),
            TyKind::Ref(re, ty, mutbl) => Ty::mk_ref(*re, ty.subst(substs), *mutbl),
            TyKind::Tuple(tys) => Ty::mk_tuple(tys.subst(substs)),
            TyKind::Slice(ty) => Ty::mk_slice(ty.subst(substs)),
            TyKind::Closure(def_id, closure_substs) => {
                Ty::mk_closure(*def_id, closure_substs.subst(substs))
            }
            TyKind::Alias(kind, alias_ty) => {
                let def_id = alias_ty.def_id;
                let alias_substs = &alias_ty.substs;
                Ty::mk_alias(*kind, def_id, alias_substs.subst(substs))
            }
            TyKind::RawPtr(ty, mutbl) => Ty::mk_raw_ptr(ty.subst(substs), *mutbl),
            TyKind::Param(param_ty) => substs[param_ty.index as usize].expect_type().clone(),
            TyKind::FnPtr(fn_sig) => Ty::mk_fn_ptr(fn_sig.subst(substs)),
            TyKind::Bool
            | TyKind::Uint(_)
            | TyKind::Str
            | TyKind::Char
            | TyKind::Float(_)
            | TyKind::Int(_)
            | TyKind::Never => self.clone(),
        }
    }
}

impl Subst for GenericArg {
    fn subst(&self, substs: &[GenericArg]) -> Self {
        match self {
            GenericArg::Ty(ty) => GenericArg::Ty(ty.subst(substs)),
            GenericArg::Lifetime(re) => GenericArg::Lifetime(re.subst(substs)),
        }
    }
}

impl Subst for Region {
    fn subst(&self, substs: &[GenericArg]) -> Self {
        match self {
            Region::ReEarlyBound(ebr) => substs[ebr.index as usize].expect_lifetime(),
            Region::ReLateBound(_, _) | Region::ReStatic | Region::ReVar(_) | Region::ReErased => {
                *self
            }
        }
    }
}

impl<T> Subst for List<T>
where
    T: Subst,
    [T]: Internable,
{
    fn subst(&self, substs: &[GenericArg]) -> Self {
        self.iter().map(|t| t.subst(substs)).collect()
    }
}
