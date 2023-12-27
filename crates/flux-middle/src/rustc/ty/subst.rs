use super::{Binder, Const, ConstKind, FnSig, GenericArg, Region, Ty, TyKind};
use crate::intern::{Internable, List};

pub(super) trait Subst {
    fn subst(&self, args: &[GenericArg]) -> Self;
}

impl<T> Subst for Binder<T>
where
    T: Subst,
{
    fn subst(&self, args: &[GenericArg]) -> Self {
        Binder(self.0.subst(args), self.1.clone())
    }
}

impl Subst for FnSig {
    fn subst(&self, args: &[GenericArg]) -> Self {
        FnSig { inputs_and_output: self.inputs_and_output.subst(args) }
    }
}

impl Subst for Ty {
    fn subst(&self, args: &[GenericArg]) -> Ty {
        match self.kind() {
            TyKind::Adt(adt_def, args2) => Ty::mk_adt(adt_def.clone(), args2.subst(args)),
            TyKind::Array(ty, len) => Ty::mk_array(ty.subst(args), len.clone()),
            TyKind::Ref(re, ty, mutbl) => Ty::mk_ref(*re, ty.subst(args), *mutbl),
            TyKind::Tuple(tys) => Ty::mk_tuple(tys.subst(args)),
            TyKind::Slice(ty) => Ty::mk_slice(ty.subst(args)),
            TyKind::Closure(def_id, args2) => Ty::mk_closure(*def_id, args2.subst(args)),
            TyKind::Coroutine(def_id, args2) => Ty::mk_coroutine(*def_id, args2.subst(args)),
            TyKind::CoroutineWitness(def_id, args2) => {
                Ty::mk_generator_witness(*def_id, args2.subst(args))
            }
            TyKind::Alias(kind, alias_ty) => {
                let def_id = alias_ty.def_id;
                Ty::mk_alias(*kind, def_id, alias_ty.args.subst(args))
            }
            TyKind::RawPtr(ty, mutbl) => Ty::mk_raw_ptr(ty.subst(args), *mutbl),
            TyKind::Param(param_ty) => args[param_ty.index as usize].expect_type().clone(),
            TyKind::FnPtr(fn_sig) => Ty::mk_fn_ptr(fn_sig.subst(args)),
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
    fn subst(&self, args: &[GenericArg]) -> Self {
        match self {
            GenericArg::Ty(ty) => GenericArg::Ty(ty.subst(args)),
            GenericArg::Lifetime(re) => GenericArg::Lifetime(re.subst(args)),
            GenericArg::Const(c) => GenericArg::Const(c.subst(args)),
        }
    }
}

impl Subst for Const {
    fn subst(&self, args: &[GenericArg]) -> Self {
        match &self.kind {
            ConstKind::Param(param_const) => {
                args[param_const.index as usize].expect_const().clone()
            }
            ConstKind::Value(_) => self.clone(),
        }
    }
}

impl Subst for Region {
    fn subst(&self, args: &[GenericArg]) -> Self {
        match self {
            Region::ReEarlyBound(ebr) => args[ebr.index as usize].expect_lifetime(),
            Region::ReFree(..)
            | Region::ReLateBound(_, _)
            | Region::ReStatic
            | Region::ReVar(_) => *self,
        }
    }
}

impl<T> Subst for List<T>
where
    T: Subst,
    [T]: Internable,
{
    fn subst(&self, args: &[GenericArg]) -> Self {
        self.iter().map(|t| t.subst(args)).collect()
    }
}
