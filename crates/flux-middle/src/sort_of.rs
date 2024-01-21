use flux_common::bug;
use rustc_hir::{def::DefKind, PrimTy};
use rustc_span::def_id::{DefId, LocalDefId};

use crate::{fhir, global_env::GlobalEnv, intern::List, queries::QueryResult, rty};

impl<'sess, 'tcx> GlobalEnv<'sess, 'tcx> {
    pub fn sort_of_alias_pred(&self, alias_pred: &fhir::AliasPred) -> QueryResult<rty::FuncSort> {
        let trait_id = alias_pred.trait_id;
        let name = alias_pred.name;
        let fsort = self.sort_of_assoc_pred(trait_id, name);
        Ok(fsort.instantiate_func_sort(|param_ty| {
            self.sort_of_generic_arg(&alias_pred.generic_args[param_ty.index as usize])
                .unwrap()
        }))
    }

    pub fn sort_of_bty(&self, bty: &fhir::BaseTy) -> Option<rty::Sort> {
        match &bty.kind {
            fhir::BaseTyKind::Path(fhir::QPath::Resolved(_, path)) => self.sort_of_path(path),
            fhir::BaseTyKind::Slice(_) => Some(rty::Sort::Int),
        }
    }

    fn sort_of_path(&self, path: &fhir::Path) -> Option<rty::Sort> {
        match path.res {
            fhir::Res::PrimTy(PrimTy::Int(_) | PrimTy::Uint(_)) => Some(rty::Sort::Int),
            fhir::Res::PrimTy(PrimTy::Bool) => Some(rty::Sort::Bool),
            fhir::Res::PrimTy(PrimTy::Float(..) | PrimTy::Str | PrimTy::Char) => {
                Some(rty::Sort::unit())
            }
            fhir::Res::Def(DefKind::TyAlias { .. } | DefKind::Enum | DefKind::Struct, def_id) => {
                let mut sort_args = vec![];
                let sort_def = self.adt_sort_def_of(def_id);
                for arg in sort_def.filter_generic_args(&path.args) {
                    sort_args.push(self.sort_of_ty(arg.expect_type())?);
                }
                Some(rty::Sort::Adt(self.adt_sort_def_of(def_id), List::from_vec(sort_args)))
            }
            fhir::Res::SelfTyAlias { alias_to, .. } => self.sort_of_self_ty_alias(alias_to),
            fhir::Res::Def(DefKind::TyParam, def_id) => {
                self.sort_of_generic_param(def_id.expect_local())
            }
            fhir::Res::SelfTyParam { trait_ } => self.sort_of_self_param(trait_),
            fhir::Res::Def(DefKind::AssocTy | DefKind::OpaqueTy, _) => None,
            fhir::Res::Def(..) => bug!("unexpected res `{:?}`", path.res),
        }
    }

    pub fn sort_of_self_ty_alias(&self, alias_to: DefId) -> Option<rty::Sort> {
        let self_ty = self.tcx.type_of(alias_to).instantiate_identity();
        self.sort_of_self_ty(alias_to, self_ty)
    }

    fn sort_of_generic_param(&self, def_id: LocalDefId) -> Option<rty::Sort> {
        let param = self.get_generic_param(def_id);
        match &param.kind {
            fhir::GenericParamKind::BaseTy | fhir::GenericParamKind::SplTy => {
                Some(rty::Sort::Param(self.def_id_to_param_ty(def_id)))
            }
            fhir::GenericParamKind::Type { .. } | fhir::GenericParamKind::Lifetime => None,
        }
    }

    fn sort_of_self_param(&self, owner: DefId) -> Option<rty::Sort> {
        let generics = self.map().get_generics(self.tcx, owner.expect_local())?;
        let kind = generics.self_kind.as_ref()?;
        match kind {
            fhir::GenericParamKind::BaseTy | fhir::GenericParamKind::SplTy => {
                Some(rty::Sort::Param(rty::SELF_PARAM_TY))
            }
            fhir::GenericParamKind::Type { .. } | fhir::GenericParamKind::Lifetime => None,
        }
    }

    fn sort_of_generic_arg(&self, arg: &fhir::GenericArg) -> Option<rty::Sort> {
        match arg {
            fhir::GenericArg::Lifetime(_) => None,
            fhir::GenericArg::Type(ty) => self.sort_of_ty(ty),
        }
    }

    pub fn sort_of_ty(&self, ty: &fhir::Ty) -> Option<rty::Sort> {
        match &ty.kind {
            fhir::TyKind::BaseTy(bty) | fhir::TyKind::Indexed(bty, _) => self.sort_of_bty(bty),
            fhir::TyKind::Exists(_, ty) | fhir::TyKind::Constr(_, ty) => self.sort_of_ty(ty),
            fhir::TyKind::RawPtr(_, _)
            | fhir::TyKind::Ref(_, _)
            | fhir::TyKind::Tuple(_)
            | fhir::TyKind::Array(_, _)
            | fhir::TyKind::Never => Some(rty::Sort::unit()),
            fhir::TyKind::Hole(_)
            | fhir::TyKind::Ptr(_, _)
            | fhir::TyKind::OpaqueDef(_, _, _, _) => None,
        }
    }

    fn sort_of_self_ty(&self, def_id: DefId, ty: rustc_middle::ty::Ty) -> Option<rty::Sort> {
        use rustc_middle::ty;
        match ty.kind() {
            ty::TyKind::Bool => Some(rty::Sort::Bool),
            ty::TyKind::Slice(_) | ty::TyKind::Int(_) | ty::TyKind::Uint(_) => Some(rty::Sort::Int),
            ty::TyKind::Adt(adt_def, args) => {
                let mut sort_args = vec![];
                let sort_def = self.adt_sort_def_of(adt_def.did());
                for arg in sort_def.filter_generic_args(args) {
                    sort_args.push(self.sort_of_self_ty(def_id, arg.expect_ty())?);
                }
                Some(rty::Sort::Adt(self.adt_sort_def_of(adt_def.did()), List::from_vec(sort_args)))
            }
            ty::TyKind::Param(p) => {
                let generic_param_def = self
                    .tcx
                    .generics_of(def_id)
                    .param_at(p.index as usize, self.tcx);
                self.sort_of_generic_param(generic_param_def.def_id.expect_local())
            }
            ty::TyKind::Float(_)
            | ty::TyKind::Str
            | ty::TyKind::Char
            | ty::TyKind::RawPtr(_)
            | ty::TyKind::Ref(..)
            | ty::TyKind::Tuple(_)
            | ty::TyKind::Array(..)
            | ty::TyKind::Never => Some(rty::Sort::unit()),
            _ => bug!("unexpected self ty {ty:?}"),
        }
    }
}
