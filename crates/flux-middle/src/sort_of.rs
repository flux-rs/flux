use flux_arc_interner::List;
use flux_common::{bug, span_bug};
use rustc_hir::{def::DefKind, PrimTy};
use rustc_span::def_id::DefId;

use crate::{fhir, global_env::GlobalEnv, queries::QueryResult, query_bug, rty};

impl<'sess, 'tcx> GlobalEnv<'sess, 'tcx> {
    pub fn sort_of_alias_reft(self, alias: &fhir::AliasReft) -> QueryResult<Option<rty::FuncSort>> {
        let fhir::Res::Def(DefKind::Trait, trait_id) = alias.path.res else {
            bug!("expected trait")
        };
        let name = alias.name;
        let Some(fsort) = self.sort_of_assoc_reft(trait_id, name)? else { return Ok(None) };
        Some(fsort.instantiate_func_sort(|param_ty| {
            if param_ty.index == 0 {
                self.sort_of_ty(alias.qself)
            } else {
                let args = alias.path.last_segment().args;
                self.sort_of_generic_arg(&args[(param_ty.index - 1) as usize])
            }
            .transpose()
            .unwrap()
        }))
        .transpose()
    }

    pub fn sort_of_bty(self, bty: &fhir::BaseTy) -> QueryResult<Option<rty::Sort>> {
        let sort = match &bty.kind {
            fhir::BaseTyKind::Path(fhir::QPath::Resolved(_, path)) => self.sort_of_path(path)?,
            fhir::BaseTyKind::Path(fhir::QPath::TypeRelative(..)) => None,
            fhir::BaseTyKind::Slice(_) => Some(rty::Sort::Int),
        };
        Ok(sort)
    }

    fn sort_of_path(self, path: &fhir::Path) -> QueryResult<Option<rty::Sort>> {
        let sort = match path.res {
            fhir::Res::PrimTy(PrimTy::Int(_) | PrimTy::Uint(_)) => Some(rty::Sort::Int),
            fhir::Res::PrimTy(PrimTy::Bool) => Some(rty::Sort::Bool),
            fhir::Res::PrimTy(PrimTy::Str) => Some(rty::Sort::Str),
            fhir::Res::PrimTy(PrimTy::Float(..) | PrimTy::Char) => Some(rty::Sort::unit()),
            fhir::Res::Def(DefKind::TyAlias { .. } | DefKind::Enum | DefKind::Struct, def_id) => {
                let mut sort_args = vec![];
                let sort_def = self.adt_sort_def_of(def_id)?;
                let generic_args = path.segments.last().unwrap().args;
                for arg in sort_def.filter_generic_args(generic_args) {
                    let Some(sort) = self.sort_of_ty(arg.expect_type())? else { return Ok(None) };
                    sort_args.push(sort);
                }
                let ctor = rty::SortCtor::Adt(self.adt_sort_def_of(def_id)?);
                Some(rty::Sort::App(ctor, List::from_vec(sort_args)))
            }
            fhir::Res::SelfTyAlias { alias_to, .. } => self.sort_of_self_ty_alias(alias_to)?,
            fhir::Res::Def(DefKind::TyParam, def_id) => self.sort_of_generic_param(def_id)?,
            fhir::Res::SelfTyParam { trait_ } => self.sort_of_self_param(trait_)?,
            fhir::Res::Def(DefKind::AssocTy | DefKind::OpaqueTy, _) => None,
            fhir::Res::Def(..) | fhir::Res::Err => {
                span_bug!(path.span, "unexpected res `{:?}`", path.res)
            }
        };
        Ok(sort)
    }

    pub fn sort_of_self_ty_alias(self, alias_to: DefId) -> QueryResult<Option<rty::Sort>> {
        let self_ty = self.tcx().type_of(alias_to).instantiate_identity();
        self.sort_of_rust_ty(alias_to, self_ty)
    }

    pub fn sort_of_generic_param(self, def_id: DefId) -> QueryResult<Option<rty::Sort>> {
        let parent = self.tcx().parent(def_id);
        let index = self.def_id_to_param_index(def_id);
        let param = self.generics_of(parent)?.param_at(index as usize, self)?;
        let sort = match &param.kind {
            rty::GenericParamDefKind::Base => {
                Some(rty::Sort::Param(rty::ParamTy { index, name: param.name }))
            }
            rty::GenericParamDefKind::Const { .. } => {
                let ty = self.tcx().type_of(def_id).instantiate_identity();
                self.sort_of_rust_ty(parent, ty)?
            }
            rty::GenericParamDefKind::Type { .. } | rty::GenericParamDefKind::Lifetime => None,
        };
        Ok(sort)
    }

    fn sort_of_self_param(self, trait_id: DefId) -> QueryResult<Option<rty::Sort>> {
        assert!(matches!(self.def_kind(trait_id), DefKind::Trait));
        let generics = self.generics_of(trait_id)?;
        let sort = match &generics.param_at(0, self)?.kind {
            rty::GenericParamDefKind::Base => Some(rty::Sort::Param(rty::SELF_PARAM_TY)),
            rty::GenericParamDefKind::Const { .. }
            | rty::GenericParamDefKind::Type { .. }
            | rty::GenericParamDefKind::Lifetime => None,
        };
        Ok(sort)
    }

    fn sort_of_generic_arg(self, arg: &fhir::GenericArg) -> QueryResult<Option<rty::Sort>> {
        match arg {
            fhir::GenericArg::Type(ty) => self.sort_of_ty(ty),
            fhir::GenericArg::Lifetime(_) | fhir::GenericArg::Const(_) => Ok(None),
        }
    }

    fn sort_of_ty(self, ty: &fhir::Ty) -> QueryResult<Option<rty::Sort>> {
        match &ty.kind {
            fhir::TyKind::BaseTy(bty) | fhir::TyKind::Indexed(bty, _) => self.sort_of_bty(bty),
            fhir::TyKind::Exists(_, ty) | fhir::TyKind::Constr(_, ty) => self.sort_of_ty(ty),
            fhir::TyKind::RawPtr(..)
            | fhir::TyKind::Ref(..)
            | fhir::TyKind::Tuple(_)
            | fhir::TyKind::Array(..)
            | fhir::TyKind::TraitObject(..)
            | fhir::TyKind::BareFn(_)
            | fhir::TyKind::Never => Ok(Some(rty::Sort::unit())),
            fhir::TyKind::Infer | fhir::TyKind::StrgRef(..) | fhir::TyKind::OpaqueDef(..) => {
                Ok(None)
            }
        }
    }

    fn sort_of_rust_ty(
        self,
        def_id: DefId,
        ty: rustc_middle::ty::Ty,
    ) -> QueryResult<Option<rty::Sort>> {
        use rustc_middle::ty;
        let sort = match ty.kind() {
            ty::TyKind::Bool => Some(rty::Sort::Bool),
            ty::TyKind::Slice(_) | ty::TyKind::Int(_) | ty::TyKind::Uint(_) => Some(rty::Sort::Int),
            ty::TyKind::Str => Some(rty::Sort::Str),
            ty::TyKind::Adt(adt_def, args) => {
                let mut sort_args = vec![];
                let sort_def = self.adt_sort_def_of(adt_def.did())?;
                for arg in sort_def.filter_generic_args(args) {
                    let Some(sort) = self.sort_of_rust_ty(def_id, arg.expect_ty())? else {
                        return Ok(None);
                    };
                    sort_args.push(sort);
                }
                let ctor = rty::SortCtor::Adt(self.adt_sort_def_of(adt_def.did())?);
                Some(rty::Sort::App(ctor, List::from_vec(sort_args)))
            }
            ty::TyKind::Param(p) => {
                let generic_param_def = self
                    .tcx()
                    .generics_of(def_id)
                    .param_at(p.index as usize, self.tcx());
                self.sort_of_generic_param(generic_param_def.def_id)?
            }
            ty::TyKind::Float(_)
            | ty::TyKind::Char
            | ty::TyKind::RawPtr(..)
            | ty::TyKind::Ref(..)
            | ty::TyKind::Tuple(_)
            | ty::TyKind::Array(..)
            | ty::TyKind::Alias(..)
            | ty::TyKind::Never => Some(rty::Sort::unit()),
            _ => bug!("unexpected self ty {ty:?}"),
        };
        Ok(sort)
    }

    pub fn normalize_weak_alias_sort(self, alias_ty: &rty::AliasTy) -> QueryResult<rty::Sort> {
        match self.def_kind(alias_ty.def_id) {
            DefKind::Impl { .. } => Ok(self.sort_of_self_ty_alias(alias_ty.def_id)?.unwrap()),
            DefKind::Struct | DefKind::Enum | DefKind::TyAlias => {
                Ok(self
                    .adt_sort_def_of(alias_ty.def_id)?
                    .to_sort(&alias_ty.args))
            }
            _ => Err(query_bug!(alias_ty.def_id, "unexpected weak alias `{:?}`", alias_ty.def_id)),
        }
    }
}
