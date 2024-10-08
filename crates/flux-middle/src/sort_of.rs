use flux_arc_interner::List;
use flux_common::{bug, tracked_span_bug};
use rustc_hir::def::DefKind;
use rustc_span::def_id::DefId;

use crate::{global_env::GlobalEnv, queries::QueryResult, query_bug, rty};

impl<'sess, 'tcx> GlobalEnv<'sess, 'tcx> {
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

impl rty::BaseTy {
    pub fn sort(&self) -> rty::Sort {
        match self {
            rty::BaseTy::Int(_) | rty::BaseTy::Uint(_) | rty::BaseTy::Slice(_) => rty::Sort::Int,
            rty::BaseTy::Bool => rty::Sort::Bool,
            rty::BaseTy::Adt(adt_def, args) => adt_def.sort(args),
            rty::BaseTy::Param(param_ty) => rty::Sort::Param(*param_ty),
            rty::BaseTy::Str => rty::Sort::Str,
            rty::BaseTy::Alias(kind, alias_ty) => rty::Sort::Alias(*kind, alias_ty.clone()),
            rty::BaseTy::Float(_)
            | rty::BaseTy::Char
            | rty::BaseTy::RawPtr(..)
            | rty::BaseTy::Ref(..)
            | rty::BaseTy::FnPtr(..)
            | rty::BaseTy::FnDef(..)
            | rty::BaseTy::Tuple(_)
            | rty::BaseTy::Array(_, _)
            | rty::BaseTy::Closure(..)
            | rty::BaseTy::Coroutine(..)
            | rty::BaseTy::Dynamic(_, _)
            | rty::BaseTy::Never => rty::Sort::unit(),
            rty::BaseTy::Infer(_) => tracked_span_bug!(),
        }
    }
}

impl rty::AliasReft {
    pub fn fsort(&self, genv: GlobalEnv) -> QueryResult<Option<rty::FuncSort>> {
        let Some(fsort) = genv.sort_of_assoc_reft(self.trait_id, self.name)? else {
            return Ok(None);
        };
        Ok(Some(fsort.instantiate(genv.tcx(), &self.args, &[])))
    }
}
