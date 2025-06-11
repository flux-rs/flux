use flux_arc_interner::List;
use flux_common::tracked_span_bug;
use rustc_hir::def::DefKind;
use rustc_span::def_id::DefId;

use crate::{
    global_env::GlobalEnv,
    queries::{QueryErr, QueryResult},
    query_bug,
    rty::{
        self,
        fold::{FallibleTypeFolder, TypeFoldable, TypeSuperFoldable as _},
    },
};

impl GlobalEnv<'_, '_> {
    pub fn sort_of_self_ty_alias(self, alias_to: DefId) -> QueryResult<Option<rty::Sort>> {
        let self_ty = self.tcx().type_of(alias_to).instantiate_identity();
        self.sort_of_rust_ty(alias_to, self_ty)
    }

    pub fn sort_of_generic_param(self, def_id: DefId) -> QueryResult<Option<rty::Sort>> {
        let parent = self.tcx().parent(def_id);
        let index = self.def_id_to_param_index(def_id);
        let param = self.generics_of(parent)?.param_at(index as usize, self)?;
        let sort = match &param.kind {
            rty::GenericParamDefKind::Base { .. } => {
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

    pub fn sort_of_def_id(self, def_id: DefId) -> QueryResult<Option<rty::Sort>> {
        let ty = self.tcx().type_of(def_id).no_bound_vars().unwrap();
        if ty.is_integral() { Ok(Some(rty::Sort::Int)) } else { self.sort_of_rust_ty(def_id, ty) }
    }

    pub fn sort_of_rust_ty(
        self,
        def_id: DefId,
        ty: rustc_middle::ty::Ty,
    ) -> QueryResult<Option<rty::Sort>> {
        use rustc_middle::ty;
        let sort = match ty.kind() {
            ty::TyKind::Bool => Some(rty::Sort::Bool),
            ty::TyKind::Slice(_) | ty::TyKind::Int(_) | ty::TyKind::Uint(_) => Some(rty::Sort::Int),
            ty::TyKind::Char => Some(rty::Sort::Char),
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
            | ty::TyKind::RawPtr(..)
            | ty::TyKind::Ref(..)
            | ty::TyKind::Tuple(_)
            | ty::TyKind::Array(..)
            | ty::TyKind::Alias(..)
            | ty::TyKind::Never => Some(rty::Sort::unit()),
            _ => None,
        };
        Ok(sort)
    }

    pub fn normalize_free_alias_sort(self, alias_ty: &rty::AliasTy) -> QueryResult<rty::Sort> {
        match self.def_kind(alias_ty.def_id) {
            DefKind::Impl { .. } => Ok(self.sort_of_self_ty_alias(alias_ty.def_id)?.unwrap()),
            DefKind::TyAlias => {
                Ok(self
                    .type_of(alias_ty.def_id)?
                    .instantiate(self.tcx(), &alias_ty.args, &alias_ty.refine_args)
                    .expect_ctor()
                    .sort())
            }
            DefKind::Struct | DefKind::Enum => {
                Ok(self
                    .adt_sort_def_of(alias_ty.def_id)?
                    .to_sort(&alias_ty.args))
            }
            _ => Err(query_bug!(alias_ty.def_id, "unexpected weak alias `{:?}`", alias_ty.def_id)),
        }
    }

    pub fn deep_normalize_weak_alias_sorts<T: TypeFoldable>(self, t: &T) -> QueryResult<T> {
        struct WeakAliasSortNormalizer<'genv, 'tcx> {
            genv: GlobalEnv<'genv, 'tcx>,
        }

        impl FallibleTypeFolder for WeakAliasSortNormalizer<'_, '_> {
            type Error = QueryErr;

            fn try_fold_sort(&mut self, sort: &rty::Sort) -> QueryResult<rty::Sort> {
                // TODO(BUMP) if let rty::Sort::Alias(rty::AliasKind::Weak, alias_ty) = sort {
                // TODO(BUMP)    self.genv
                // TODO(BUMP)       .normalize_weak_alias_sort(alias_ty)?
                // TODO(BUMP)       .try_fold_with(self)
                // TODO(BUMP) } else {
                sort.try_super_fold_with(self)
                // TODO(BUMP)  }
            }
        }
        t.try_fold_with(&mut WeakAliasSortNormalizer { genv: self })
    }
}

impl rty::BaseTy {
    pub fn sort(&self) -> rty::Sort {
        match self {
            rty::BaseTy::Int(_) | rty::BaseTy::Uint(_) | rty::BaseTy::Slice(_) => rty::Sort::Int,
            rty::BaseTy::Bool => rty::Sort::Bool,
            rty::BaseTy::Char => rty::Sort::Char,
            rty::BaseTy::Adt(adt_def, args) => adt_def.sort(args),
            rty::BaseTy::Param(param_ty) => rty::Sort::Param(*param_ty),
            rty::BaseTy::Str => rty::Sort::Str,
            rty::BaseTy::Alias(kind, alias_ty) => {
                // HACK(nilehmann) The refinement arguments in `alias_ty` should not influence the
                // sort. However, we must explicitly remove them because they can contain expression
                // holes. If we don't remove them, we would generate inference variables for them
                // which we won't be able to solve.
                let alias_ty =
                    rty::AliasTy::new(alias_ty.def_id, alias_ty.args.clone(), List::empty());
                rty::Sort::Alias(*kind, alias_ty)
            }
            rty::BaseTy::Float(_)
            | rty::BaseTy::RawPtr(..)
            | rty::BaseTy::RawPtrMetadata(..) // TODO(RJ): This should be `int` for slice?
            | rty::BaseTy::Ref(..)
            | rty::BaseTy::FnPtr(..)
            | rty::BaseTy::FnDef(..)
            | rty::BaseTy::Tuple(_)
            | rty::BaseTy::Array(_, _)
            | rty::BaseTy::Closure(..)
            | rty::BaseTy::Coroutine(..)
            | rty::BaseTy::Dynamic(_, _)
            | rty::BaseTy::Never
            | rty::BaseTy::Foreign(..) => rty::Sort::unit(),
            rty::BaseTy::Infer(_) => tracked_span_bug!(),
        }
    }
}

impl rty::AliasReft {
    pub fn fsort(&self, genv: GlobalEnv) -> QueryResult<rty::FuncSort> {
        Ok(genv
            .sort_of_assoc_reft(self.assoc_id)?
            .instantiate(genv.tcx(), &self.args, &[]))
    }
}
