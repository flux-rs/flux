///! The context used before refinement checking while building the [`fhir::Map`] and for
///! well-formedness checking.
use std::borrow::Borrow;

use flux_errors::{ErrorGuaranteed, FluxSession};
use rustc_errors::IntoDiagnostic;
use rustc_hir::{def_id::LocalDefId, PrimTy};
use rustc_middle::ty::TyCtxt;
use rustc_span::{def_id::DefId, Symbol};

use crate::{cstore::CrateStoreDyn, fhir};

pub struct EarlyCtxt<'a, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub sess: &'a FluxSession,
    pub cstore: Box<CrateStoreDyn>,
    pub map: fhir::Map,
}

impl<'a, 'tcx> EarlyCtxt<'a, 'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        sess: &'a FluxSession,
        cstore: Box<CrateStoreDyn>,
        map: fhir::Map,
    ) -> Self {
        Self { tcx, sess, cstore, map }
    }

    pub fn sort_decl(&self, name: impl Borrow<Symbol>) -> Option<&fhir::SortDecl> {
        self.map.sort_decl(name)
    }

    pub fn func_decl(&self, name: impl Borrow<Symbol>) -> Option<&fhir::FuncDecl> {
        self.map.func_decl(name)
    }

    pub fn const_by_name(&self, name: impl Borrow<Symbol>) -> Option<&fhir::ConstInfo> {
        self.map.const_by_name(name)
    }

    pub fn index_sorts_of(&self, def_id: DefId) -> &[fhir::Sort] {
        if let Some(local_id) = def_id
            .as_local()
            .or_else(|| self.map.externs().get(&def_id).copied())
        {
            self.map.refined_by(local_id).index_sorts()
        } else {
            self.cstore
                .refined_by(def_id)
                .map(fhir::RefinedBy::index_sorts)
                .unwrap_or_default()
        }
    }

    pub fn early_bound_sorts_of(&self, def_id: DefId) -> &[fhir::Sort] {
        if let Some(local_id) = def_id.as_local() {
            self.map.refined_by(local_id).early_bound_sorts()
        } else {
            self.cstore
                .refined_by(def_id)
                .map(fhir::RefinedBy::early_bound_sorts)
                .unwrap_or_default()
        }
    }

    pub fn field_index(&self, def_id: DefId, fld: Symbol) -> Option<usize> {
        if let Some(local_id) = def_id.as_local() {
            self.map.refined_by(local_id).field_index(fld)
        } else {
            self.cstore
                .refined_by(def_id)
                .and_then(|refined_by| refined_by.field_index(fld))
        }
    }

    pub fn field_sort(&self, def_id: DefId, fld: Symbol) -> Option<&fhir::Sort> {
        if let Some(local_id) = def_id.as_local() {
            self.map.refined_by(local_id).field_sort(fld)
        } else {
            self.cstore
                .refined_by(def_id)
                .and_then(|refined_by| refined_by.field_sort(fld))
        }
    }

    #[track_caller]
    pub fn emit_err<'b>(&'b self, err: impl IntoDiagnostic<'b>) -> ErrorGuaranteed {
        self.sess.emit_err(err)
    }

    pub fn hir(&self) -> rustc_middle::hir::map::Map<'tcx> {
        self.tcx.hir()
    }

    pub fn sort_of_res(&self, res: fhir::Res) -> Option<fhir::Sort> {
        let sort = match res {
            fhir::Res::PrimTy(PrimTy::Int(_) | PrimTy::Uint(_)) => fhir::Sort::Int,
            fhir::Res::PrimTy(PrimTy::Bool) => fhir::Sort::Bool,
            fhir::Res::PrimTy(PrimTy::Float(..) | PrimTy::Str | PrimTy::Char) => fhir::Sort::Unit,
            fhir::Res::Param(def_id) => {
                let param = self.get_generic_param(def_id.expect_local());
                match &param.kind {
                    fhir::GenericParamDefKind::BaseTy => fhir::Sort::Param(def_id),
                    fhir::GenericParamDefKind::Type { .. }
                    | fhir::GenericParamDefKind::Lifetime => return None,
                }
            }
            fhir::Res::Alias(def_id) | fhir::Res::Enum(def_id) | fhir::Res::Struct(def_id) => {
                fhir::Sort::Record(def_id)
            }
        };
        Some(sort)
    }

    /// Whether values of this sort can be compared for equality.
    pub fn has_equality(&self, sort: &fhir::Sort) -> bool {
        match sort {
            fhir::Sort::Int
            | fhir::Sort::Bool
            | fhir::Sort::Real
            | fhir::Sort::Unit
            | fhir::Sort::User(_)
            | fhir::Sort::BitVec(_) => true,
            fhir::Sort::Record(def_id) => {
                self.index_sorts_of(*def_id)
                    .iter()
                    .all(|sort| self.has_equality(sort))
            }
            fhir::Sort::Loc
            | fhir::Sort::Func(_)
            | fhir::Sort::Param(_)
            | fhir::Sort::Wildcard
            | fhir::Sort::Infer(_) => false,
        }
    }

    pub fn sort_of_bty(&self, bty: &fhir::BaseTy) -> Option<fhir::Sort> {
        match &bty.kind {
            fhir::BaseTyKind::Path(fhir::Path { res, .. }) => self.sort_of_res(*res),
            fhir::BaseTyKind::Slice(_) => Some(fhir::Sort::Int),
        }
    }

    pub fn get_generic_param(&self, def_id: LocalDefId) -> &fhir::GenericParamDef {
        let owner = self.hir().ty_param_owner(def_id);
        self.map.get_generics(owner).unwrap().get_param(def_id)
    }

    pub fn is_box(&self, res: fhir::Res) -> bool {
        if let fhir::Res::Struct(def_id) = res {
            self.tcx.adt_def(def_id).is_box()
        } else {
            false
        }
    }
}
