///! The context used before refinement checking while building the [`fhir::Map`] and for
///! well-formedness checking.
use std::borrow::Borrow;

use flux_errors::{ErrorGuaranteed, FluxSession};
use rustc_errors::IntoDiagnostic;
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

    pub fn uif(&self, name: impl Borrow<Symbol>) -> Option<&fhir::UifDef> {
        self.map.uif(name)
    }

    pub fn const_by_name(&self, name: impl Borrow<Symbol>) -> Option<&fhir::ConstInfo> {
        self.map.const_by_name(name)
    }

    pub fn sorts_of(&self, def_id: DefId) -> &[fhir::Sort] {
        if let Some(local_id) = def_id.as_local() {
            self.map.get_adt(local_id).sorts()
        } else {
            self.cstore.sorts_of(def_id).unwrap_or_default()
        }
    }

    pub fn early_bound_sorts_of(&self, def_id: DefId) -> &[fhir::Sort] {
        if let Some(local_id) = def_id.as_local() {
            self.map.get_adt(local_id).early_bound_sorts()
        } else {
            todo!()
        }
    }

    pub fn field_index(&self, def_id: DefId, fld: Symbol) -> Option<usize> {
        if let Some(local_id) = def_id.as_local() {
            self.map.get_adt(local_id).field_index(fld)
        } else {
            self.cstore.field_index(def_id, fld)
        }
    }

    pub fn field_sort(&self, def_id: DefId, fld: Symbol) -> Option<&fhir::Sort> {
        if let Some(local_id) = def_id.as_local() {
            self.map.get_adt(local_id).field_sort(fld)
        } else {
            self.cstore.field_sort(def_id, fld)
        }
    }

    #[track_caller]
    pub fn emit_err<'b>(&'b self, err: impl IntoDiagnostic<'b>) -> ErrorGuaranteed {
        self.sess.emit_err(err)
    }

    pub fn is_coercible_to_func(&self, sort: &fhir::Sort) -> Option<fhir::FuncSort> {
        if let fhir::Sort::Func(fsort) = sort {
            Some(fsort.clone())
        } else if let Some(fhir::Sort::Func(fsort)) = self.is_single_field_adt(sort) {
            Some(fsort.clone())
        } else {
            None
        }
    }

    pub fn is_single_field_adt<'b>(&'b self, sort: &fhir::Sort) -> Option<&'b fhir::Sort> {
        if let fhir::Sort::Adt(def_id) = sort && let [sort] = self.sorts_of(*def_id) {
            Some(sort)
        } else {
            None
        }
    }

    pub fn hir(&self) -> rustc_middle::hir::map::Map<'tcx> {
        self.tcx.hir()
    }
}
