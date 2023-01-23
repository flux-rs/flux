///! Context used before refinement checking while building [`fhir::Map`] and during
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

    #[track_caller]
    pub fn emit_err<'b>(&'b self, err: impl IntoDiagnostic<'b>) -> ErrorGuaranteed {
        self.sess.emit_err(err)
    }

    pub fn sorts_of(&self, def_id: DefId) -> &[fhir::Sort] {
        if let Some(local_id) = def_id.as_local() {
            self.map.sorts_of(local_id)
        } else {
            &[]
        }
    }

    pub fn uif(&self, name: impl Borrow<Symbol>) -> Option<&fhir::UifDef> {
        self.map.uif(name)
    }

    pub fn const_by_name(&self, name: impl Borrow<Symbol>) -> Option<&fhir::ConstInfo> {
        self.map.const_by_name(name)
    }

    pub fn field_index(&self, adt_def_id: DefId, fld: Symbol) -> Option<usize> {
        if let Some(local_id) = adt_def_id.as_local() {
            self.map.adt(local_id).field_index(fld)
        } else {
            todo!()
        }
    }

    pub fn field_sort(&self, adt_def_id: DefId, fld: Symbol) -> Option<&fhir::Sort> {
        if let Some(local_id) = adt_def_id.as_local() {
            self.map.adt(local_id).field_sort(fld)
        } else {
            todo!()
        }
    }
}
