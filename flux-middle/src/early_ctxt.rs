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
    pub cstore: &'a CrateStoreDyn,
    pub map: &'a mut fhir::Map,
}

impl<'a, 'tcx> EarlyCtxt<'a, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, sess: &'a FluxSession, map: &'a mut fhir::Map) -> Self {
        todo!()
    }

    pub fn sort_decl(&self, name: impl Borrow<Symbol>) -> Option<fhir::SortDecl> {
        todo!()
    }

    #[track_caller]
    pub fn emit_err<'b>(&'b self, err: impl IntoDiagnostic<'b>) -> ErrorGuaranteed {
        self.sess.emit_err(err)
    }

    pub fn sorts_of(&self, def_id: DefId) -> &'a [fhir::Sort] {
        todo!()
    }

    pub fn uif(&self, name: impl Borrow<Symbol>) -> Option<&fhir::UifDef> {
        todo!()
    }

    pub fn const_by_name(&self, name: impl Borrow<Symbol>) -> Option<&fhir::ConstInfo> {
        todo!()
    }
}
