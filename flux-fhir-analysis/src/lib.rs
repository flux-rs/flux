#![feature(rustc_private, let_chains, box_patterns)]

extern crate rustc_errors;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_span;

use flux_macros::fluent_messages;
use flux_middle::early_ctxt::EarlyCtxt;
use rustc_errors::{DiagnosticMessage, ErrorGuaranteed, SubdiagnosticMessage};
use wf::Wf;

fluent_messages! { "../locales/en-US.ftl" }

mod annot_check;
mod wf;

pub fn check_crate(early_cx: &EarlyCtxt) -> Result<(), ErrorGuaranteed> {
    let mut err: Option<ErrorGuaranteed> = None;

    for defn in early_cx.map.defns() {
        err = Wf::check_defn(early_cx, defn).err().or(err);
    }

    for qualifier in early_cx.map.qualifiers() {
        err = Wf::check_qualifier(early_cx, qualifier).err().or(err);
    }

    for alias in early_cx.map.type_aliases() {
        err = Wf::check_alias(early_cx, alias)
            .and_then(|_| annot_check::check_alias(early_cx, alias))
            .err()
            .or(err);
    }

    for struct_def in early_cx.map.structs() {
        err = Wf::check_struct_def(early_cx, struct_def)
            .and_then(|_| annot_check::check_struct_def(early_cx, struct_def))
            .err()
            .or(err);
    }

    for enum_def in early_cx.map.enums() {
        err = Wf::check_enum_def(early_cx, enum_def)
            .and_then(|_| annot_check::check_enum_def(early_cx, enum_def))
            .err()
            .or(err);
    }

    for (def_id, fn_sig) in early_cx.map.fn_sigs() {
        err = Wf::check_fn_sig(early_cx, fn_sig)
            .and_then(|_| annot_check::check_fn_sig(early_cx, def_id, fn_sig))
            .err()
            .or(err);
    }

    let qualifiers = early_cx.map.qualifiers().map(|q| q.name.clone()).collect();
    for (_, fn_quals) in early_cx.map.fn_quals() {
        err = Wf::check_fn_quals(early_cx.sess, &qualifiers, fn_quals)
            .err()
            .or(err);
    }

    if let Some(err) = err {
        Err(err)
    } else {
        Ok(())
    }
}
