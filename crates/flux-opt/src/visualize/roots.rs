use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

pub fn get_roots(tcx: &TyCtxt, def_ids: &[DefId], filename: &str) -> Vec<DefId> {
    let mut result = vec![];

    for def_id in def_ids {
        let span = tcx.def_span(*def_id);
        let file_name = tcx.sess.source_map().span_to_filename(span);

        let s = file_name.prefer_local().to_string();

        if s.ends_with(filename) {
            result.push(*def_id);
        }
    }

    result
}
