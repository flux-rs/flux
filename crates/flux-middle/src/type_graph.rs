//! Type dependency graph: maps each local struct/enum to the other local
//! struct/enums referenced in its field definitions.

use std::{fs, io, path::Path};

use flux_common::dbg::SpanTrace;
use rustc_data_structures::unord::UnordMap;
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::{self, TyCtxt};
use serde::Serialize;
use toposort_scc::IndexGraph;

#[derive(Serialize)]
struct JsonNode {
    uid: usize,
    path: String,
    span: SpanTrace,
    deps: Vec<usize>,
}

/// Collect DefIds of all ADTs (struct/enum) referenced in `ty`, recursively.
fn collect_adt_refs<'tcx>(ty: ty::Ty<'tcx>, out: &mut Vec<DefId>) {
    match ty.kind() {
        ty::TyKind::Adt(adt_def, args) => {
            out.push(adt_def.did());
            for arg in args.iter() {
                if let ty::GenericArgKind::Type(inner_ty) = arg.kind() {
                    collect_adt_refs(inner_ty, out);
                }
            }
        }
        ty::TyKind::Array(inner, _) | ty::TyKind::Slice(inner) => {
            collect_adt_refs(*inner, out);
        }
        ty::TyKind::Ref(_, inner, _) | ty::TyKind::RawPtr(inner, _) => {
            collect_adt_refs(*inner, out);
        }
        ty::TyKind::Tuple(tys) => {
            for inner in tys.iter() {
                collect_adt_refs(inner, out);
            }
        }
        _ => {}
    }
}

pub fn dump_type_graph(tcx: TyCtxt<'_>, dir: &Path) -> io::Result<()> {
    // Collect all local struct/enum DefIds
    let local_adts: Vec<DefId> = tcx
        .iter_local_def_id()
        .filter(|&local_id| {
            matches!(
                tcx.def_kind(local_id),
                DefKind::Struct | DefKind::Enum
            )
        })
        .map(|local_id| local_id.to_def_id())
        .collect();

    let adt_to_idx: UnordMap<DefId, usize> = local_adts
        .iter()
        .enumerate()
        .map(|(i, &did)| (did, i))
        .collect();

    // Build adjacency: type -> types it references in its fields
    let adj: Vec<Vec<usize>> = local_adts
        .iter()
        .map(|&def_id| {
            let adt_def = tcx.adt_def(def_id);
            let mut refs = Vec::new();
            for variant in adt_def.variants() {
                for field in &variant.fields {
                    let field_ty = tcx.type_of(field.did).skip_binder();
                    collect_adt_refs(field_ty, &mut refs);
                }
            }
            let mut local_refs: Vec<usize> = refs
                .into_iter()
                .filter_map(|did| adt_to_idx.get(&did).copied())
                .collect();
            local_refs.sort_unstable();
            local_refs.dedup();
            // Remove self-references
            let self_idx = adt_to_idx.get(&def_id).copied().unwrap();
            local_refs.retain(|&idx| idx != self_idx);
            local_refs
        })
        .collect();

    // Toposort: transpose so deps come first
    let mut graph = IndexGraph::from_adjacency_list(&adj);
    graph.transpose();
    let topo_order = graph.toposort_or_scc().unwrap_or_else(|sccs| {
        sccs.into_iter().flatten().collect()
    });

    let mut uid_of: Vec<usize> = vec![0; local_adts.len()];
    for (uid, &orig_idx) in topo_order.iter().enumerate() {
        uid_of[orig_idx] = uid;
    }

    let json_nodes: Vec<JsonNode> = topo_order
        .iter()
        .enumerate()
        .map(|(uid, &orig_idx)| {
            let def_id = local_adts[orig_idx];
            let dep_uids: Vec<usize> = adj[orig_idx].iter().map(|&j| uid_of[j]).collect();
            JsonNode {
                uid,
                path: tcx.def_path_str(def_id),
                span: SpanTrace::new(tcx, tcx.def_span(def_id)),
                deps: dep_uids,
            }
        })
        .collect();

    fs::create_dir_all(dir)?;
    let path = dir.join("type_graph.json");
    let file = fs::File::create(path)?;
    serde_json::to_writer_pretty(file, &json_nodes)
        .map_err(|e| io::Error::new(io::ErrorKind::Other, e))
}
