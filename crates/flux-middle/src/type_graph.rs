//! Type dependency graph: maps each local struct/enum to the other local
//! struct/enums referenced in its field definitions.

use std::{io, path::Path};

use rustc_data_structures::unord::UnordMap;
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::{self, TyCtxt};

use crate::call_graph::dump_dep_graph_json;

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
    let local_adts: Vec<DefId> = tcx
        .iter_local_def_id()
        .filter(|&local_id| matches!(tcx.def_kind(local_id), DefKind::Struct | DefKind::Enum))
        .map(|local_id| local_id.to_def_id())
        .collect();

    let adt_to_idx: UnordMap<DefId, usize> = local_adts
        .iter()
        .enumerate()
        .map(|(i, &did)| (did, i))
        .collect();

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
            let self_idx = adt_to_idx.get(&def_id).copied().unwrap();
            local_refs.retain(|&idx| idx != self_idx);
            local_refs
        })
        .collect();

    dump_dep_graph_json(tcx, dir, "type_graph.json", &local_adts, &adj)
}
